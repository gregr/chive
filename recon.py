# Copyright 2010 Gregory L. Rosenblatt

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

def tyErr(msg): raise RuntimeError(msg)
class Cons:
    def __init__(self, name, vars): self.name = name; self.vars = vars
class TyExpr:
    def freeVars(self): return set()
    def subst(self, subs): return self, ()
    def occurs(self, name): return False
    def strengthen(self, cenv, mentions, parity, final): return self
    def __repr__(self): return '%s(%s)'%(self.__class__.__name__, str(self))
    def __str__(self): return ''
class TyExtreme(TyExpr):
    def __init__(self, name, relat): self.name = name; self.relat = relat
    def __str__(self): return self.name
    def constrain(self, subs, cenv, rhs, relat):
        if relat != self.relat and self is not rhs:
            tyErr('invalid type constraint: %s %s %s'%
                  (self.name, ('<:', '<:>',':>')[relat+1], rhs))
    def merge(self, subs, cenv, rhs, parity, grow):
        if self.relat*parity > 0: return self
        return rhs
    def contains(self, cenv, ty, parity):
        return self.relat*parity > 0 or self is ty
tyTop = TyExtreme('Top', 1); tyBot = TyExtreme('Bot', -1)
def mapFrees(args): return set().union(*(arg.freeVars() for arg in args))
def mapSubs(subs, args0, ret, mk):
    args = [subst(subs, arg) for arg in args0]
    if all(a1 == a2 for a1, a2 in zip(args, args0)): return ret, ()
    return mk(args), ()
def mapOccurs(name, args): return any(arg.occurs(name) for arg in self.args)
class TyCons(TyExpr):
    def __init__(self, cons, args): self.cons = cons; self.args = args
    def __str__(self):
        if self.args:
            if (not self.cons.name.isalnum()) and len(self.args) == 2:
                return '(%s %s %s)'%(self.args[0],self.cons.name,self.args[1])
            return '(%s)'%(self.cons.name+' '+' '.join(map(str, self.args)))
        return self.cons.name
    def freeVars(self): return mapFrees(self.args)
    def subst(self, subs):
        return mapSubs(subs, self.args, self,
                       lambda args1: TyCons(self.cons, args1))
    def occurs(self, name): return mapOccurs(name, self.args)
    def strengthen(self, cenv, mentions, parity, final):
        args = [arg.strengthen(cenv, mentions, parity*var, final)
                for arg, var in zip(self.args, self.cons.vars)]
        return TyCons(self.cons, args)
    def constrain(self, subs, cenv, rhs, relat):
        if not isinstance(rhs, TyCons) or self.cons is not rhs.cons:
            tyErr('invalid constraint') # todo
        for lhs, rhs, variance in zip(self.args, rhs.args, self.cons.vars):
            constrain(subs, cenv, lhs, rhs, relat*variance)
    def merge(self, subs, cenv, ty, parity, grow):
        if isinstance(ty, TyCons) and ty.cons is self.cons:
            args = [merge(subs, cenv, lhs, rhs, parity*var, grow)
                    for lhs, rhs, var in
                    zip(self.args, ty.args, self.cons.vars)]
            return TyCons(self.cons, args)
        elif parity == 0: tyErr("cannot equate '%s' and '%s'"%(self, ty))
        elif parity > 0:
            if isinstance(ty, TyCons): return TyVariant([self, ty])
            return tyTop
        else: return tyBot
    def contains(self, cenv, ty, parity):
        if isinstance(ty, TyCons) and ty.cons is self.cons:
            return all(contains(cenv, lhs, rhs, parity*var)
                       for lhs, rhs, var in
                       zip(self.args, ty.args, self.cons.vars))
        else: return ty is tyBot
class TyVariant(TyExpr):
    def __init__(self, conss): self.conss = conss; assert len(conss) > 1
    def __str__(self):
        return '{%s}'%' '.join(str(cons) for cons in self.conss)
    def freeVars(self): return mapFrees(self.conss)
    def subst(self, subs): return mapSubs(subs, self.conss, self, TyVariant)
    def occurs(self, name): return mapOccurs(name, self.conss)
    def strengthen(self, cenv, mentions, parity, final):
        return TyVariant([cns.strengthen(cenv, mentions, parity, final)
                          for cns in self.conss])
    def constrain(self, subs, cenv, rhs, relat):
        if isinstance(rhs, TyCons):
            if relat > 0:
                for cons in self.conss:
                    if cons.cons is rhs.cons:
                        return constrain(subs, cenv, cons, rhs, relat)
            tyErr('variant... constructor') # todo
        elif isinstance(rhs, TyVariant):
            if relat == 0:
                lhs = sorted((id(cons.cons), cons) for cons in self.conss)
                rhs = sorted((id(cons.cons), cons) for cons in rhs.conss)
                if len(lhs) != len(rhs): tyErr('unmatched variant sizes')
                for lc, rc in zip(lhs, rhs):
                    lc.constrain(subs, cenv, lc, relat)
            else:
                if relat < 0: lhs = rhs; rhs = self
                else: lhs = self
                for cons in rhs.conss: lhs.constrain(subs, cenv, cons, relat)
        else: tyErr('invalid variant constraint') # todo
    def merge(self, subs, cenv, ty, parity, grow):
        if isinstance(ty, TyCons):
            for idx, cons in enumerate(self.conss):
                if cons.cons is ty.cons:
                    merged = cons.merge(subs, cenv, ty, parity, grow)
                    if parity < 0 or not isinstance(merged, TyCons):
                        return merged
                    else:
                        if merged is cons: return self
                        return TyVariant(self.conss[:idx]+[merged]+
                                         self.conss[idx+1:])
            if parity > 0: return TyVariant(self.conss+[ty])
        elif isinstance(ty, TyVariant):
            match = dict((cons.cons, cons) for cons in ty.conss); acc = []
            for cons in self.conss:
                other = match.get(cons.cons)
                if other is None: parity > 0 and acc.append(cons)
                else:
                    acc.append(cons.merge(subs, cenv, other, parity, grow))
                    del match[cons.cons]
            if parity > 0: acc.extend(list(match.values()))
            if len(acc) > 1: return TyVariant(acc)
            elif len(acc) == 1: return acc[0]
            else: return tyBot
        if parity > 0: return tyTop
        else: return tyBot
    def contains(self, cenv, ty, parity):
        if isinstance(ty, TyVariant):
            return all(contains(cenv, self, cons, parity) for cons in ty.conss)
        elif isinstance(ty, TyCons):
            for cons in self.conss:
                if cons.cons is ty.cons:
                    return all(contains(cenv, lhs, rhs, parity*var)
                               for lhs, rhs, var in
                               zip(cons.args, ty.args, cons.cons.vars))
        else: return ty is tyBot
class TyUQfied(TyExpr):
    def __init__(self, bqs, body): self.bqs = bqs; self.body = body
    def __str__(self):
        return '(all [%s] => %s)'%(', '.join('%s<:%s'%(qn, bnd)
                                   for qn, bnd in self.bqs), self.body)
    def _boundVars(self): return tuple(zip(self.bqs))[0]
    def freeVars(self): return self.body.freeVars() - set(self._boundVars())
    def subst(self, subs):
        qns = self._boundVars()
        body = subst([sub for sub in subs if sub[0] not in qns], self.body)
        if body is self.body: return self, ()
        return TyUQfied(self.bqs, body), ()
    def occurs(self, name):
        return (name not in self._boundVars()) and self.body.occurs(name)
    def _instantiate(self, cenv, relat):
        subs = []
        for qn, bnd in self.bqs:
            newName, _ = fresh(cenv, qn)
            if relat >= 0: bnd = TyQVar(newName.name, bnd)
            newName.constrain([], cenv, bnd, -1)
            subs.append((qn, newName))
        print('subs:', subs)
        return subst(subs, self.body)
    def constrain(self, subs, cenv, rhs, relat):
        constrain(subs, cenv, self._instantiate(cenv, relat), rhs, relat)
    def merge(self, subs, cenv, ty, parity, grow):
        return merge(subs, cenv, self._instantiate(cenv, parity), ty, parity,
                     grow)
    def contains(self, cenv, ty, parity):
        return contains(cenv, self._instantiate(cenv, parity), ty, parity)
class TyQVar(TyExpr):
    def __init__(self, name, bnd): self.name = name; self.bnd = bnd
    def __str__(self): return '(%s<:%s)'%(self.name, self.bnd)
    def constrain(self, subs, cenv, rhs, relat):
        if rhs is self: return
        if parity < 0: constrain(subs, cenv, self.bnd, rhs, relat)
        tyErr('invalid quantified var constraint: %s <: %s'%(rhs, self))
    def merge(self, subs, cenv, ty, parity, grow):
        if ty is self: return self
        if parity > 0: return merge(subs, cenv, self.bnd, ty, parity, grow)
        elif parity < 0: return tyBot
        tyErr('cannot equate %s and %s'%(self, ty))
    def contains(self, cenv, ty, parity):
        if ty is self: return True
        if parity < 0: return contains(cenv, self.bnd, ty, parity)
        return False
class TyVar(TyExpr):
    def __init__(self, name): self.name = name
    def __str__(self): return self.name
    def identical(self, cenv, ty):
        return isinstance(ty, TyVar) and (ty.name == self.name or
                                          cenv[ty.name] is cenv[self.name])
    def freeVars(self): return {self.name}
    def subst(self, subs):
        for idx, (nm, ty) in enumerate(subs):
            if self.name == nm: return ty, subs[idx:]
        return self, ()
    def occurs(self, name): return self.name == name
    def strengthen(self, cenv, mentions, parity, final):
        if final and mentions[self.name] > 1: return self
        cx = cenv[self.name]
        if cx.invar: return cx.invar.strengthen(cenv, mentions, parity, final)
        if parity == 1:
            if final or cx.contravar.bnd is not tyBot:
                return cx.contravar.bnd.strengthen(cenv, mentions, parity,
                                                   final)
        elif (final or isinstance(cx.covar.bnd, TyCons) or
              cx.covar.bnd.freeVars()):
            return cx.covar.bnd.strengthen(cenv, mentions, parity, final)
        count = mentions.setdefault(cx.name, 0); mentions[cx.name] += 1
        return TyVar(cx.name)#.strengthen(cenv, mentions, parity, final)
    def constrain(self, subs, cenv, rhs, relat):
        print('uh oh:', self, '?', rhs)
        if self.identical(cenv, rhs): return
        if relat == 0: cenv[self.name].equate(subs, cenv, rhs, True)
        else:
            lc = cenv[self.name]
            if isinstance(rhs, TyVar):
                rc = cenv[rhs.name]
                if relat > 0: high, low = lc, rc
                else: high, low = rc, lc
                high.link(low)
            else: lc.merge(subs, cenv, rhs, relat, True)
    def merge(self, subs, cenv, ty, parity, grow):
        if self.identical(cenv, ty): return self
        varc = cenv[self.name]
        if parity == 0: varc.equate(subs, cenv, ty, grow); return ty
        else:
            if grow: bnd = varc.parity(parity).bnd
            else: bnd = varc.upperBound().bnd
            maybe = merge(subs, cenv, bnd, ty, parity, False)
            if not grow or (isinstance(maybe, TyExtreme) and
                            maybe.relat*parity > 0): return maybe
            var, csrnt = fresh(cenv)
            csrnt.merge(subs, cenv, ty, parity, grow)
            csrnt.mergeC(varc, parity)
            return var
    def contains(self, cenv, ty, parity): # todo: chokes on recursive types
        return contains(cenv, cenv[self.name].upperBound().bnd, ty, parity)

def makeVar(cenv, name, parity):
    csrnt = Constraint(name, parity); cenv[name] = csrnt
    return TyVar(name), csrnt
uid = 0
def fresh(cenv, nm=''):
    global uid
    name = '$UID_%s_%s'%(uid, nm); uid += 1; return makeVar(cenv, name, 1)
def subst(subs, ty):
    print('subst:', ty)
    while subs: ty, subs = ty.subst(subs); print('subst:', ty)
    return ty
def ordered(lhs, rhs, ordering):
    for tyty in ordering:
        if isinstance(lhs, tyty): return True
        if isinstance(rhs, tyty): return False
    return True
cxOrder = TyUQfied, TyVar, TyExtreme, TyVariant
def constrain(subs, cenv, lhs, rhs, relat):
    lhs = subst(subs, lhs); rhs = subst(subs, rhs)
    if not ordered(lhs, rhs, cxOrder): relat*=-1; lhs,rhs = rhs,lhs
    lhs.constrain(subs, cenv, rhs, relat)
def merge(subs, cenv, lhs, rhs, parity, grow):
    if not ordered(lhs, rhs, (TyExtreme, TyUQfied, TyVar, TyVariant)):
        lhs,rhs = rhs,lhs
    return lhs.merge(subs, cenv, rhs, parity, grow)
def contains(cenv, lhs, rhs, parity):
    if not ordered(lhs, rhs, cxOrder): parity*=-1; lhs,rhs = rhs,lhs
    return lhs.contains(cenv, rhs, parity)
def identical(cenv, lhs, rhs):
    return contains(cenv, lhs, rhs, -1) and contains(cenv, lhs, rhs, 1)

class Bound:
    def __init__(self, initBnd): self.bnd = initBnd; self.deps = set()
    def __str__(self): return '%s, %s'%(self.bnd, list(self.deps))
#    def __str__(self): return '%s'%self.bnd
    def mergeBound(self, subs, cenv, bnd, parity):
        self.deps |= bnd.deps;
        self.bnd = merge(subs, cenv, self.bnd, bnd.bnd, parity)
    def discardDeps(self, deps): self.deps -= deps
class Constraint:
    def __init__(self, name, parity):
        self.name = name; self.invar = None
        self.covar = Bound(tyTop); self.contravar = Bound(tyBot)
        self.bndParity = {1: self.contravar, -1: self.covar}
        self.finalParity = parity
    def __repr__(self):
        return 'CX(%s, %s <: %s)'%(self.name, self.contravar, self.covar)
    def equate(self, subs, cenv, ty, grow):
        self.invar = ty; subs.append((self.name, ty))
        if isinstance(ty, TyVar):
            csrnt = cenv[ty.name]; cenv[self.name] = csrnt
            csrnt.covar.mergeBound(subs, cenv, self.covar, -1, grow)
            csrnt.contravar.mergeBound(subs, cenv, self.contravar, 1, grow)
        else: self.meet(subs, cenv, ty, grow)#; self.join(subs, cenv, ty, grow)
    def link(self, low):
        self.contravar.deps.add(low.name); low.covar.deps.add(self.name)
    def mergeC(self, csrnt, relat):
        if relat > 0: lhs,rhs = self, csrnt
        elif relat < 0: lhs,rhs = csrnt, self
        lhs.link(rhs)
    def merge(self, subs, cenv, ty, relat, grow):
        if relat > 0: self.join(subs, cenv, ty, grow)
        elif relat < 0: self.meet(subs, cenv, ty, grow)
        else: self.equate(subs, cenv, ty, grow)
    def join(self, subs, cenv, ty, grow):
        self.contravar.bnd = merge(subs, cenv, self.contravar.bnd, ty, 1,grow)
    def meet(self, subs, cenv, ty, grow):
        self.covar.bnd = merge(subs, cenv, self.covar.bnd, ty, -1, grow)
    def parity(self, parity): return self.bndParity[parity]
    def upperBound(self): return self.parity(-1)
    def check(self, cenv):
        if not contains(cenv, self.covar.bnd, self.contravar.bnd, 1):
            tyErr("failed constraint '%s': %s <: %s"%
                  (self.name, self.contravar.bnd, self.covar.bnd))
        if self.invar and not contains(cenv, self.covar.bnd, self.invar, 1):
            tyErr("failed constraint invariant '%s': %s <: %s"%
                (self.name, self.invar, self.covar.bnd))

# todo: this all ends up incorrect thanks to constraint bounds with type vars
def dfs(cenv, cx, parity, finished, seen):
    if cx in seen: return
    seen.add(cx)
    for dep in cx.parity(parity).deps|cx.parity(parity).bnd.freeVars():
        dfs(cenv, cenv[dep], parity, finished, seen)
    finished.append(cx)
def depthReach(cenv, cs, parity, components, seen):
    while cs:
        cx = cs.pop()
        if cx in seen: continue
        print('cx:', cx.name)
        component = []; components.append(component) 
        dfs(cenv, cx, parity, component, seen)
def depSort(cenv):
    seen = set(); cs = set(cenv.values()); orders = []
    depthReach(cenv, cs, -1, orders, seen)
    print('orders:\n', '\n'.join(map(str, orders)))
    seen = set(); components = []
    for order in reversed(orders):
        depthReach(cenv, order, 1, components, seen)
    print('components:\n', '\n'.join(map(str, components)))
    return components

def mergeDeps(subs, cenv, cx, parity, ignore=set()):
    bnd = cx.parity(parity).bnd
    cx.parity(parity).discardDeps(ignore)
    for name in cx.parity(parity).deps:
        dep = cenv[name]
        bnd = merge(subs, cenv, bnd, dep.parity(parity).bnd, parity, False)
    cx.parity(parity).bnd = bnd
def mergeComp(subs, cenv, comp, parity):
    tgt = comp[0]; comp = set(comp); comp.remove(tgt)
    for cx in comp: mergeDeps(subs, cenv, cx, parity, comp)
    tgt.parity(parity).deps |= set(cy.name for cy in comp)
    mergeDeps(subs, cenv, tgt, parity)
def mergeComponents(subs, cenv, components, parity):
    for comp in components:
        if len(comp) == 1: mergeDeps(subs, cenv, comp[0], parity)
        else: mergeComp(subs, cenv, comp, parity)

def satisfy(subs, cenv):
    components = depSort(cenv)
    mergeComponents(subs, cenv, reversed(components), -1)
    mergeComponents(subs, cenv, components, 1)
    for comp in components:
        tgt = comp[0]
        if len(comp) > 1:
            for cx in comp[1:]: cenv[cx.name] = tgt
        tgt.check(cenv)
        deps = tgt.contravar.deps
        if len(deps) == 1: # coalesce matching single-dep contravar constraints
            dep = cenv[list(deps)[0]]
            if identical(cenv, dep.covar.bnd, tgt.covar.bnd):
                cenv[tgt.name] = dep

def quantify(cenv, ty):
    mentions = {}
    ty = ty.strengthen(cenv, mentions, 1, False)
    print('strengthen:', mentions, ty)
    ty = ty.strengthen(cenv, mentions, 1, True)
    print('final:', mentions, ty)
    bqs = [(name, cenv[name].upperBound().bnd)
           for name, count in mentions.items() if count > 1]
    if bqs: ty = TyUQfied(bqs, ty)
    return ty

if __name__ == '__main__':
    cenv = {}; subs = []
    def mkv(name, parity=1): return makeVar(cenv, name, parity)[0]
    def stat():
        print('status:')
        for k, v in cenv.items(): print(k, '::', v)
    def go(): satisfy(subs, cenv)
    def test(): stat(); go(); stat()
    def mkarr(*tys):
        tys = list(tys); res = tys.pop()
        while tys: res = TyCons(arrow, (tys.pop(), res))
        return res
    def qfy(ty): return quantify(cenv, ty)
    arrow = Cons('->', (-1, 1)); intc = Cons('Int', ());
    pair = Cons('Pair', (1, 1))
    intTy = TyCons(intc, ())
    addTy = TyCons(arrow, (intTy, TyCons(arrow, (intTy, intTy))))
    pairTy = TyCons(pair, (intTy, tyTop))
    nilTy = TyCons(Cons('Nil', ()), ())
    listTy = TyVariant([pairTy, nilTy])
    pconsdef = mkarr(tyTop, tyTop, pairTy)
    def mkPairTy(a, b): return TyCons(pair, (a, b))
    def mkListTy(x): return TyVariant([nilTy, mkPairTy(x, tyTop)])
    polypconsdef = TyUQfied([('A', tyTop), ('B', tyTop)],
                            mkarr(TyVar('A'), TyVar('B'),
                                  mkPairTy(TyVar('A'), TyVar('B'))))
    selectTy = mkarr(pairTy, intTy)
    fTy = TyUQfied([('X', tyTop), ('Y', tyTop)],
                  mkarr(TyVar('X'), mkarr(TyVar('X'), TyVar('Y')), TyVar('Y')))
#     gv = mkv('g'); xv = mkv('x'); gvr = mkv('$g')
#     gdef = mkarr(xv, gvr)
#     constrain(subs, cenv, gv, gdef, 0)
# #    gbodyr = mkv('gbodyr'); gapp1r = mkv('gapp1r')
#     gapp2r = mkv('gapp2r')
# #    gbody = mkarr(gapp1r, gapp2r, gbodyr)
# #    gapp1 = mkarr(xv, selectTy, gapp1r)
#     gapp2 = mkarr(xv, selectTy, gapp2r)
# #    constrain(subs, cenv, fTy, gapp1, -1)
#     constrain(subs, cenv, fTy, gapp2, -1)
#     constrain(subs, cenv, gvr, gapp2r, 1)

#    constrain(subs, cenv, pconsdef, gbody, -1)
#    constrain(subs, cenv, gvr, gbodyr, 1)
    qdef = TyUQfied([('Q', listTy)], mkarr(TyVar('Q'), listTy, TyVar('Q')))
    rdef = TyUQfied([('R', tyTop)],
                    mkarr(mkPairTy(TyVar('R'), tyTop),
                          mkListTy(TyVar('R')), intTy))
    sdef = mkarr(nilTy, pairTy, listTy)

    fv = mkv('f'); xv = mkv('x', -1); hv = mkv('h', -1)
    fvr = mkv('$f'); fbodyr = mkv('fbodyr')
    fdef = mkarr(xv, hv, fvr)
    constrain(subs, cenv, fv, fdef, 0)
    fapp1r = mkv('fapp1r'); fapp2r = mkv('fapp2r')
    fbody = mkarr(fapp1r, fapp2r, fbodyr)
    fapp1 = mkarr(xv, hv, fapp1r)
    fapp2 = mkarr(xv, hv, fapp2r)
    constrain(subs, cenv, qdef, fapp1, -1)
    constrain(subs, cenv, rdef, fapp2, -1)
    constrain(subs, cenv, polypconsdef, fbody, -1)

#     fbody = mkarr(xv, fbodyr)
#     constrain(subs, cenv, hv, fbody, -1)
    constrain(subs, cenv, fvr, fbodyr, 1)

#     gv = mkv(cenv, 'g'); yv = mkv(cenv, 'y'); jv = mkv(cenv, 'j')
#     gvr = mkv(cenv, '$g'); gbodyr = mkv(cenv, 'gbodyr')
#     gdef = mkarr(yv, gvr)
#     constrain(subs, cenv, gv, gdef, 0)
#     gbody = mkarr(yv, gbodyr)
# #    constrain(subs, cenv, pconsdef, fbody, -1)
#     constrain(subs, cenv, gdef, fbody, -1)
#     constrain(subs, cenv, fvr, fbodyr, 1)
#     constrain(subs, cenv, fdef, gbody, -1)
#     constrain(subs, cenv, gvr, gbodyr, 1)
#     fbody = TyCons(arrow, (xv, TyCons(arrow, (yv, fvr))))
#     fdef = TyCons(arrow, (xv, TyCons(arrow, (yv, fvr))))
#     constrain(subs, cenv, fv, fdef, 0)
#     constrain(subs, cenv, addTy, fbody, -1)
# #    constrain(subs, cenv, fv, fbody, -1)
