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

class Repr:
    def __str__(self): return ''
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self)
################################################################
# types
class Type(Repr):
    def contains(self, ty, tenv=None): return self is ty

class BasicType(Type): pass

class ScalarType(BasicType): pass
#class PyType(ScalarType): pass

class AggregateType(BasicType): pass # future: alignment
class StructType(AggregateType): pass # heterogeneous els
class ArrayType(AggregateType): pass # homogeneous els

# combine removal/addition in an update operation:
# tables/records: ({?a}//{?b})|{?c} # can also use struct-like repacking?
# arrays: reslice arr [(old-range new-subarr) (old-range new-subarr) ...]
# structs (no resizing): repack struct [(0 ?v) (2 ?v) ...]

class BoxedType(Type): pass # regions: mutability
class RefType(BoxedType): pass # strict, non-polymorphic, no ptr-arithmetic
#class DynArrayType(RefType): pass
#class DynArrayRefType(RefType): pass # ptr-like refs w/arithmetic to DA data
#class WeakRefType(RefType): pass # stores boxed element in unmanaged memory
#class ResourceType(RefType): pass # finalizable

# more general record type to support row-typing?
class TableType(BoxedType): pass # scalar/hashable keys; homogeneous els

class TaggedType(BoxedType): pass # polymorphic, regions: strictness
class AnyType(TaggedType): pass
class SumType(TaggedType): pass
class ProdType(TaggedType): pass
class ProcType(TaggedType): pass # closure and effect information?

# type variables
# lattice types: top, bottom, unions, intersections
# row types
# refinement types

class Tag: pass

################################################################
# interpreter utilities
from functools import reduce
from itertools import chain
from collections import namedtuple

def alphaGen(alphabet=[chr(o) for o in range(ord('a'), ord('z')+1)]):
    count = 0
    while True:
        countStr = str(count)
        for s in alphabet: yield s+countStr
        count += 1
class UIDGen:
    def __init__(self): self.counter = 0; self.recycled = set()
    def get(self):
        if self.recycled: uid = self.recycled.pop()
        else: uid = self.counter; self.counter += 1
        return uid
    def put(self, uid):
        assert uid < self.counter, (uid, self.counter)
        self.recycled.add(uid); prev = self.counter-1
        while prev in self.recycled: self.recycled.remove(prev); prev -= 1
        self.counter = prev+1
def Label(uidg=UIDGen()): return uidg.get()
_Name = namedtuple('Name', 'str uid')
def Name(str, uidg=UIDGen()): return _Name(str, uidg.get())
_showUID = False
def strName(self):
    global _showUID
    if _showUID: return str((self.str, self.uid))
    return str(self.str)
_Name.__str__ = strName
def strTup(tup): return '(%s)'%' '.join(str(el) for el in tup)
def strDict(dct, joiner=' '):
    return '{%s}'%joiner.join('(%s => %s)'%(key, strSet(val))
                           for key, val in dct.items())
def strSet(st):
    if isinstance(st, set): return '#{%s}'%' '.join(str(el) for el in st)
    return str(st)
def unionReduce(xs): return reduce(set.union, xs, set())
class Mapping(Repr):
    def __init__(self, dat=None):
        if dat is None: dat = {}
        self.data = dat
    def __str__(self): return strDict(self.data)
    def _getDefault(self): return None
    def _combineVal(self, key, val): return val
    def single(self, val): return val
    def get(self, key):
        val = self.data.get(key)
        if val is None: return self._getDefault()
        return val
    def insert(self, kvs):
        dat = self.data.copy()
        dat.update((key, self._combineVal(key, val)) for key, val in kvs)
        return self.__class__(dat)
    def join(self, other): return self.insert(other.data.items())
    def only(self, keys):
        dat = dict((key, val) for key, val in self.data.items() if key in keys)
        return self.__class__(dat)
class Measure(Mapping):
    def _getDefault(self): return 0
    def _combineVal(self, key, val): return min(2, self.get(key)+val)
    def join(self, other, adjust):
        return self.insert(map(adjust, other.data.items()))
class Env(Mapping):
    def _getDefault(self): return set()
    def _combineVal(self, key, val): return self.get(key)|val
    def single(self, val): return {val}
    def contains(self, env):
        return all(self.get(key).issuperset(val)
                   for (key,val) in env.data.items())
################################################################
# frame strings
nres = tuple(1 << idx for idx in range(6))
nreE, nreB, nreK, nreBs, nreKs, nreKsBs = nres
# empty, push(bra), pop(ket), pushes, pops, pops and pushes
nreStrs = {nreE:'e', nreB:'<|', nreK:'|>', nreBs:'<|<|+', nreKs:'|>|>+',
           nreKsBs:'|>+<|+'}
def nreSetStr(nreSet): return ', '.join(nreStrs[nre] for nre in nresIn(nreSet))
from operator import or_
nreAll = reduce(or_, nres, 0)
nreAllKs = nreK|nreKs|nreKsBs
nreInverse = {nreE:nreE, nreB:nreK, nreBs:nreKs, nreK:nreB, nreKs:nreBs,
              nreKsBs:nreKsBs}
nreCatMaps = (
    (nreE, (nreE, nreB, nreBs, nreK, nreKs, nreKsBs)),
    (nreB, (nreB, nreBs, nreBs, nreE, nreK|nreKs, nreBs|nreKsBs)),
    (nreBs, (nreBs, nreBs, nreBs, nreB|nreBs, nreAll&~nreKsBs, nreBs|nreKsBs)),
    (nreK, (nreK, nreE|nreKsBs, nreB|nreBs|nreKsBs, nreKs, nreKs, nreKsBs)),
    (nreKs, (nreKs, nreAllKs, nreAll, nreKs, nreKs, nreKsBs)),
    (nreKsBs, (nreKsBs, nreKsBs, nreKsBs, nreAllKs, nreAllKs, nreAll))
    ); nreCatMaps = dict(nreCatMaps)
nreCat = dict((key, dict((1 << idx, val) for idx, val in enumerate(tab)))
              for key, tab in nreCatMaps.items())
def nresIn(nreSet):
    for nre in nres:
        if nreSet&nre: yield nre
def nreCatComp(lhs, rhs):
    acc = 0
    for nre0 in nresIn(lhs):
        for nre1 in nresIn(rhs): acc |= nreCat[nre0][nre1]
    return acc
def nreInverseComp(nreSet):
    acc = 0
    for nre in nresIn(nreSet): acc |= nreInverse[nre]
    return acc
nrePowCard = 2**len(nres)
# precompute all cat and inverse results
nreSetCatMap = tuple(tuple(nreCatComp(lhs, rhs) for rhs in range(nrePowCard))
                     for lhs in range(nrePowCard))
nreSetInverse = tuple(nreInverseComp(nreSet) for nreSet in range(nrePowCard))
def nreSetCat(lhs, rhs, eager=False):
    if lhs==nreK and rhs==nreB and eager: return nreE
    return nreSetCatMap[lhs][rhs]
class FrameString(Repr):
    def __init__(self, byLab=None):
        if byLab is None: byLab = {}
        self.byLab = byLab
    def __str__(self):
        repDict = {}
        for lab, byTm in self.byLab.items():
            for tm, nreSet in byTm.items():
                repDict[(lab, tm)] = nreSetStr(nreSet)
        return '\n'+strDict(repDict, '\n')
    def get(self, lab, tm):
        byTm = self.byLab.get(lab)
        if byTm is not None: return byTm.get(tm, nreE)
        return nreE
    def inverse(self):
        return FrameString(dict((lab, dict((tm, nreSetInverse[nreSet])
                                           for tm, nreSet in byTime.items()))
                                for lab, byTime in self.byLab.items()))
    def cat(self, fs, fcnts):
        byLab = {}
        for lab, byTmL in self.byLab.items():
            byTmR = fs.byLab.get(lab, {})
            newByTm = {}; byLab[lab] = newByTm
            for tm, lhs in byTmL.items():
                nreNew = nreSetCat(lhs, byTmR.get(tm, nreE),
                                   (fcnts.get((lab,tm))<2))
                if nreNew != nreE: newByTm[tm] = nreNew
        for lab, byTmR in fs.byLab.items():
            byTmL = self.byLab.get(lab)
            if byTmL is not None:
                byTm = byLab[lab]
                for tm, rhs in byTmR.items():
                    if tm not in byTmL: byTm[tm] = rhs
            else: byLab[lab] = dict((tm, rhs) for tm, rhs in byTmR.items())
        return FrameString(byLab)
    def join(self, fs):
        byLab = self.byLab.copy()
        for lab, byTm1 in fs.byLab.items():
            byTm0 = byLab.get(lab)
            if byTm0 is not None:
                byTm0 = byTm0.copy(); byLab[lab] = byTm0
                for tm, nreSet in byTm1.items():
                    byTm0[tm] = byTm0.get(tm, nreE)|nreSet
            else: byLab[lab] = byTm1
        return FrameString(byLab)
    def joinEmptyTime(self, tm):
        changed = False
        for lab, byTime in self.byLab.items():
            nreSet = byTime.get(tm)
            if nreSet is not None:
                if not changed: byLab = self.byLab.copy(); changed = True
                byTime = byTime.copy(); byLab[lab] = byTime
                byTime[tm] = nreSet|nreE
        if not changed: return self
        return FrameString(byLab)
    def only(self, tms):
        changed = False
        for lab, byTime in self.byLab.items():
            for tm in byTime:
                if tm not in tms:
                    if not changed: byLab = self.byLab.copy(); changed = True
                    byTime = dict((tm, nreSet) for tm, nreSet in byTime.items()
                                  if tm in tms)
                    byLab[lab] = byTime; break
        if not changed: return self
        return FrameString(byLab)
def pushFrame(lab, time): return FrameString({lab: {time: nreB}})
class FrameLog(Repr):
    def __init__(self, byTime=None):
        if byTime is None: byTime = {}
        self.byTime = byTime
    def __str__(self): return strDict(self.byTime)
    def get(self, tm):
        fs = self.byTime.get(tm)
        if fs is None: return FrameString()
        return fs
    def join(self, flog):
        byTime = self.byTime.copy()
        for tm, fs1 in flog.byTime.items():
            fs0 = byTime.get(tm)
            if fs0 is not None: byTime[tm] = fs0.join(fs1)
            else: byTime[tm] = fs1
        return FrameLog(byTime)
    def update(self, fs, fcnts, newTm=None):
        byTime = dict((tm, fstr.cat(fs, fcnts))
                      for tm, fstr in self.byTime.items())
        if newTm is not None:
            fs = byTime.get(newTm)
            if fs is None: byTime[newTm] = FrameString()
            else: fs.joinEmptyTime(newTm)
        return FrameLog(byTime)
    def only(self, tms):
        return FrameLog(dict((tm, fs.only(tms))
                             for tm, fs in self.byTime.items()))
################################################################
# interpreter
class ConcreteTime:
    def __init__(self, count): self.count = count
    def advance(self, code): return ConcreteTime(self.count+1)
    def __eq__(self, tm): return self.count == tm.count
    def __hash__(self): return hash(self.count)
class AbstractTime:
    def __init__(self, codes, mx): self.codes = codes; self.mx = mx
    def __eq__(self, tm): return self.codes == tm.codes
    def __hash__(self): return hash(self.codes)
    def __str__(self): return strTup(self.codes)
    def __repr__(self): return '<m=%d %s>'%(self.mx, self)
    def advance(self, code):
        codes = (self.codes+(code,)); codes = codes[max(0,len(codes)-self.mx):]
        return AbstractTime(codes, self.mx)

def namedTup(*args): ntup = namedtuple(*args); ntup.__str__=strTup; return ntup
Closure = namedTup('Closure', 'proc time')
Binding = namedTup('Binding', 'name time')
Context = namedTup('Context', 'code time')
def advance(ctx): return ctx.time.advance(ctx.code)
def touchedClosure(clo):
    return set(Binding(name, clo.time) for name in clo.proc.frees()), clo.time
def zip2(xs):
    ys = tuple(zip(*xs))
    if not ys: ys = ((), ())
    return ys
def touchedBinding(cfg, bnd):
    bts = zip2(touchedClosure(clo) for clo in cfg.store.get(bnd))
    return unionReduce(bts[0]), set(bts[1])
def reachable(cfg, bnds):
    seenBnds = set(bnds); seenTms = set()
    while bnds:
        bts = zip2(touchedBinding(cfg, bnd) for bnd in bnds)
        bnds = unionReduce(bts[0]) - seenBnds
        seenBnds |= bnds; seenTms |= unionReduce(bts[1])
    return seenBnds, seenTms
thickDiv = '='*64; thinDiv = '-'*64
def printDivd(msg): print(thickDiv+'\n= '+msg+'\n'+thickDiv)
class AbstractConfig(Repr):
    def __init__(self, store): self.store = store
    def __str__(self): return '%s'%str(self.store)
    def contains(self, cfg): return self.store.contains(cfg.store)
    def join(self, cfg, *args):
        return self.__class__(self.store.join(cfg.store), *args)
    def only(self, bnds, tms, *args):
        return self.__class__(self.store.only(bnds), *args)
    def update(self, tm, clo, bvs, fvs, *args):
        return self.join(self.__class__(Env(dict(chain(bvs, fvs))), *args))
    def print(self):
        printDivd('store summary'); print(strDict(self.store.data, '\n'))
class CountConfig(AbstractConfig):
    def __init__(self, store, count):
        super().__init__(store); self.count = count
    def __str__(self): return '(%s %s)'%(super().__str__(), str(self.count))
    def join(self, cfg, *args):
        count = self.count.join(cfg.count, adjEqBinding(self.store, cfg.store))
        return super().join(cfg, count)
    def only(self, bnds, tms, *args):
        return super().only(bnds, tms, self.count.only(bnds))
    def update(self, tm, clo, bvs, fvs, *args):
        count = Mapping(dict((bnd, 1) for bnd, _ in chain(bvs, fvs)))
        return super().update(tm, clo, bvs, fvs, count)
    def print(self):
        super().print(); printDivd('count summary')
        print(strDict(testSum.count.data, '\n'))
def adjEqBinding(env0, env1):
    def adjust(kv):
        bnd, cnt = kv
        if cnt == 1 and env0.get(bnd) == env1.get(bnd): cnt = 0
        return bnd, cnt
    return adjust
class FrameConfig(AbstractConfig):
    def __init__(self, store, flog, fcount):
        super().__init__(store); self.flog = flog; self.fcount = fcount
    def __str__(self): return '(%s %s %s)'%(super().__str__(), str(self.flog),
                                            str(self.fcount))
    def join(self, cfg, *args):
        fcount = self.fcount.join(cfg.fcount, adjEqFrame(self.flog, cfg.flog))
        return super().join(cfg, self.flog.join(cfg.flog), fcount)
    def update(self, tm, clo, bvs, fvs, *args):
        fchange = youngest(self.flog, clo, (val for _, val in bvs)).inverse()
        flog = self.flog.update(fchange, self.fcount)
        countKey = (clo.proc.lab, clo.time)
        curCount = self.fcount.get(countKey)
        fcount = self.fcount.insert(((countKey, min(2, curCount+1)),))
        flog = flog.update(pushFrame(*countKey), fcount, tm)
        return super().update(tm, clo, bvs, fvs, flog, fcount)
    def only(self, bnds, tms, *args):
        flog = self.flog.only(tms)
        labTms = unionReduce(set((lab, tm) for lab, byTm in
                                 flog.get(tm).byLab.items()
                                 if tm in byTm) for tm in tms)
        return super().only(bnds, tms, flog, self.fcount.only(labTms))
    def print(self):
        super().print(); printDivd('frame summary')
        print(strDict(testSum.flog.byTime, '\n'+thinDiv+'\n'))
def youngest(flog, clo, params):
    vals = unionReduce(params); vals.add(clo)
    return reduce(FrameString.join, (flog.get(val.time) for val in vals
                                     if isCont(val)), FrameString())
def adjEqFrame(fl0, fl1):
    def adjust(kv):
        key, cnt = kv; lab, tm = key
        if cnt==1 and fl0.get(tm).get(lab,tm)==fl1.get(tm).get(lab,tm): cnt = 0
        return key, cnt
    return adjust
#def newConfig(): return CountConfig(Env(), Measure())
def newConfig(): return FrameConfig(Env(), FrameLog(), Measure())
class State:
    def __init__(self, ctx, cfg): self.ctx = ctx; self.cfg = cfg
    def next(self): return self.ctx.code.eval(self.ctx.time, self.cfg)
    def reachable(self):
        return reachable(self.cfg, self.ctx.code.touched(self.ctx.time))
    def garbageCollect(self):
        return State(self.ctx, self.cfg.only(*self.reachable()))

class Expr(Repr):
    def __init__(self, lab=None):
        if lab is None: lab = Label()
        self.lab = lab
    def __eq__(self, expr): return self.lab == expr.lab
    def __hash__(self): return hash(self.lab)
    def __str__(self): raise NotImplementedError
    def frees(self): raise NotImplementedError
def accFrees(xs): return unionReduce(x.frees() for x in xs)

class CExpr(Expr):
    def touched(self, tm): return set(Binding(nm, tm) for nm in self.frees())
    def eval(self, tm, cfg): raise NotImplementedError
class Halt(CExpr):
    def __init__(self, resultName='halt-result', *args):
        super().__init__(*args); self.result = Name(resultName)
    def __str__(self): return '*HALT!*'
    def frees(self): return set((self.result,))
    def eval(self, tm, cfg): return ()
def makeHalt(): hlt = Halt(); return CProc((hlt.result,), hlt)
class Call(CExpr):
    def __init__(self, proc, params, *args):
        super().__init__(*args); self.proc = proc; self.params = params
    def __str__(self):
        return '(call %s %s)'%(str(self.proc), strTup(self.params))
    def frees(self): return self.proc.frees()|accFrees(self.params)
    def eval(self, tm, cfg):
        clos = self.proc.eval(tm, cfg)
        paramss = tuple(pm.eval(tm, cfg) for pm in self.params)
        nexts = []
        for clo in clos:
            ntm = clo.proc.advance(Context(self, tm), clo.time)
            nexts.append(applyProc(tm, clo, paramss, ntm, cfg))
        return nexts
def applyProc(tm, clo, paramss, ntm, cfg):
    proc, ptm = clo
    bvs = tuple(zip((Binding(bv, ntm) for bv in proc.binders), paramss))
    fvs = tuple((Binding(fv, ntm), cfg.store.get(Binding(fv, ptm)))
                for fv in proc.frees())
    return State(Context(proc.code, ntm), cfg.update(tm, clo, bvs, fvs))

class VExpr(Expr):
    def eval(self, tm, cfg): raise NotImplementedError
class Var(VExpr):
    def __init__(self, name, *args): super().__init__(*args); self.name = name
    def __str__(self): return str(self.name)
    def frees(self): return {self.name}
    def eval(self, tm, cfg): return cfg.store.get(Binding(self.name, tm))
class UVar(Var): pass
class CVar(Var): pass
class Proc(VExpr):
    def __init__(self, binders, code, *args):
        super().__init__(*args); self.binders = binders; self.code = code
    def __str__(self):
        return '(%s %s %s)'%(self.strTag, strTup(self.binders), str(self.code))
    def frees(self): return self.code.frees()-set(self.binders)
    def eval(self, tm, cfg): return cfg.store.single(Closure(self, tm))
    def isCont(self): return False
class UProc(Proc):
    strTag = 'uproc'
    def advance(self, ctx, tm): return advance(ctx)
class CProc(Proc):
    strTag = 'cproc'
    def advance(self, ctx, tm): return tm
    def isCont(self): return True
def isCont(val): return isinstance(val, Closure) and val.proc.isCont()
def progState(proc, params, tm):
    cfg = newConfig(); clo = Closure(proc, tm)
    return applyProc(tm, clo, params+(makeHalt().eval(tm, cfg),), tm, cfg)

def freshUVar(alpha=alphaGen(['u'])): return UVar(Name(next(alpha)))
def freshCVar(alpha=alphaGen(['k'])): return CVar(Name(next(alpha)))
class DExpr(Expr):
    def toCPS(self, ce): raise NotImplementedError
class DVar(DExpr):
    def __init__(self, name, *args): super().__init__(*args); self.name = name
    def __str__(self): return str(self.name)
    def toCPS(self, ce): return Call(ce, (UVar(self.name, self.lab),))
class DProc(DExpr):
    def __init__(self, binders, body, *args):
        super().__init__(*args); self.binders = binders; self.body = body
    def __str__(self):
        return '(dproc %s %s)'%(strTup(self.binders), str(self.body))
    def toCPS(self, ce):
        cv = freshCVar()
        uproc = UProc(self.binders+(cv.name,), self.body.toCPS(cv), self.lab)
        return Call(ce, (uproc,))
class DApply(DExpr):
    def __init__(self, proc, params, *args):
        super().__init__(*args); self.proc = proc; self.params = params
    def __str__(self): return '(%s %s)'%(str(self.proc), strTup(self.params))
    def toCPS(self, ce):
        uvp = freshUVar(); uvs = tuple(freshUVar() for _ in self.params)
        call = Call(uvp, uvs+(ce,), self.lab)
        for uv, param in reversed(tuple(zip(uvs, self.params))):
            call = param.toCPS(CProc((uv.name,), call))
        return self.proc.toCPS(CProc((uvp.name,), call))
def dLetStar(bnds, body):
    for (binder, de) in reversed(bnds):
        body = DApply(DProc((binder,), body), (de,))
    return body
def dProg(dexpr):
    haltBnd = Name('halt'); return UProc((haltBnd,), dexpr.toCPS(Var(haltBnd)))

def garbageCollect(state): return state.garbageCollect()
def search(seen, unseen):
    while unseen:
        state = garbageCollect(unseen.pop()); cfg = seen.get(state.ctx)
        if cfg is not None:
            if cfg.contains(state.cfg): continue
            cfg = cfg.join(state.cfg)
            state = garbageCollect(State(state.ctx, cfg)) # context widening
        else: cfg = state.cfg
        seen[state.ctx] = cfg; unseen.extend(state.next())
    return seen
def searchProg(proc, mx=0):
    return search({}, [progState(proc, (), AbstractTime((), mx))])
def summary(seen):
    cfg = newConfig(); return reduce(cfg.__class__.join, seen.values(), cfg)
################################################################
# testing
#  (let* ((id (lambda (x) x))
#         (a (id (lambda (z) z)))
#         (b (id (lambda (y) y))))
#   b))
dvID, dvA, dvB, dvX, dvY, dvZ = [DVar(Name(nm)) for nm in
                                 ('id', 'a', 'b', 'x', 'y', 'z')]
testProg = dProg(dLetStar([(dvID.name, DProc((dvX.name,), dvX)),
                           (dvA.name,
                            DApply(dvID, (DProc((dvZ.name,), dvZ),))),
                           (dvB.name,
                            DApply(dvID, (DProc((dvY.name,), dvY),)))],
                          dvB))
test = searchProg(testProg, 1)
testSum = summary(test)
testSum.print()
