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

from type import *
from functools import reduce
from itertools import chain
import os

def final(val): return None, val
def cont(ctx, expr): return ctx, expr
def evalExpr(ctx, expr, ty=None): # tail-call trampoline
    while ctx is not None: ctx, expr = expr.eval(ctx)
    if ty is not None: ty.checkTy(expr)
    return expr # when ctx is None, expr will be a final value
class Expr:
    def freeVars(self): return set()
    def subst(self, subs): pass
    def pretty(self): return 'todo'

################################################################
class Atom(Expr): pass
class PrimVal(Atom):
    def __init__(self, val): self.val = val
    def eval(self, ctx): return final(self.val)
class Var(Atom):
    def __init__(self, name): self.name = name
    def freeVars(self): return set([self.name])
    def subst(self, subs):
        newName = subs.get(self.name)
        if newName is not None: self.name = newName
    def eval(self, ctx):
        val = ctx.env.get(self.name)
        if val is None: typeErr(ctx, "unbound variable '%s'"%self.name)
        return final(val)

################################################################
# symbols
ubSymTy = ScalarType('#Symbol')
nextSymId = 0
def ubSymbol_new(n):
    global nextSymId
    assert type(n) is str, n
    sd = (n, nextSymId)
    nextSymId += 1
    return sd
symTy = ProductType('Symbol', (ubSymTy,))
def isSymbol(v): return getTy(v) is symTy
def symbol_new(n): return symTy.new(ubSymTy.new(ubSymbol_new(n)))
def symbol_prim(s): return getVal(symTy.unpackEl(s, 0))
def symbol_name(s): return symbol_prim(s)[0]
def symbol_id(s): return symbol_prim(s)[1]
def symbol_eq(s1, s2): return symbol_prim(s1) == symbol_prim(s2)
symTable = {}
def symbol(n, table=symTable):
    s = table.get(n)
    if s is None: s = symbol_new(n); table[n] = s
    return s
def nameGen(alphabet=[chr(o) for o in range(ord('a'), ord('z')+1)]):
    rep = 0
    while True:
        repStr = str(rep)
        for s in alphabet: yield s+repStr
        rep += 1
def alias_new(sym): return symbol_new(symbol_name(sym))
def gensym(names=nameGen()): return symbol_new(next(names))

################################################################
# envs
class Env:
    __slots__ = ['p', 'bs']
    def __init__(self, p=None): self.p = p; self.bs = {}
    def get(self, n):
        for e in self._lineage():
            v = e.bs.get(n)
            if v is not None: return v
        return None
    def add(self, n, v):
        assert self.bs.get(n) is None, "redefinition of '%s'"%n
        self.bs[n] = v
    def bindings(self):
        bs = {}
        for e in reversed(tuple(self._lineage())): bs.update(e.bs)
        return bs
    def show(self): return '\n'.join(repr(e.bs) for e in self._lineage())
    def __repr__(self): return '<Env>'
    def _lineage(self):
        e = self
        while e is not None: yield e; e = e.p
class EnvKey:
    __slots__ = ['sym']
    def __init__(self, sym): self.sym = sym
    def __hash__(self): return symbol_id(self.sym)
    def __eq__(self, n): return hash(self) == hash(n)
    def __repr__(self): return '<EnvKey %r>' % prettySymbol(self.sym)
    def __str__(self): return prettySymbol(self.sym)

################################################################
# procs
class NativeProc:
    def __init__(self, name, code, binders):
        self.name = name; self.code = code; self.binders = binders
    def freeVars(self): return self.code.freeVars()-set(self.binders)
    def subst(self, subs):
        subs = dict((old, new) for old, new in subs if old not in self.binders)
        self.code.subst(subs)
    def call(self, ctx, args):
        ctx = ctx.copy(); ctx.env = Env(ctx.env)
        for binder, arg in zip(self.binders, args): ctx.env.add(binder, arg)
        return self.code.eval(ctx)
    def arity(self): return len(self.binders)
class NativeClosure:
    def __init__(self, proc, ctx): self.proc = proc; self.ctx = ctx
    def __str__(self): return str(self.proc.name)
    def call(self, args): return self.proc.call(self.ctx, args)
    def arity(self): return self.proc.arity()
class ForeignProc:
    def __init__(self, name, code, argc):
        self.name = name; self.code = code; self.argc = argc
    def __str__(self): return str(self.name)
    def call(self, args): return self.code(*args)
    def arity(self): return self.argc
class PartialApp:
    def __init__(self, proc, saved, ty):
        self.proc = proc; self.saved = saved; self.ty = ty
    def __repr__(self):
        return '<PApp %s %s>'%(self.proc, tuple(map(pretty, self.saved)))
    def arity(self): return self.proc.arity()-len(self.saved)
    def apply(self, ctx, args):
        nextTy, argts, nextArity = self.ty.appliedTy(len(args), self.arity())
        saved = self.saved+tuple(evalExpr(ctx, arg, argt)
                                 for argt, arg in zip(argts, args))
        if nextArity == 0: return self.proc.call(saved), args[len(argts):]
        return final(nextTy.new(PartialApp(self.proc, saved, nextTy))), ()
def proc_new(proc, ctx, ty):
    return ty.new(PartialApp(NativeClosure(proc, ctx), (), ty))
def fproc_new(name, code, ty):
    return ty.new(PartialApp(ForeignProc(name, code), (), ty))
def applyFull(ctx, proc, args):
    cprc = cont(ctx, proc)
    while args:
        proc = evalExpr(*cprc) # lifted out here for tail-calls
        if isProc(proc): cprc, args = getVal(proc).apply(ctx, args)
        else: typeError(ctx, "cannot apply non-procedure: '%s'"%proc)
    return cprc

################################################################
class Constr(Expr): pass
class ConsProc(Constr):
    def __init__(self, name, binders, body, paramts, rett):
        # todo: what about fake rett in light of nested ConsProcs?
        if isinstance(body, ConsProc): # combine adjacently-nested ConsProcs
            if rett is None:
                paramts = list(paramts)
                ts, rett = uncurryProcType(body.ty, len(body.proc.binders))
                paramts.extend(ts)
            binders += body.proc.binders; body = body.proc.code
        if rett is None: rett = anyTy
        self.proc = NativeProc(name, body, binders)
        self.ty = currySpecificProcType(name, paramts, rett)
    def freeVars(self): return self.proc.freeVars()
    def subst(self, subs): self.proc.subst(subs)
    def eval(self, ctx): return final(proc_new(self.proc, ctx, self.ty))
def accFreeVars(xs): return reduce(set.union,(x.freeVars() for x in xs),set())
def mapSubst(subs, xs):
    for xx in xs: xx.subst(subs)
class ConsNode(Constr):
    def __init__(self, ty, cargs, ctx=None):
        if not isinstance(ty, ProductType):
            typeErr(ctx, "invalid product type: '%s'"%ty)
        ty.checkIndex(len(cargs),
                      'incorrect number of constructor arguments:', True)
        self.ty = ty; self.cargs = cargs
    def freeVars(self): return accFreeVars(xs)
    def subst(self, subs): mapSubst(subs, self.cargs)
    def eval(self, ctx):
        cargs = [evalExpr(ctx, carg) for carg in self.cargs]
        return final(node(self.ty, *cargs))
def constr_new(ctx, ty):
    assert isinstance(ty, ProductType), ty
    cargs = [EnvKey(gensym()) for elt in ty.elts]
    cty = currySpecificProcType(ty.name, ty.elts, ty)
    body = ConsNode(ty, [Var(nm) for nm in cargs], ctx)
    return proc_new(NativeProc(cty.name, body, cargs), ctx, cty)

################################################################
# primitives
def populator():
    population = {}
    def adder(name, val):
        sym = symbol(name); den = alias_new(sym); nm = EnvKey(sym)
        assert nm not in population, name; population[nm] = (den, val)
    return population, adder
primitives, addPrim = populator()
primTypes, addPrimTy = populator()
def primDen(name): return primitives.get(EnvKey(symbol(name)))[0]
addPrimTy('Symbol', symTy)
addPrimTy('Any', anyTy)
def prodTy(name, *elts):
    ty = ProductType(name, elts); addPrimTy(name, ty); return ty
def node(ty, *args): return ty.new(*args)
def singleton(name):
    ty = prodTy(name); val = ty.new(); addPrim(name, val); return ty, val
unitTy, unit = singleton('Unit')
unitDen = primDen('Unit')

################################################################
# basic values
def basicTy(name, pyty):
    ubTy = PyType('#'+name, pyty); addPrimTy('#'+name, ubTy)
    ty = prodTy(name, ubTy)
#    def isX(v): return node_tag(v) is tag
    def toX(v): return ty.new(ubTy.new(v))
    def fromX(v): return getVal(ty.unpackEl(v, 0))
    return ubTy, ty, toX, fromX
ubIntTy, intTy, toInt, fromInt = basicTy('Int', int)
ubFloatTy, floatTy, toFloat, fromFloat = basicTy('Float', float)
ubCharTy, charTy, toChar, fromChar = basicTy('Char', str)

################################################################
# lists
listTy = VariantType()
nilTy, nil = singleton('Nil')
consTy = prodTy(':', anyTy, listTy)
listTy.init((nilTy, consTy))
addPrimTy('List', listTy)
def cons(h, t): return consTy.new(h, t)
def cons_head(x): return consTy.unpackEl(x, 0)
def cons_tail(x): return consTy.unpackEl(x, 1)
def isListCons(x): return getTy(x) is consTy
def isList(x): return x is nil or isListCons(x)
def toList(args, tail=nil):
    for x in reversed(args): tail = cons(x, tail)
    return tail
def fromList(xs, repeat=None):
    assert isList(xs), xs
    while xs is not nil:
        if repeat is not None:
            if id(xs) in repeat: return
            repeat.append(id(xs))
        yield cons_head(xs)
        xs = cons_tail(xs)
    if repeat is not None: del repeat[:]

################################################################
# contexts
class Context:
    def __init__(self, root, nspace, ops, tenv, senv, env, attr, hist=nil):
        self.root = root; self.nspace = nspace
        self.ops = ops; self.tenv = tenv; self.senv = senv; self.env = env
        self.attr = attr; self.hist = hist
    def __eq__(self, rhs): return self._cmp() == rhs._cmp()
    def _cmp(self): return (self.ops, self.tenv, self.senv)
    def copy(self):
        return Context(self.root, self.nspace,
                       self.ops, self.tenv, self.senv, self.env,
                       self.attr, self.hist)
    def branch(self):
        ctx = self.copy(); ctx.ops = Env(ctx.ops)
        ctx.tenv = Env(ctx.tenv); ctx.senv = Env(ctx.senv); return ctx
    def histAppend(self, form): self.hist = cons(form, self.hist)
ubCtxTy, ctxTy, toCtx, fromCtx = basicTy('Ctx', Context)
def getDen(xenv, sym):
    den = xenv.get(EnvKey(sym))
    if den is None: den = alias_new(sym); xenv.add(EnvKey(sym), den)
    return den
def referX(xenvFrom, xenvTo, symFrom, symTo=None):
    if symTo is None: symTo = symFrom
    xenvTo.add(EnvKey(symTo), EnvKey(getDen(xenvFrom, symFrom)))
def referVar(ctxFrom, ctxTo, sym): referX(ctxFrom.senv, ctxTo.senv, sym)
def getX(xenv, env, sym): return env.get(EnvKey(getDen(xenv, sym)))
def bindX(xenv, env, sym, xx): env.add(EnvKey(getDen(xenv, sym)), xx)
def bindVar(ctx, sym, val): bindX(ctx.senv, ctx.env, sym, val)
def bindTy(ctx, sym, ty): bindX(ctx.tenv, ctx.env, sym, ty)

def setPrims(ctx, xenv, xs, name, extra=lambda a,b,c:None):
    print('adding primitive %s:'%name)
    for name, (den, xx) in xs.items():
        print(name); xenv.add(name, den); ctx.env.add(EnvKey(den), xx)
        extra(ctx, name, xx)
def addPrimCons(ctx, name, ty):
    if isinstance(ty, ProductType) and ty.elts:
        addPrim(symbol_name(name.sym), constr_new(ctx, ty))
def freshCtx(root, nspace):
    return Context(root, nspace, Env(), Env(), Env(), Env(), None)
def loadPrims(ctx):
    setPrims(ctx, ctx.tenv, primTypes, 'types', addPrimCons)
    setPrims(ctx, ctx.senv, primitives, 'values')
def primCtx(root=None, nspace=None):
    ctx = freshCtx(root, nspace); loadPrims(ctx); return ctx

################################################################
# syntactic closures
formTy = VariantType()
syncloTy = prodTy('SynClo', ctxTy, listTy, formTy) # todo
formTy.init((listTy, symTy, syncloTy, intTy, floatTy, charTy))
addPrimTy('SynForm', formTy)
def isSynClo(s): return getTy(s) is syncloTy
def synclo_new(ctx, frees, form): return syncloTy.new(ctx, frees, form)
def synclo_ctx(s): return syncloTy.unpackEl(s, 0)
def synclo_frees(s): return syncloTy.unpackEl(s, 1)
def synclo_form(s): return syncloTy.unpackEl(s, 2)
def applySynCloCtx(ctx, sc):
    ctx = ctx.copy(); scCtx = fromCtx(synclo_ctx(sc)); senv = scCtx.senv
    frees = fromList(synclo_frees(sc))
    if frees:
        senv = Env(senv)
        for n in frees:
            n = EnvKey(n); v = ctx.senv.get(n)
            if v is not None: senv.extend(n, v)
    ctx.tenv = scCtx.tenv; ctx.senv = senv; return ctx
def syncloExpand(ctx, xs):
    while isSynClo(xs): ctx = applySynCloCtx(ctx, xs); xs = synclo_form(xs)
    return ctx, xs

################################################################
# arrays

################################################################
# strings
#stringTy = prodTy('String', None) # todo
def toString(v): return node(stringTy, v)
#def fromString(v): assert isString(v), v; return v[1]

################################################################
# macros and semantics
macroTy = prodTy('Macro', curryProcType((ctxTy, formTy), formTy))
def isMacro(v): return isTyped(v) and getTy(v) is macroTy
def macro_proc(mac): return macroTy.unpackEl(mac, 0)
def applyMacro(ctx, mac, form):
    return evalExpr(*applyFull(ctx, macro_proc(mac), [toCtx(ctx), form]))
ubSemanticTy, semanticTy, toSem, fromSem = basicTy('Semantic', object)
def isSemantic(v): return isTyped(v) and getTy(v) is semanticTy
def applySemantic(ctx, sem, form): return fromSem(sem)(ctx, form)

################################################################
# pretty printing
def prettyList(xs, seen):
    seen.append(id(xs)); shown = []; repeat = []
    for x in fromList(xs, repeat): shown.append(pretty(x, seen))
    if repeat: shown.append('...')
    seen.remove(id(xs)); return '[%s]'%' '.join(shown)
def prettySymbol(s, _=None): return symbol_name(s)
def prettySynClo(s, seen):
    seen.append(id(s))
    pret = ('(SynClo <ctx> %s %s)'%
            (#synclo_senv(s), # todo: string rep
             prettyList(synclo_frees(s), seen), pretty(synclo_form(s), seen)))
    seen.remove(id(s)); return pret
def prettyInt(i, _=None): return repr(fromInt(i))
def prettyFloat(f, _=None): return repr(fromFloat(f))
escapes = {
    '\a': '\\a',
    '\b': '\\b',
    '\t': '\\t',
    '\n': '\\n',
    '\v': '\\v',
    '\f': '\\f',
    '\r': '\\r',
    }
# todo: unprintable unicode chars
def escaped(c, delim):
    cc = escapes.get(c)
    if cc is not None: return cc
    elif c == delim: return '\\'+delim
    return c
def prettyChar(c, _=None): return "'%s'"%''.join(escaped(c, "'")
                                                 for c in fromChar(c))
def prettyString(s, _=None):
    return '"%s"'%''.join(escaped(c, '"') for c in fromString(s))
tagToPretty = {nilTy: prettyList, consTy: prettyList,
               symTy: prettySymbol,
               syncloTy: prettySynClo,
               unitTy: lambda _,__: '()',
               intTy: prettyInt, floatTy: prettyFloat, charTy: prettyChar,
               #stringTy: prettyString,
               }
def pretty(v, seen=None):
    if seen is None: seen = []
    if id(v) in seen: return '(...)'
    if isTyped(v):
        pp = tagToPretty.get(getTy(v))
        if pp is None:
            if isinstance(getTy(v), ProductType):
                seen.append(id(v)); ty = getTy(v)
                els = ' '.join(pretty(ty.unpackEl(v, idx), seen)
                               for idx in range(ty.numIndices()))
                seen.remove(id(v)); return '(%s)'%('%s %s'%(ty, els)).rstrip()
            return '<%s %s>'%(getTy(v), getVal(v))
        else: return pp(v, seen)
    else: return '<ugly %s>'%repr(v)

################################################################
# streams
class Stream:
    def __init__(self, itr):
        self.itr = itr
        self.buffer = []
    def __iter__(self): return self
    def __next__(self):
        if self.buffer: return self.buffer.pop()
        return next(self.itr)
    def put(self, x): self.buffer.append(x)
    def peek(self):
        x = next(self)
        self.put(x)
        return x
    def empty(self):
        if self.buffer: return False
        try: self.put(next(self.itr))
        except StopIteration: return True
        return False
    def compose(self, mkItr): return makeStream(mkItr(self.itr))
def makeStream(s):
    if not isinstance(s, Stream): s = Stream(s)
    return s

def resolvePath(searchPaths, path):
    curdir = os.getcwd(); ap = None
    for start in searchPaths:
        os.chdir(start); ap = os.path.abspath(path)
        if os.path.exists(ap): break
        ap = None
    os.chdir(curdir); return ap
def fileStream(path): return open(path)
exportAllFilter = (True, set(), {})
class Root:
    def __init__(self, coreMod, searchPaths=('.',)):
        self.coreMod = coreMod; self.searchPaths = searchPaths
        self.modules = {}
    def _makeModule(self, name, stream):
        mod = Module(name, stream, self)
        self.coreMod.export(mod.curNS, exportAllFilter)
        return mod
    def getFileModule(self, fpath):
        name = EnvKey(symbol(fpath)); mod = self.modules.get(name)
        if mod is None:
            mod = self._makeModule(name, fileStream(fpath))
            self.modules[name] = mod
        elif mod.isActive(): typeErr(None, "module self-dependency: '%s'"%name)
        return mod
class DepGraph:
    def __init__(self):
        self.deps = {}; self.finished = set()
    def finish(self, name): del self.deps[name]; self.finished.add(name)
    def add(self, name, deps):
        assert name not in deps, name
        self.deps[name] = [deps, []]
    def dfs(self, seen, finished, name, idx):
        seen.add(name)
        for dn in self.deps[name][idx]:
            if dn not in self.finished:
                if idx == 0: self.deps[dn][1].append(name)
                if dn not in seen: self.dfs(seen, finished, dn, idx)
        finished.append(name)
    def depSort(self, name):
        if name in self.finished: return []
        finished = []; self.dfs(set(), finished, name, 0)
        seen = set(); components = []
        for name in reversed(finished):
            if name not in seen:
                component = []; components.append(component)
                self.dfs(seen, component, name, 1)
            self.finish(name)
        return components
