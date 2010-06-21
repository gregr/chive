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

class UnwindExc(Exception): pass
def final(val): return None, val
def cont(ctx, expr): return ctx, expr
def evalExpr(ctx, expr, ty=None): # tail-call trampoline
    try:
        while ctx is not None: ctx, expr = expr.eval(ctx)
    except UnwindExc: raise
    except Exception as exc:
        if ctx.root.onErr is None: raise
        expr = ctx.root.onErr(exc, ctx, expr)
        if expr is None: raise
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
# type types
ubTyTy = PyType('_Type', Type)
tyTy = ProductType('Type', (ubTyTy,), const=True)
def isType(tt): return getTag(tt) is tyTy
def type_new(tt): return tyTy.new(ubTyTy.new(tt))
def type_type(tt): return getVal(tyTy.unpackEl(tt, 0))
################################################################
# symbols
ubSymTy = ScalarType('_Symbol')
nextSymId = 0
def ubSymbol_new(n):
    global nextSymId
    assert type(n) is str, n
    sd = (n, nextSymId)
    nextSymId += 1
    return sd
symTy = ProductType('Symbol', (ubSymTy,), const=True)
def isSymbol(v): return isTyped(v) and getTag(v) is symTy
def toSymbol(ps): return symTy.new(ubSymTy.new(ps))
def symbol_new(n): return toSymbol(ubSymbol_new(n))
def symbol_prim(s): return getVal(symTy.unpackEl(s, 0))
def symbol_name(s): return symbol_prim(s)[0]
def symbol_id(s): return symbol_prim(s)[1]
def symbol_eq(s1, s2): return symbol_prim(s1) == symbol_prim(s2)
symTable = {}
def symbol(n, table=symTable):
    ubs = table.get(n)
    if ubs is None: ubs = ubSymTy.new(ubSymbol_new(n)); table[n] = ubs
    return symTy.new(ubs)
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
        ov = self.bs.get(n)
        if ov is not None and ov is not v:
            typeErr(None, "redefinition of '%s'"%n)
        self.bs[n] = v
    def bindings(self):
        bs = {}
        for e in reversed(tuple(self._lineage())): bs.update(e.bs)
        return bs
    def stratified(self):
        for e in reversed(tuple(self._lineage())): yield e.bs
    def show(self): return '\n'.join(repr(e.bs) for e in self._lineage())
    def __repr__(self): return '<Env>'
    def _lineage(self):
        e = self
        while e is not None: yield e; e = e.p
class EnvKey:
    __slots__ = ['sym']
    def __init__(self, sym): assert isSymbol(sym), sym; self.sym = sym
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
        ctx = ctx.extendValues()
        for binder, arg in zip(self.binders, args): ctx.env.add(binder, arg)
        return self.code.eval(ctx)
    def arity(self): return len(self.binders)
class NativeClosure:
    def __init__(self, proc, ctx): self.proc = proc; self.ctx = ctx
    def __str__(self): return str(self.proc.name)
    def call(self, ctx, args):
        return self.proc.call(self.ctx.withThread(ctx.thread), args)
    def arity(self): return self.proc.arity()
class ForeignProc:
    def __init__(self, name, code, argc):
        self.name = name; self.code = code; self.argc = argc
    def __str__(self): return str(self.name)
    def call(self, ctx, args): return self.code(ctx, *args)
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
        if nextArity == 0: return self.proc.call(ctx,saved), args[len(argts):]
        return final(nextTy.new(PartialApp(self.proc, saved, nextTy))), ()
def proc_new(proc, ctx, ty):
    return ty.new(PartialApp(NativeClosure(proc, ctx), (), ty))
def fproc_new(name, code, ty, argc):
    return ty.new(PartialApp(ForeignProc(name, code, argc), (), ty))
def applyFull(ctx, proc, args):
    cprc = cont(ctx, proc)
    while args:
        proc = evalExpr(*cprc) # lifted out here for tail-calls
        if isProc(proc): cprc, args = getVal(proc).apply(ctx, args)
        else: typeErr(ctx, "cannot apply non-procedure: '%s'"%pretty(proc))
    return cprc
def applyDirect(ctx, proc, args):
    return applyFull(ctx, PrimVal(proc), tuple(PrimVal(arg) for arg in args))
################################################################
# thunks
class Thunk:
    def __init__(self, ctx, code):
        self.ty = anyTy; self.ctx = ctx; self.code = code
    def expectTy(self, ty):
        if self.ty.contains(ty): self.ty = ty
    def _eval(self, ctx):
        return evalExpr(self.ctx.withThread(ctx.thread), self.code, self.ty)
    def force(self, ctx, box):
        if self.ctx is not None: self.code = self._eval(ctx)
        box[:] = self.code[:]; return box
def force(ctx, box):
    if isThunk(box): box = getVal(box).force(ctx, box)
    return box
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
class ConsThunk(Constr):
    def __init__(self, name, body):
        self.ty = ThunkType(name); self.body = body
    def freeVars(self): return self.body.freeVars()
    def subst(self, subs): self.body.subst(subs)
    def eval(self, ctx): return final(self.ty.new(Thunk(ctx, self.body)))
class ConsNode(Constr):
    def __init__(self, ty, cargs, ctx=None):
        if not isinstance(ty, ProductType):
            typeErr(ctx, "invalid product type: '%s'"%ty)
        ty.checkIndex(len(cargs),
                      'incorrect number of constructor arguments:', True)
        self.ty = ty; self.cargs = cargs
    def freeVars(self): return accFreeVars(self.cargs)
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
class ConsColl(Constr):
    def __init__(self, ty, ctx=None):
        self.ty = ty
        if not isinstance(ty, (ArrayType, TableType)):
            typeErr(ctx, "invalid collection type: '%s'"%ty)
    def eval(self, ctx): return final(self.ty.new())

################################################################
# contexts
class History:
    def __init__(self, parent=None):
        self.parent = parent; self.main = []; self.subs = []
        self.final = None
    def add(self, form): self.main.append(form)
    def newSub(self): sh = History(self); self.subs.append(sh); return sh
    def finish(self, form):# pass
        if self.final is None: self.final = form
        else: assert form is self.final, (pretty(form), pretty(self.final))
        self.subs = [sh for sh in self.subs if sh.main or sh.subs]
    def show(self):
        return '\n'.join(map(pretty, chain(self.main, [self.final])))
class Context: # current file resolution dir
    def __init__(self, root, thread, nspace, readers, ops, tenv, senv, env,
                 src, hist=None):
        self.root = root; self.thread = thread; self.nspace = nspace
        self.readers = readers; self.ops = ops
        self.tenv = tenv; self.senv = senv; self.env = env
        self.src = src; self.hist = hist or History()
    def __eq__(self, rhs): return self._cmp() == rhs._cmp()
    def _cmp(self): return (self.ops, self.tenv, self.senv)
    def copy(self):
        return Context(self.root, self.thread, self.nspace,
                       self.readers, self.ops, self.tenv, self.senv, self.env,
                       self.src, self.hist)
    def subHist(self):
        ctx = self.copy(); ctx.hist = ctx.hist.newSub(); return ctx
    def withThread(self, thread):
        ctx = self.copy(); ctx.thread = thread; return ctx
    def extendSyntax(self, ops=False):
        ctx = self.copy(); ctx.senv = Env(self.senv)
        if ops: ctx.ops = Env(self.ops)
        return ctx
    def extendValues(self):
        ctx = self.copy(); ctx.env = Env(self.env); return ctx
def nullCtx(src):
    return Context(None, None, None, None, None, None, None, None, src)
def newDen(ctx, sym):
    den = alias_new(sym); ctx.senv.add(EnvKey(sym), den); return den
def newTyDen(ctx, sym):
    den = alias_new(sym); ctx.tenv.add(EnvKey(sym), den); return den
def getDen(ctx, sym):
    den = ctx.senv.get(EnvKey(sym))
    if den is None: den = newDen(ctx.nspace.ctx, sym)
    return den
def getTyDen(ctx, sym):
    den = ctx.tenv.get(EnvKey(sym))
    if den is None: den = newTyDen(ctx.nspace.ctx, sym)
    return den
def referVar(ctxFrom, ctxTo, symFrom, symTo=None):
    if symTo is None: symTo = symFrom
    ctxTo.senv.add(EnvKey(symTo), getDen(ctxFrom, symFrom))
def referTy(ctxFrom, ctxTo, symFrom, symTo=None):
    if symTo is None: symTo = symFrom
    ctxTo.tenv.add(EnvKey(symTo), getTyDen(ctxFrom, symFrom))
def valNames(ctx): return ctx.senv.bindings().keys()
def tyNames(ctx): return ctx.tenv.bindings().keys()
def getVar(ctx, sym): return ctx.env.get(EnvKey(getDen(ctx, sym)))
def getTy(ctx, sym): return ctx.env.get(EnvKey(getTyDen(ctx, sym)))
def bindVar(ctx, sym, val): ctx.env.add(EnvKey(getDen(ctx, sym)), val)
def bindTy(ctx, sym, ty): ctx.env.add(EnvKey(getTyDen(ctx, sym)), ty)
def defVar(ctx, sym, val): ctx.nspace.defVar(sym, val)
def defTy(ctx, sym, ty): ctx.nspace.defTy(sym, ty)
def freshCtx(root, nspace):
    return Context(root, None, nspace, Env(), Env(), Env(), Env(), Root.env,
                   None)
################################################################
# modules
def resolvePath(searchPaths, path):
    curdir = os.getcwd(); ap = None
    for start in searchPaths:
        os.chdir(start); ap = os.path.abspath(path)
        if os.path.exists(ap): break
        ap = None
    os.chdir(curdir); return ap
class Module:
    gnames = nameGen(['top'])
    def __init__(self, iface, nspace):
        self.iface = iface; self.nspace = nspace; self.name = next(self.gnames)
    def valNames(self): return self.iface.valNames(self.nspace)
    def valResolve(self, sym): return self.iface.valResolve(self.nspace, sym)
    def tyNames(self): return self.iface.tyNames(self.nspace)
    def tyResolve(self, sym): return self.iface.tyResolve(self.nspace, sym)
    def readerStrs(self): return self.iface.readerStrs(self.nspace)
    def openIn(self, nspace):
        for nm in self.valNames(): nspace.referVar(self.nspace.ctx, nm.sym)
        for nm in self.tyNames(): nspace.referTy(self.nspace.ctx, nm.sym)
        for chs in self.readerStrs():
            nspace.defReader(chs, self.nspace.ctx.readers.get(chs))
# generalize to ModifiedModule?
# HidingModule
# class RenamedModule:
#     def __init__(self, iface, remap): self.iface = iface; self.nameMap = remap
#     def valNames(self): return set(self.nameMap.keys())
#     def valResolve(self, nspace, sym):
#         sym = self.nameMap.get(EnvKey(sym))
#         if sym is not None: return self.iface.valResolve(nspace, sym)
class Interface: pass
class FullInterface(Interface): # only use internally?
    def valNames(self, nspace): return nspace.valNames()
    def valResolve(self, nspace, sym): return nspace.valResolve(sym)
    def tyNames(self, nspace): return nspace.tyNames()
    def tyResolve(self, nspace, sym): return nspace.tyResolve(sym)
    def readerStrs(self, nspace): return nspace.readerStrs()
class ExportInterface(Interface):
    def __init__(self, valueSyms, typeSyms, readerStrs):
#        syntaxNames = set(map(EnvKey, syntaxSyms))
        self.vns = set(map(EnvKey, valueSyms))#|syntaxNames
        self.tns = set(map(EnvKey, typeSyms))
#        self.sns = syntaxNames
        self.readerStrs = set(readerStrs)
    def valNames(self, nspace): return self.vns
    def tyNames(self, nspace): return self.tns
    def valResolve(self, nspace, sym):
        names = self.valNames()
        if EnvKey(sym) in names: return nspace.valResolve(sym)
        else: typeErr(None, "cannot resolve value '%s'; exports: '%s'"
                      %(EnvKey(sym), names))
    def tyResolve(self, nspace, sym):
        names = self.tyNames()
        if EnvKey(sym) in names: return nspace.tyResolve(sym)
        else: typeErr(None, "cannot resolve type '%s'; exports: '%s'"
                      %(EnvKey(sym), names))
    def readerStrs(self, nspace): return self.readerStrs
class CompoundInterface(Interface):
    def __init__(self, ifaces): self.ifaces = ifaces
    def _union(self, nspace, attr):
        return reduce(set.union,
                      (getattr(ifc, attr)(nspace) for ifc in self.ifaces))
    def _resolve(self, nspace, sym, attr):
        for ifc in self.ifaces:
            val = getattr(ifc, attr)(nspace, sym)
            if val is not None: return val
    def valNames(self, nspace): return self._union(nspace, 'valNames')
    def valResolve(self, nspace, sym):
        return self._resolve(nspace, sym, 'valResolve')
    def tyNames(self, nspace): return self._union(nspace, 'tyNames')
    def tyResolve(self, nspace, sym):
        return self._resolve(nspace, sym, 'tyResolve')
    def readerStrs(self, nspace): return self._union(nspace, 'readerStrs')
class Namespace:
    def __init__(self, root): self.ctx = freshCtx(root, self)
    def valNames(self): return valNames(self.ctx)
    def tyNames(self): return tyNames(self.ctx)
    def valResolve(self, sym): return getVar(self.ctx, sym)
    def tyResolve(self, sym): return getTy(self.ctx, sym)
    def readerStrs(self): return self.ctx.readers.bindings().keys()
    def referVar(self, ctxFrom, symFrom, symTo=None):
        referVar(ctxFrom, self.ctx, symFrom, symTo)
    def referTy(self, ctxFrom, symFrom, symTo=None):
        referTy(ctxFrom, self.ctx, symFrom, symTo)
    def defVar(self, sym, val): bindVar(self.ctx, sym, val)
    def defTy(self, sym, val): bindTy(self.ctx, sym, val)
    def defOp(self, sym, op): self.ctx.ops.add(EnvKey(sym), op)
    def defReader(self, chs, reader): addDisp(chs, reader, self.ctx.readers)
class Source:
    def __init__(self, nspace): self.nspace = nspace
    def eval(self, evaluate): # todo: only eval on demand
        for expr in self.exprs(): evaluate(self.nspace.ctx, expr)
class DirectSource(Source):
    def __init__(self, nspace, exprs):
        super().__init__(nspace); self._exprs = exprs
    def exprs(self): return self._exprs
class StreamSource(Source):
    def exprs(self): # todo: configurable parser
        stream = Stream(self.name(), self.stream())
        parser = Parser(self.nspace.ctx, stream)
        return parser.parse()
class DirectStreamSource(StreamSource):
    def __init__(self, nspace, name, stream):
        super().__init__(nspace); self._name = name; self._stream = stream
    def name(self): return self._name
    def stream(self): return self._stream
class FileSource(StreamSource):
    def __init__(self, nspace, absPath): # ctx with current file resolution dir
        super().__init__(nspace); self.absPath = absPath
    def name(self): return self.absPath
    def stream(self): return open(self.name())

class Thread:
    def __init__(self, root): self.root = root; self.tid = None; self.tls = {}
    def getDataTLS(self, ctx, key):
        data = self.tls.get(key)
        if data is None:
            thunk = self.root.getInitTLS(ctx, key)
            data = thunk._eval(ctx); self.tls[key] = data
        return data
class Root:
    env = Env(); onErr = None
    def __init__(self, searchPaths):
        self.searchPaths = searchPaths; self.tlsInit = {}
    def getInitTLS(self, ctx, key):
        thunk = self.tlsInit.get(key)
        if thunk is None: typeErr(ctx, "invalid thread-local key '%s'"%key)
        return thunk
    def setInitTLS(self, ctx, key, code):
        assert key not in self.tlsInit, key
        # todo: code should rely only on constants
        self.tlsInit[key] = Thunk(ctx, code)
    def emptyModule(self):
        return Module(ExportInterface((),(),()), Namespace(self))
def interactStream(prompt):
    import readline
    from io import StringIO
    buffer = []; prompt2 = ('.'*(len(prompt)-1)) + ' '; line = input(prompt)
    while line: buffer.append(line+'\n'); line = input(prompt2)
    return StringIO(''.join(buffer))
def interactStreams(prompt):
    try:
        while True: yield interactStream(prompt)
    except EOFError: pass
################################################################
# primitives
def node(ty, *args): return ty.new(*args)
primNS = Namespace(None); primCtx = primNS.ctx
def addPrim(name, val):
    print('adding primitive value:', name)
    primNS.defVar(symbol(name), val)
def addConsDen(ctx, sym, ty):
    if len(ty.elts) == 0: consVal = node(ty)
    else: consVal = constr_new(ctx, ty)
    bindVar(ctx, sym, consVal); return consVal
def addPrimTy(name, ty):
    print('adding primitive type:', name)
    primNS.defTy(symbol(name), type_new(ty))
    if isinstance(ty, ProductType):
        return addConsDen(primCtx, symbol(name), ty)
def primDen(name): return getDen(primCtx, symbol(name))
addPrimTy('_Type', ubTyTy); addPrimTy('Type', tyTy)
addPrimTy('_Symbol', ubSymTy); addPrimTy('Symbol', symTy)
addPrimTy('Any', anyTy)
def prodTy(name, *elts, const=None):
    ty = ProductType(name, elts, const=const); addPrimTy(name, ty); return ty
def arrTy(name, elt): ty = ArrayType(name, elt); addPrimTy(name, ty); return ty
def tabTy(name, keyt, elt, weak=False):
    ty = TableType(name, keyt, elt, weak); addPrimTy(name, ty); return ty
def singleton(name): ty = ProductType(name, ()); return ty, addPrimTy(name, ty)
unitTy, unit = singleton('Unit')
unitDen = primDen('Unit')
################################################################
# basic values
def basicTy(name, pyty):
    ubTy = PyType('_'+name, pyty); addPrimTy('_'+name, ubTy)
    ty = prodTy(name, ubTy, const=True)
#    def isX(v): return node_tag(v) is tag
    def toX(v): return ty.new(ubTy.new(v))
    def fromX(v): return getVal(ty.unpackEl(v, 0))
    return ubTy, ty, toX, fromX
ubIntTy, intTy, toInt, fromInt = basicTy('Int', int)
ubFloatTy, floatTy, toFloat, fromFloat = basicTy('Float', float)
ubCharTy, charTy, toChar, fromChar = basicTy('Char', str)
################################################################
# booleans
falseTy, false = singleton('False')
trueTy, true = singleton('True')
boolTy = VariantType((falseTy, trueTy))
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
def isListCons(x): return getTag(x) is consTy
def isList(x): return x is nil or isListCons(x)
def toList(args, tail=nil):
    for x in reversed(args): tail = cons(x, tail)
    return tail
class LazyList(Exception): pass
def fromList(xs, ctx=None, repeat=None):
    assert isList(xs), xs
    while xs is not nil:
        if repeat is not None:
            if id(xs) in repeat: return
            repeat.append(id(xs))
        if isThunk(xs):
            if ctx is not None: xs = force(ctx, xs); continue
            raise LazyList(xs)
        yield cons_head(xs)
        xs = cons_tail(xs)
    if repeat is not None: del repeat[:]
################################################################
# arrays for boxed values
arrayTy = arrTy('Array', anyTy)
################################################################
# strings
stringTy = arrTy('String', ubCharTy)
def isString(val): return getTag(val) is stringTy
def toString(pyStr):
    cs = stringTy.new(); arrConcatList(cs, list(pyStr)); return cs
def fromString(chStr): return ''.join(arrToList(chStr))
def copyString(chStr): return toString(fromString(chStr))
################################################################
# syntactic closures
ubCtxTy, ctxTy, toCtx, fromCtx = basicTy('Ctx', Context)
ubIfaceTy, ifaceTy, toIface, fromIface = basicTy('Interface', Interface)
ubNspaceTy, nspaceTy, toNspace, fromNspace = basicTy('Namespace', Namespace)
ubModTy, modTy, toMod, fromMod = basicTy('Module', Module)
primMod = Module(FullInterface(),primNS); addPrim('primitives', toMod(primMod))
formTy = VariantType()
syncloTy = prodTy('SynClo', ctxTy, listTy, formTy, const=True) # todo
formTy.init((listTy, symTy, syncloTy, intTy, floatTy, charTy, stringTy))
addPrimTy('SynForm', formTy)
def isSynClo(s): return getTag(s) is syncloTy
def synclo_new(ctx, frees, form): return syncloTy.new(ctx, frees, form)
def synclo_ctx(s): return syncloTy.unpackEl(s, 0)
def synclo_frees(s): return syncloTy.unpackEl(s, 1)
def synclo_form(s): return syncloTy.unpackEl(s, 2)
def applySynCloCtx(ctx, sc):
    ctx = ctx.copy(); scCtx = fromCtx(synclo_ctx(sc))
    src = scCtx.src; tenv = scCtx.tenv; senv = scCtx.senv
    if src is not None: ctx.src = src
    if tenv is not None: ctx.tenv = tenv
    if senv is not None:
        frees = fromList(synclo_frees(sc), ctx)
        if frees:
            senv = Env(senv)
            for n in frees:
                n = EnvKey(n); v = ctx.senv.get(n)
                if v is not None: senv.extend(n, v)
        ctx.senv = senv
    return ctx
def syncloExpand(ctx, xs):
    while isSynClo(xs): ctx = applySynCloCtx(ctx, xs); xs = synclo_form(xs)
    return ctx, xs
def stripOuterSynClo(xs):
    while isSynClo(xs): xs = synclo_form(xs)
    return xs
stripSC = stripOuterSynClo
def stripSCs(scs): return tuple(stripOuterSynClo(sc) for sc in scs)
def primSC(form): return synclo_new(toCtx(primCtx), nil, form)
################################################################
# macros and semantics
#macroTy = prodTy('Macro', curryProcType((ctxTy, formTy), formTy), const=True) # todo
macroTy = prodTy('Macro', curryProcType((ctxTy, formTy), anyTy), const=True)
def isMacro(v): return isTyped(v) and getTag(v) is macroTy
def macro_proc(mac): return macroTy.unpackEl(mac, 0)
def applyMacro(ctx, mac, form):
    args = PrimVal(macro_proc(mac)), [PrimVal(toCtx(ctx)), PrimVal(form)]
    return ctx.copy(), evalExpr(*applyFull(ctx, *args))
ubSemanticTy, semanticTy, toSem, fromSem = basicTy('Semantic', object)
def isSemantic(v): return isTyped(v) and getTag(v) is semanticTy
def applySemantic(ctx, sem, form): return fromSem(sem)(ctx, form)
################################################################
# common tables
for ty in (tyTy, symTy, charTy, intTy): ty.hashable = True
symTabTy = tabTy('SymbolTable', symTy, anyTy)
tyTabTy = tabTy('TypeTable', tyTy, anyTy, True)
################################################################
# pretty printing
def prettyList(xs, seen):
    seen.append(id(xs)); shown = []; repeat = []
    try:
        for x in fromList(xs, None, repeat): shown.append(pretty(x, seen))
        if repeat: shown.append('...')
    except LazyList as ll: shown.append('...%s'%pretty(ll.args[0]))
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
def prettyArray(arr, _=None):
    return '#[%s]'%' '.join(map(pretty, arrToList(arr)))
tagToPretty = {nilTy: prettyList, consTy: prettyList,
               symTy: prettySymbol,
               syncloTy: prettySynClo,
               unitTy: lambda _,__: '()',
               intTy: prettyInt, floatTy: prettyFloat, charTy: prettyChar,
               stringTy: prettyString,
               arrayTy: prettyArray,
               }
def pretty(v, seen=None):
    if seen is None: seen = []
    if id(v) in seen: return '(...)'
    if isTyped(v):
        pp = tagToPretty.get(getTag(v))
        if pp is None:
            if isinstance(getTag(v), ProductType):
                seen.append(id(v)); ty = getTag(v)
                els = ' '.join(pretty(ty.unpackEl(v, idx), seen)
                               for idx in range(ty.numIndices()))
                seen.remove(id(v)); return '(%s)'%('%s %s'%(ty, els)).rstrip()
            elif isinstance(getTag(v), ThunkType): return '(%s)'%str(getTag(v))
            return '<%s %s>'%(getTag(v), getVal(v))
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

from syntax2 import *# todo: syntax is already dependent on this module
for chs, reader in stdDispatchers.bindings().items():
    primNS.defReader(chs, reader)
ubParserTy, parserTy, toParser, fromParser = basicTy('Parser', Parser)
