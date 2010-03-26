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

def final(val): return None, val
def cont(ctx, expr): return ctx, expr
def evalExpr(ctx, expr, ty=None): # tail-call trampoline
    while ctx is not None: ctx, expr = expr.eval(ctx)
    if ty is not None: ty.checkTy(expr)
    return expr # when ctx is None, expr will be a final value
class Expr:
    def pretty(self): return 'todo'

################################################################
class Atom(Expr): pass
class PrimVal(Atom):
    def __init__(self, val): self.val = val
    def eval(self, ctx): return final(self.val)
class Var(Atom):
    def __init__(self, name): self.name = name
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
    def __init__(self, p=None):
        self.p = p
        self.bs = {}
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
        if isinstance(body, ConsProc): # combine adjacently-nested ConsProcs
            binders += body.proc.binders; body = body.proc.code
        self.proc = NativeProc(name, body, binders)
        self.ty = currySpecificProcType(name, paramts, rett)
    def eval(self, ctx): return final(proc_new(self.proc, ctx, self.ty))
class ConsNode(Constr):
    def __init__(self, ty, cargs, ctx=None):
        if not isinstance(ty, ProductType):
            typeErr(ctx, "invalid product type: '%s'"%ty)
        ty.checkIndex(len(cargs),
                      'incorrect number of constructor arguments:', True)
        self.ty = ty; self.cargs = cargs
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
ubTagTy = PyType('#Tag', Type)
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
nilTy, nil = singleton('Nil')
consTy = prodTy(':', anyTy, anyTy) # todo
def cons(h, t): return consTy.new(h, t)
def cons_head(x): return consTy.unpackEl(x, 0)
def cons_tail(x): return consTy.unpackEl(x, 1)
def isListCons(x): return getTy(x) is consTy
def isList(x): return x is nil or isListCons(x)
def toList(args, tail=nil):
    for x in reversed(args): tail = cons(x, tail)
    return tail
def fromList(xs):
    assert isList(xs), xs
    while xs is not nil:
        yield cons_head(xs)
        xs = cons_tail(xs)

################################################################
# contexts
class Context:
    def __init__(self, root, mod, tenv, senv, env, attr, hist=nil):
        self.root = root; self.mod = mod
        self.tenv = tenv; self.senv = senv; self.env = env
        self.attr = attr; self.hist = hist
    def __eq__(self, rhs):
        return self.tenv is rhs.tenv and self.senv is rhs.senv
    def copy(self):
        return Context(self.root, self.mod, self.tenv, self.senv, self.env,
                       self.attr, self.hist)
    def histAppend(self, form): self.hist = cons(form, self.hist)
ubCtxTy, ctxTy, toCtx, fromCtx = basicTy('Ctx', Context)

def primCtx():
    tenv = Env(); senv = Env(); env = Env()
    ctx = Context(None, None, tenv, senv, env, None)
    print('adding primitive types:')
    for name, (den, ty) in primTypes.items():
        print(name); tenv.add(name, den); env.add(EnvKey(den), ty)
        if isinstance(ty, ProductType) and ty.elts:
            addPrim(symbol_name(name.sym), constr_new(ctx, ty))
    print('adding primitive values:')
    for name, (den, val) in primitives.items():
        print(name); senv.add(name, den); env.add(EnvKey(den), val)
    return ctx

################################################################
# syntactic closures
syncloTy = prodTy('SynClo', ctxTy, anyTy, anyTy) # todo
def isSynClo(s): return getTy(s) is syncloTy
def synclo_new(ctx, frees, form): return syncloTy.new(ctx, frees, form)
def synclo_ctx(s): return syncloTy.unpackEl(s, 0)
def synclo_frees(s): return syncloTy.unpackEl(s, 1)
def synclo_form(s): return syncloTy.unpackEl(s, 2)
def applySynCloCtx(ctx, sc):
    scCtx = fromCtx(synclo_ctx(sc)); senv = scCtx.senv
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
macroTy = prodTy('Macro', curryProcType((anyTy, anyTy), anyTy))
def isMacro(v): return isTyped(v) and getTy(v) is macroTy
def macro_proc(mac): return macroTy.unpackEl(mac, 0)
def applyMacro(ctx, mac, form):
    return evalExpr(*applyFull(ctx, macro_proc(mac), [toCtx(ctx), form]))
ubSemanticTy, semanticTy, toSem, fromSem = basicTy('Semantic', object)
def isSemantic(v): return isTyped(v) and getTy(v) is semanticTy
def applySemantic(ctx, sem, form): return fromSem(sem)(ctx, form)

################################################################
# pretty printing
def prettyList(xs): return '[%s]'%' '.join(pretty(x) for x in fromList(xs))
def prettySymbol(s): return symbol_name(s)
def prettySynClo(s): return ('(SynClo <ctx> %s %s)'%
                             (#synclo_senv(s), # todo: string rep
                              prettyList(synclo_frees(s)),
                              pretty(synclo_form(s))))
def prettyInt(i): return repr(fromInt(i))
def prettyFloat(f): return repr(fromFloat(f))
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
def prettyChar(c): return "'%s'"%''.join(escaped(c, "'") for c in fromChar(c))
def prettyString(s):
    return '"%s"'%''.join(escaped(c, '"') for c in fromString(s))
tagToPretty = {nilTy: prettyList, consTy: prettyList,
               symTy: prettySymbol,
               syncloTy: prettySynClo,
               unitTy: lambda _: '()',
               intTy: prettyInt, floatTy: prettyFloat, charTy: prettyChar,
               #stringTy: prettyString,
               }
def pretty(v):
    if isTyped(v):
#        if isProc(v): return '<(%s) %s>'%(getTy(v), getVal(v))
        pp = tagToPretty.get(getTy(v))
        if pp is None:
            if isinstance(getTy(v), ProductType):
                ty = getTy(v)
                els = ' '.join(pretty(ty.unpackEl(v, idx))
                               for idx in range(ty.numIndices()))
                return '(%s)'%('%s %s'%(ty, els)).rstrip()
            return '<%s %s>'%(getTy(v), getVal(v))
        else: return pp(v)
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
