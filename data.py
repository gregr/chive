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
# primitives
primitives = {}
def addPrim(name, val):
    sym = symbol(name); den = alias_new(sym); nm = EnvKey(sym)
    assert nm not in primitives, name; primitives[nm] = (den, val)
def primDen(name): return primitives.get(EnvKey(symbol(name)))[0]
ubTagTy = PyType('#Tag', Type)
def addPrimTag(name, tag): addPrim(name, ubTagTy.new(tag))
addPrimTag('Symbol-tag', symTy)
addPrimTag('Any-tag', anyTy)
def prodTy(name, *elts):
    tag = ProductType(name, elts); addPrimTag(name+'-tag', tag); return tag
def node(ty, *args): return ty.new(*args)
def singleton(name):
    ty = prodTy(name); val = ty.new(); addPrim(name, val); return ty, val
unitTy, unit = singleton('Unit')
unitDen = primDen('Unit')
ubEnvTy = PyType('#Env', Env)
envTy = prodTy('Env', ubEnvTy)
def toEnv(e): return node(envTy, ubEnvTy.new(e))
def fromEnv(e): return getVal(envTy.unpackEl(e, 0))

################################################################
# syntactic closures
syncloTy = prodTy('SynClo', envTy, anyTy, anyTy) # todo
def isSynClo(s): return getTy(s) is syncloTy
def synclo_new(senv, frees, form): return syncloTy.new(senv, frees, form)
def synclo_senv(s): return syncloTy.unpackEl(s, 0)
def synclo_frees(s): return syncloTy.unpackEl(s, 1)
def synclo_form(s): return syncloTy.unpackEl(s, 2)
def applySynCloEnv(senv, sc):
    new = fromEnv(synclo_senv(sc))
    frees = fromList(synclo_frees(sc))
    if frees:
        new = Env(new)
        for n in frees:
            n = EnvKey(n)
            v = senv.get(n)
            if v is not None: new.extend(n, v)
    return new
def syncloExpand(senv, xs):
    while isSynClo(xs):
        senv = applySynCloEnv(senv, xs)
        xs = synclo_form(xs)
    return senv, xs

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
# basic values
def basicTy(name, pyty):
    ubTy = PyType('#'+name, pyty); addPrimTag('#'+name, ubTy)
    ty = prodTy(name, ubTy)
#    def isX(v): return node_tag(v) is tag
    def toX(v): return ty.new(ubTy.new(v))
    def fromX(v): return getVal(ty.unpackEl(v, 0))
    return ubTy, ty, toX, fromX
ubIntTy, intTy, toInt, fromInt = basicTy('Int', int)
ubFloatTy, floatTy, toFloat, fromFloat = basicTy('Float', float)
ubCharTy, charTy, toChar, fromChar = basicTy('Char', str)

################################################################
# arrays

################################################################
# strings
#stringTy = prodTy('String', None) # todo
def toString(v): return node(stringTy, v)
#def fromString(v): assert isString(v), v; return v[1]

################################################################
# pretty printing
def prettyList(xs): return '[%s]'%' '.join(pretty(x) for x in fromList(xs))
def prettySymbol(s): return symbol_name(s)
def prettySynClo(s): return ('(SynClo <env> %s %s)'%
                             (#synclo_senv(s),
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
                return '(%s %s)'%(ty, els)
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

################################################################
# contexts
class Context:
    def __init__(self, root, mod, senv, env, attr, hist=nil):
        self.root = root; self.mod = mod; self.senv = senv; self.env = env
        self.attr = attr; self.hist = hist
    def copy(self):
        return Context(self.root, self.mod, self.senv, self.env, self.hist)
    def histAppend(self, form): self.hist = cons(form, self.hist)
# ctxTy = prodTy('Context', 2)#4)
# def toCtx(ctx): return node(#toRoot(ctx.root), toMod(ctx.mod),
#                             toEnv(ctx.senv), toEnv(ctx.env))
def primCtx():
    senv = Env(); env = Env()
    print('adding primitives:')
    for name, (den, val) in primitives.items():
        print(name)
        sym = name.sym; senv.add(EnvKey(sym), den); env.add(EnvKey(den), val)
    return Context(None, None, senv, env, None)
