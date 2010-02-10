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

class Named:
    def __init__(self, name): self.name = name
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self.name)

class Tag(Named): pass
class PrimTag(Tag): pass
class NodeTag(Tag):
    def __init__(self, name, fieldTypes):
        super().__init__(name)
        self.fieldTypes = fieldTypes
    def numFields(self): return len(self.fieldTypes)

def isNode(v):
    return isinstance(v, list) and len(v) > 0 and isinstance(v[0], NodeTag)
def node(tag, *args):
    assert len(args) == tag.numFields(), (len(args), tag.numFields())
    return [tag]+list(args)
def node_tag(node): assert isNode(node), node; return node[0]

def nodeTagN(name, nargs): return NodeTag(name, (None,)*nargs)
def singleton(name):
    tag = nodeTagN(name, 0)
    return tag, node(tag)
unitTag, unit = singleton('Unit')

################################################################
# symbols
primSymTag = PrimTag('#Symbol')
nextSymId = 0
def primSymbol_new(n):
    global nextSymId
    assert type(n) is str, n
    sd = (n, nextSymId)
    nextSymId += 1
    return sd
symTag = nodeTagN('Symbol', 1)
def isSymbol(v): return node_tag(v) is symTag
def symbol_new(n): return node(symTag, primSymbol_new(n))
def symbol_prim(s): assert isSymbol(s), v; return s[1]
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
def toAlias(sym): return symbol_new(symbol_name(sym))
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

envTag = nodeTagN('Env', 1)
def toEnv(e): return node(envTag, e)
def fromEnv(e): assert node_tag(e) is envTag, e; return e[1]

################################################################
# syntactic closures
syncloTag = nodeTagN('SynClo', 3)
def isSynClo(s): return node_tag(s) is syncloTag
def synclo_new(senv, frees, form): return node(syncloTag, senv, frees, form)
def _synclo_get(s, i): assert isSynClo(s), s; return s[i]
def synclo_senv(s): return _synclo_get(s, 1)
def synclo_frees(s): return _synclo_get(s, 2)
def synclo_form(s): return _synclo_get(s, 3)

################################################################
# lists
nilTag, nil = singleton('Nil')
consTag = nodeTagN(':', 2)
def cons(h, t): return node(consTag, h, t)
def cons_head(x): assert node_tag(x) is consTag, x; return x[1]
def cons_tail(x): assert node_tag(x) is consTag, x; return x[2]
def isListCons(x): return node_tag(x) is consTag
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
# primitive values
primAddrTag = PrimTag('#Addr') # only explicitly needed for array elemTags
primArrayTag = PrimTag('#Array')
def isPrimArray(v):
    return isinstance(v, tuple) and len(v)>0 and v[0] is primArrayTag
def primArray_new(elemTag, xs): # tag determines size of each element
    assert isinstance(elemTag, Tag), elemTag
    assert isinstance(xs, list), xs
    return (primArrayTag, elemTag, xs) # only adding primTag for debugging
def primArray_tag(v): assert isPrimArray(v), v; return v[1]
def primArray_data(v): assert isPrimArray(v), v; return v[2]
primIntTag = PrimTag('#Int')
intTag = nodeTagN('Int', 1)
def isInt(v): return node_tag(v) is intTag
def toInt(v): return node(intTag, v)
def fromInt(v): assert isInt(v), v; return v[1]
primFloatTag = PrimTag('#Float')
floatTag = nodeTagN('Float', 1)
def isFloat(v): return node_tag(v) is floatTag
def toFloat(v): return node(floatTag, v)
def fromFloat(v): assert isFloat(v), v; return v[1]
primCharTag = PrimTag('#Char')
def toPrimChar(v): return v
def fromPrimChar(v): return v
charTag = nodeTagN('Char', 1)
def isChar(v): return node_tag(v) is charTag
def toChar(v): return node(charTag, primChar(v))
def fromChar(v): assert isChar(v), v; return v[1]

################################################################
# strings
def toPrimString(pys):
    assert isinstance(pys, str), pys
    return primArray_new(primCharTag, [toPrimChar(pych) for pych in pys])
def fromPrimString(v):
    assert primArray_tag(v) is primCharTag, v
    return ''.join(fromPrimChar(ch) for ch in primArray_data(v))
stringTag = nodeTagN('String', 1)
def isString(v): return node_tag(v) is stringTag
def toString(v): return node(stringTag, toPrimString(v))
def fromString(v): assert isString(v), v; return v[1]

################################################################
# pretty printing
def prettyList(xs): return '[%s]'%' '.join(pretty(x) for x in fromList(xs))
def prettySymbol(s): return symbol_name(s)
def prettySynClo(s): return ('(SynClo <env> %s %s)'%
                             (#synclo_senv(s),
                              prettyList(synclo_frees(s)),
                              pretty(synclo_form(s))))
#def prettyArray(a): '#[%s]'%' '.join(pretty(x) for x in array_data(a))
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
tagToPretty = {nilTag: prettyList, consTag: prettyList,
               symTag: prettySymbol,
               syncloTag: prettySynClo,
               unitTag: lambda _: '()',
#               arrayTag: prettyArray,
               intTag: prettyInt, floatTag: prettyFloat, charTag: prettyChar,
               stringTag: prettyString,
               }
def pretty(v):
    if isNode(v): pp = tagToPretty.get(node_tag(v))
    else: pp = None
    if pp is None: return '<ugly %s>'%repr(v)
    return pp(v)

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
