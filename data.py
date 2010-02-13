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

class TypeError(Exception): pass
def typeErr(ctx, msg): raise TypeError(ctx, msg)

class Named:
    def __init__(self, name): self.name = name
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self.name)
class Tag(Named):
    def contains(self, tag): return self == tag
class PrimTag(Tag): pass
class ArrayTag(PrimTag):
    def __init__(self, elemTag):
        super().__init__('#Array_'+elemTag.name)
        self.elemTag = elemTag
elemToArrayTag = {}
def arrayTag(elemTag):
    tag = elemToArrayTag.get(elemTag)
    if tag is None: tag = ArrayTag(elemTag); elemToArrayTag[elemTag] = tag
    return tag
# class TupleTag(PrimTag):
#     def __init__(self, fieldTags):
#         super().__init__('#Tuple_'+'_'.join(ft.name for ft in fieldTags))
#         self.fieldTags = fieldTags
# fieldsToTupleTag = {}

class NodeTag(Tag):
    def __init__(self, name, fieldTags):
        super().__init__(name)
        self.fieldTags = fieldTags
    def numFields(self):
        if self.fieldTags is None:
            typeErr(None, "attempted to use undefined tag: '%s'"%self.name)
        return len(self.fieldTags)
def nodeTag(name, *ftags): return NodeTag(name, ftags)
# todo: polymorphic param tag
class AnyTag(Tag):
    def contains(self, tag): return True
anyTag = AnyTag('Any')
class UnionTag(Tag):
    def __init__(self, name, subTags): self.name = name; self.subTags = subTags
    def contains(self, tag): return any(t.contains(tag) for t in self.subTags)

def isPrimVal(v):
    return isinstance(v, tuple) and len(v) > 0 and isinstance(v[0], PrimTag)
def packPrimVal(ptag, pv): return (ptag, pv)
def unpackPrimVal(pv): assert isPrimVal(pv), pv; return pv[1]
def primVal_tag(v): assert isPrimVal(v), v; return v[0]

def isNode(v):
    return isinstance(v, list) and len(v) > 0 and isinstance(v[0], NodeTag)
def node(tag, *args): # todo: tag-check args
    assert len(args) == tag.numFields(), (len(args), tag.numFields())
    return [tag]+list(args)
def node_tag(node): assert isNode(node), node; return node[0]
def assertNodeIndex(node, index, tag):
    if tag is not None: assert node_tag(node) is tag, node
    assert index < node_tag(node).numFields(), index
def nodePack(node, index, val, tag=None):
    assertNodeIndex(node, index, tag)
    if isinstance(node.fieldTags[index], PrimTag): val = unpackPrimVal(val)
    node[index] = val
def nodeUnpack(node, index, tag=None):
    assertNodeIndex(node, index, tag)
    val = node[index]
    if isinstance(node.fieldTags[index], PrimTag): val = packPrimVal(val)
    return val

def val_tag(ctx, val):
    if isNode(val): vtag = node_tag(val)
    elif isPrimVal(val): vtag = primVal_tag(val)
    else: typeErr(ctx, "attempted to extract tag from unknown value: '%s'"%val)
def checkIsNodeTag(ctx, tag):
    if not isinstance(tag, NodeTag):
        typeErr(ctx, "expected node tag but found '%s'"%tag)
def checkIsNode(ctx, val):
    if not isNode(val): typeErr(ctx, "expected node but found '%s'"%val)
def checkTagBounds(ctx, tag, index, msg):
    checkIsNodeTag(ctx, tag)
    if index >= tag.numFields():
        typeErr(ctx, (msg+"; tag='%s', num-fields='%d'")%
                (index, tag, tag.numFields()))
def checkTag(ctx, tag, val):
    vtag = val_tag(ctx, val)
    if not tag.contains(vtag):
        typeErr(ctx, "tag error: expected subtag of '%s', found '%s'"%
                (tag, vtag))

def singleton(name):
    tag = nodeTag(name)
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
symTag = nodeTag('Symbol', primSymTag)
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

primEnvTag = PrimTag('#Env')
envTag = nodeTag('Env', primEnvTag)
def toEnv(e): return node(envTag, e)
def fromEnv(e): assert node_tag(e) is envTag, e; return e[1]

################################################################
# syntactic closures
syncloTag = nodeTag('SynClo', envTag, anyTag, anyTag) # todo
def isSynClo(s): return node_tag(s) is syncloTag
def synclo_new(senv, frees, form): return node(syncloTag, senv, frees, form)
def _synclo_get(s, i): assert isSynClo(s), s; return s[i]
def synclo_senv(s): return _synclo_get(s, 1)
def synclo_frees(s): return _synclo_get(s, 2)
def synclo_form(s): return _synclo_get(s, 3)
def applySynCloEnv(senv, sc):
    new = env_data(synclo_senv(sc))
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
nilTag, nil = singleton('Nil')
consTag = nodeTag(':', anyTag, anyTag) # todo
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
primTagTag = PrimTag('#Tag')
tagTag = nodeTag('Tag', primTagTag)
def isTag(v): return node_tag(v) is tagTag
def toTag(v): return node(tagTag, v)
def fromTag(v): assert isTag(v), v; return v[1]
primArrayTag = PrimTag('#Array')
def isArray(v):
    return isPrimVal(v) and isinstance(primVal_tag(v), ArrayTag)
def array_new(elemTag, xs):
    assert isinstance(elemTag, Tag), elemTag
    assert isinstance(xs, list), xs
    return packPrimVal(arrayTag(elemTag), xs)
def array_elemTag(v): assert isArray(v), v; return v[0].elemTag
def array_data(v): assert isArray(v), v; return unpackPrimVal(v)
# def checkArrayBounds(ctx, arr, index, msg):
#     data = primArray_data(arr)
#     if index >= len(data):
#         typeErr(ctx, (msg+"; length='%d'")%(index, len(data)))
#     return data
# def primArray_get(ctx, arr, index): # todo: confirm elemTag?
#     data = checkArrayBounds(ctx, arr, index, "array index out of bounds: '%d'")
#     return data[index]
primIntTag = PrimTag('#Int')
intTag = nodeTag('Int', primIntTag)
def isInt(v): return node_tag(v) is intTag
def toInt(v): return node(intTag, v)
def fromInt(v): assert isInt(v), v; return v[1]
primFloatTag = PrimTag('#Float')
floatTag = nodeTag('Float', primFloatTag)
def isFloat(v): return node_tag(v) is floatTag
def toFloat(v): return node(floatTag, v)
def fromFloat(v): assert isFloat(v), v; return v[1]
primCharTag = PrimTag('#Char')
def toPrimChar(v): return v
def fromPrimChar(v): return v
charTag = nodeTag('Char', primCharTag)
def isChar(v): return node_tag(v) is charTag
def toChar(v): return node(charTag, primChar(v))
def fromChar(v): assert isChar(v), v; return v[1]

################################################################
# strings
def toPrimString(pys):
    assert isinstance(pys, str), pys
    return array_new(primCharTag, [toPrimChar(pych) for pych in pys])
def fromPrimString(v):
    assert array_elemTag(v) is primCharTag, v
    return ''.join(fromPrimChar(ch) for ch in array_data(v))
stringTag = nodeTag('String', arrayTag(primCharTag))
def isString(v): return node_tag(v) is stringTag
def toString(v): return node(stringTag, toPrimString(v))
def fromString(v): assert isString(v), v; return fromPrimString(v[1])

################################################################
# procs
class ProcType: pass
def makeProcType(tag, primTag):
    class Proc(ProcType):
        def __init__(self, name, binders, code, closure):
            self.name = name; self.binders = binders; self.code = code;
            self.closure = closure
    def proc_new(name, binders, code, closure):
        return node(tag, Proc(name, binders, code, closure))
    return proc_new
primProcTag = PrimTag('#Proc')
procTag = nodeTag('Proc', primProcTag)
proc_new = makeProcType(procTag, primProcTag)
def isProc(v): return node_tag(v) is procTag
def fromProc(proc): assert isProc(proc), proc; return proc[1]
def applyProc(appCtx, proc, args):
    binders = proc.binders; ctx = proc.closure.copy(); ctx.env = Env(ctx.env)
    for binder, arg in zip(binders, args):
        ctx.env.add(binder, evalExpr(appCtx, arg)) # todo: check arg tags?
    arity = len(binders)
    if arity <= len(args): return proc.code.eval(ctx), args[arity:]
    else: return proc_new(proc.name, binders[len(args):], proc.code, ctx), ()
primForeignProcTag = PrimTag('#ForeignProc')
foreignProcTag = nodeTag('ForeignProc', primForeignProcTag)
foreignProc_new = makeProcType(foreignProcTag, primForeignProcTag)
def isForeignProc(v): return node_tag(v) is foreignProcTag
def fromForeignProc(fproc):
    assert isForeignProc(fproc), fproc; return fproc[1]
def applyForeignProc(appCtx, fproc, args): # todo: check arg tags?
    arity = len(fproc.binders); code = fproc.code; closure = fproc.closure
    closure += [evalExpr(appCtx, arg) for arg in args[:arity]]
    if arity <= len(args): return code(appCtx, *closure), args[arity:]
    else: return foreignProc_new(fproc.name, arity-len(args), code, closure),()
def applyFull(ctx, proc, args):
    cprc = cont(ctx, proc)
    while args:
        proc = evalExpr(*cprc) # lifted out here for tail-calls
        if isProc(proc): cprc, args = applyProc(ctx, fromProc(proc), args)
        elif isForeignProc(proc):
            cprc, args = applyForeignProc(ctx, fromForeignProc(proc), args)
        else: typeError(ctx, "cannot apply non-procedure: '%s'"%proc)
    return cprc

################################################################
# macros and semantics
macroTag = nodeTag('Macro', procTag)
def isMacro(v): return node_tag(v) is macroTag
def macro_proc(mac): assert isMacro(mac), mac; return mac[1]
def applyMacro(ctx, mac, form):
    return evalExpr(*applyFull(ctx, macro_proc(mac), [form]))
primSemanticTag = PrimTag('#Semantic')
semanticTag = nodeTag('Semantic', primSemanticTag)
def isSemantic(v): return node_tag(v) is semanticTag
def semantic_new(sproc): return node(semanticTag, sproc)
def semantic_proc(sm): assert isSemantic(sm), sm; return sm[1]
def applySemantic(ctx, sem, form): return semantic_proc(sem)(ctx, form)

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

################################################################
# contexts
class Context:
    def __init__(self, root, mod, senv, env, attr, hist=nil):
        self.root = root; self.mod = mod; self.senv = senv; self.env = env
        self.attr = attr; self.hist = hist
    def copy(self):
        return Context(self.root, self.mod, self.senv, self.env, self.hist)
    def histAppend(self, form): self.hist = cons(form, self.hist)
# ctxTag = nodeTag('Context', 2)#4)
# def toCtx(ctx): return node(#toRoot(ctx.root), toMod(ctx.mod),
#                             toEnv(ctx.senv), toEnv(ctx.env))
