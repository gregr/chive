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

################################################################
# types
class Type:
    def contains(self, ty, tenv=None): return self is ty
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self)

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
################################################################
# interpreter
class Env:
    def __init__(self, dat=None):
        if dat is None: dat = {}
        self.data = dat
    def __eq__(self, env): return self.data == env.data
    def __hash__(self): return hash(self.data)
    def __str__(self): return strDict(self.data)
    def __repr__(self): return '<Env %s>'%str(self)
    def get(self, key):
        val = self.data.get(key)
        if val is None: return set()
        return val
    def insert(self, kvs):
        dat = self.data.copy()
        dat.update((key, self.get(key)|val) for (key, val) in kvs)
        return Env(dat)
    def contains(self, env):
        return all(self.get(key).issuperset(val)
                   for (key,val) in env.data.items())
    def join(self, env): return self.insert(env.data.items())
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
    def __repr__(self): return '<m=%d %s>'%(self.mx, str(self))
    def advance(self, code):
        codes = (self.codes+(code,)); codes = codes[max(0,len(codes)-self.mx):]
        return AbstractTime(codes, self.mx)

def namedTup(*args): ntup = namedtuple(*args); ntup.__str__=strTup; return ntup
Closure = namedTup('Closure', 'proc time')
Binding = namedTup('Binding', 'name time')
Context = namedTup('Context', 'code time')
def advance(ctx): return ctx.time.advance(ctx.code)
class Config:
    def __init__(self, store): self.store = store
    def __str__(self): return str(self.store)
    def __repr__(self): return '<Config %s>'%str(self)
    def contains(self, cfg): return self.store.contains(cfg.store)
    def join(self, cfg): return Config(self.store.join(cfg.store))
class State:
    def __init__(self, ctx, cfg): self.ctx = ctx; self.cfg = cfg
    def next(self): return self.ctx.code.eval(self.ctx.time, self.cfg)

class Expr:
    def __init__(self): self.lab = Label()
    def __str__(self): raise NotImplementedError
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, str(self))
    def frees(self): raise NotImplementedError
def accFrees(xs): return reduce(set.union,(x.frees() for x in xs),set())

class CExpr(Expr):
    def eval(self, tm, cfg): raise NotImplementedError
class Halt(CExpr):
    def __str__(self): return '*HALT!*'
    def frees(self): return set()
    def eval(self, tm, cfg): return ()
class Call(CExpr):
    def __init__(self, proc, params):
        super().__init__(); self.proc = proc; self.params = params
    def __str__(self):
        return '(call %s %s)'%(str(self.proc), strTup(self.params))
    def frees(self): return self.proc.frees()|accFrees(self.params)
    def eval(self, tm, cfg):
        clos = self.proc.eval(tm, cfg)
        paramss = tuple(pm.eval(tm, cfg) for pm in self.params)
        nexts = []
        for (proc, ptm) in clos:
            ntm = proc.advance(Context(self, tm), ptm)
            nexts.append(applyProc(proc, paramss, ptm, ntm, cfg))
        return nexts
def applyProc(proc, paramss, ptm, ntm, cfg):
    bvs = zip((Binding(bv, ntm) for bv in proc.binders), paramss)
    fvs = ((Binding(fv, ntm), cfg.store.get(Binding(fv, ptm)))
           for fv in proc.frees())
    ncfg = Config(cfg.store.insert(chain(bvs, fvs)))
    return State(Context(proc.code, ntm), ncfg)

class VExpr(Expr):
    def eval(self, tm, cfg): raise NotImplementedError
class Var(VExpr):
    def __init__(self, name): super().__init__(); self.name = name
    def __str__(self): return str(self.name)
    def frees(self): return {self.name}
    def eval(self, tm, cfg): return cfg.store.get(Binding(self.name, tm))
class Proc(VExpr):
    def __init__(self, binders, code):
        super().__init__(); self.binders = binders; self.code = code
    def __str__(self):
        return '(%s %s %s)'%(self.strTag, strTup(self.binders), str(self.code))
    def frees(self): return self.code.frees()-set(self.binders)
    def eval(self, tm, cfg): return {Closure(self, tm)}
class UProc(Proc):
    strTag = 'uproc'
    def advance(self, ctx, tm): return advance(ctx)
class CProc(Proc):
    strTag = 'cproc'
    def advance(self, ctx, tm): return tm
finalResult = Name('final-result')
halt = CProc((finalResult,), Halt())
def progState(proc, params, tm):
    cfg = Config(Env())
    return applyProc(proc, params+(halt.eval(tm, cfg),), tm, tm, cfg)

def freshCVar(alpha=alphaGen(['k'])): return Var(Name(next(alpha)))
def freshUVar(alpha=alphaGen(['u'])): return Var(Name(next(alpha)))
class DExpr(Expr):
    def toCPS(self, ce): raise NotImplementedError
class DVar(DExpr):
    def __init__(self, name): super().__init__(); self.name = name
    def __str__(self): return str(self.name)
    def toCPS(self, ce): return Call(ce, (Var(self.name),))
class DProc(DExpr):
    def __init__(self, binders, body):
        super().__init__(); self.binders = binders; self.body = body
    def __str__(self):
        return '(dproc %s %s)'%(strTup(self.binders), str(self.body))
    def toCPS(self, ce):
        cv = freshCVar()
        return Call(ce, (UProc(self.binders+(cv.name,), self.body.toCPS(cv)),))
class DApply(DExpr):
    def __init__(self, proc, params):
        super().__init__(); self.proc = proc; self.params = params
    def __str__(self): return '(%s %s)'%(str(self.proc), strTup(self.params))
    def toCPS(self, ce):
        uvp = freshUVar(); uvs = tuple(freshUVar() for _ in self.params)
        call = Call(uvp, uvs+(ce,))
        for uv, param in reversed(tuple(zip(uvs, self.params))):
            call = param.toCPS(CProc((uv.name,), call))
        return self.proc.toCPS(CProc((uvp.name,), call))
def dLetStar(bnds, body):
    for (binder, de) in reversed(bnds):
        body = DApply(DProc((binder,), body), (de,))
    return body
def dProg(dexpr):
    haltBnd = Name('halt'); return UProc((haltBnd,), dexpr.toCPS(Var(haltBnd)))

def garbageCollect(state): return state
def search(seen, todo):
    while todo:
        state = garbageCollect(todo.pop())
        cfg = seen.get(state.ctx)
        if cfg is not None:
            if cfg.contains(state.cfg): continue
            cfg = cfg.join(state.cfg)
            state = garbageCollect(State(state.ctx, cfg))
        else: cfg = state.cfg
        seen[state.ctx] = cfg; todo.extend(state.next())
    return seen
def searchProg(proc, mx=0):
    return search({}, [progState(proc, (), AbstractTime((), mx))])
def summary(seen): return reduce(Config.join, seen.values(), Config(Env()))
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
print(strDict(testSum.store.data, '\n'))