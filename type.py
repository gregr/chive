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

from storage import *

class TypeError(Exception): pass
def typeErr(ctx, msg): raise TypeError(ctx, msg)
def isTyped(val): return (isinstance(val, tuple) and len(val)>0 and
                          isinstance(getTy(val), Type))
def typed(ty, val): return (ty, val)
def getTy(val): return val[0]
def getVal(val): return val[1]
class Type:
    def contains(self, ty, tenv=None): return self is ty
    def checkTy(self, val):
        if not self.contains(getTy(val)):
            typeErr(None, "expected '%s', given '%s'"%
                    (self.desc(), getTy(val).desc()))
    def checkIndex(self, idx, msg, exact=False):
        ni = self.numIndices()
        if ni is None and not exact: return
        if (exact and (idx != ni)) or idx<0 or idx>self.numIndices():
            typeErr(None, msg+" '%d'; %s has %d elements"%
                    (idx, self.desc(), ni))
    def size(self): raise NotImplementedError
    def numIndices(self): return 0
    def index(self, idx): raise NotImplementedError
    def unpack(self, mem, offset): raise NotImplementedError
    def pack(self, mem, offset, val): raise NotImplementedError
    def unpackEl(self, agg, idx):
        self.checkTy(agg); elt, off = self.index(idx)
        return elt.unpack(getVal(agg), off)
    def packEl(self, agg, idx, val):
        self.checkTy(agg); elt, off = self.index(idx);
        elt.pack(getVal(agg), off, val)
    def desc(self): raise NotImplementedError
    def __str__(self): return self.desc()
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self.desc())
################################################################
# unboxed types
class UnboxedType(Type):
    def unpack(self, mem, offs): return typed(self, self._unpack(mem, offs))
    def _unpack(self, mem, offs): raise NotImplementedError
    def pack(self, mem, offs, val):
        self.checkTy(val); self._pack(mem, offs, getVal(val))
    def _pack(self, mem, offset, val): raise NotImplementedError
class AtomicUnboxedType(UnboxedType):
    def size(self): return 1 # fixed size due to python
    def _unpack(self, mem, offset): return mem_read(mem, offset)
    def _pack(self, mem, offset, val): mem_write(mem, offset, val)
class ScalarType(AtomicUnboxedType):
    def __init__(self, name, pred=None): self.name = name; self.pred = pred
    def new(self, val):
        if self.pred is not None and not self.pred(val):
            typeErr(None, "invalid scalar '%r'"%val)
        return typed(self, val)
    def desc(self): return str(self.name)
class PyType(ScalarType):
    def __init__(self, name, pyty):
        super().__init__(name, (lambda x: isinstance(x, pyty)))
def cachedType(cls):
    cls._cache = {}
    def makeType(*args):
        ty = cls._cache.get(args)
        if ty is None: ty = cls(*args); cls._cache[args] = ty
        return ty
    return makeType
class PtrType(AtomicUnboxedType):
    def __init__(self, elt): self.elt = elt
    def contains(self, ty, tenv=None):
        return type(ty) is type(self) and self.elt.contains(ty.elt, tenv)
    def desc(self): return '&%s'%self.elt
ptrType = cachedType(PtrType)
class AggUnboxedType(UnboxedType):
    def _unpack(self, mem, offset): return mem_offset(mem, offset)
    def _pack(self, mem, offset, val):
        mem_copy(mem_offset(mem, offset), val, self.size())
class ArrayType(AggUnboxedType):
    def __init__(self, elt, cnt=None): self.elt = elt; self.cnt = cnt
    def contains(self, ty, tenv=None):
        return (type(ty) is type(self) and self.elt.contains(ty.elt, tenv)
                and (ty.cnt == self.cnt or
                    (ty.cnt is not None and ty.cnt > self.cnt)))
    def size(self):
        if self.cnt is not None: return self.cnt*self.elt.size()
        else: return None
    def numIndices(self): return self.cnt
    def index(self, idx): # None-length array implies dynamic extent
        assert self.cnt is None or idx>=0 and idx<self.cnt, (idx, self.desc())
        return self.elt, idx*self.elt.size()
    def desc(self):
        if self.cnt is None: pref = '';
        else: pref = '%d * '%self.cnt
        return '#[%s]'%(pref+self.elt.desc())
arrayType = cachedType(ArrayType)
def struct_index(struct, idx):
    struct.checkIndex(idx, 'invalid index')
    return struct.elts[idx], sum(elt.size() for elt in struct.elts[:idx])
class StructType(AggUnboxedType):
    def __init__(self, elts): self.elts = elts
    def contains(self, ty, tenv=None):
        return (type(ty) is type(self) and
                all(t1.contains(t2, tenv)
                    for t1, t2 in zip(self.elts, ty.elts)))
    def size(self): return sum(elt.size() for elt in self.elts())
    def numIndices(self): return len(self.elts)
    def index(self, idx): return struct_index(self, idx)
    def desc(self): return '#{%s}'%' '.join(lyt.desc() for lyt in self.ellyts)
structType = cachedType(StructType)
################################################################
# boxed types
class BoxedType(Type):
    def size(self): return 1
    def unpack(self, mem, offset):
        box = mem_read(mem, offset); self.checkTy(box); return box
    def pack(self, mem, offset, box):
        self.checkTy(box); mem_write(mem, offset, box)
class AnyType(BoxedType):
    def contains(self, ty, tenv=None): return isinstance(ty, BoxedType)
    def desc(self): return 'Any'
anyTy = AnyType()
class NodeType(BoxedType):
    def __init__(self, name, elts):
        self.name = name; self.elts = elts;
        if elts is not None: self.eltSize = sum(elt.size() for elt in elts)
    def contains(self, ty, tenv=None):
        if isinstance(ty, RefinedType):
            return (ty.elt is self and
                    all(elt.contains(arg, tenv)
                        for elt, arg in zip(self.elts, ty.args)))
        return ty is self
    def checkValid(self):
        if self.elts is None:
            typeErr(None, "attempted to use undefined tag: '%s'"%self.name)
    def numIndices(self): self.checkValid(); return len(self.elts)
    def index(self, idx): self.checkValid(); return struct_index(self, idx)
    def new(self, *args):
        self.checkIndex(len(args), 'invalid number of constructor args', True)
        mem = mem_alloc(self.eltSize)
        offset = 0
        for elt, arg in zip(self.elts, args):
            elt.pack(mem, offset, arg); offset += elt.size()
        return typed(self, mem)
    def desc(self): return str(self.name)
    def refine(self, args):
        assert len(args) == len(self.elts)
        for arg, elt in zip(args, self.elts):
            if arg is None: arg = elt
            elif not elt.contains(arg):
                typeErr(None, 'cannot refine node type')
        return RefinedType(self, args)
def isNode(v): return isTyped(v) and anyTy.contains(getTy(v))
class ProcType(BoxedType):
    def __init__(self, inTy, outTy): self.inTy = inTy; self.outTy = outTy
    def contains(self, ty, tenv=None):
        return (isProc(ty) and self.inTy.contains(ty.inTy, tenv) and
                self.outTy.contains(ty.outTy, tenv))
    def new(self, proc): return typed(self, proc)
    def appliedTy(self, remainingApps):
        ty = self; argts = []
        while remainingApps != 0:
            if not isinstance(ty, ProcType): break
            argts.append(ty.inTy); ty = ty.outTy; remainingApps -= 1
        return ty, argts, remainingApps
    def desc(self): return '%s -> %s'%(self.inTy.desc(), self.outTy.desc())
    def refine(self, rIn, rOut):
        rpt = procType(rIn, rOut)
        if self.contains(rpt): return rpt
        typeErr(None, 'cannot refine proc type')
def isProc(v): return isTyped(v) and isinstance(getTy(v), ProcType)
procType = cachedType(ProcType)
def curryProcType(paramts, rett):
    for paramt in paramts: rett = procType(paramt, rett)
    return rett
class UnionType(BoxedType): # todo: refinement produces union of refinements
    def __init__(self, elts): self.elts = elts
    def contains(self, ty, tenv=None):
        return ((isinstance(ty, UnionType) and
                 all(self.contains(elt, tenv) for elt in ty.elts))
                 or any(elt.contains(ty, tenv) for elt in self.elts))
    def desc(self): return '(%s)'%'|'.join(elt.desc() for elt in self.elts)
def intersectCns(cns, ty, tenv):
    if cns[0].contains(ty, tenv): cns[0] = ty; return True # todo: reduce ty
    return False
class ParamVarType(BoxedType): # only makes sense within parametric context
    def __init__(self, name): self.name = name
    def contains(self, ty, tenv=None):
        assert tenv is not None; constraint = tenv.get(self.name)
        return intersectCns(constraint, ty, tenv)
    def desc(self): return str(self.name)
class ConstraintType(BoxedType):
    def __init__(self, name, constraint=anyTy):
        self.name = name; self.constraint = constraint
    def contains(self, ty, tenv=None):
        return self.constraint.contains(ty, tenv)
    def desc(self): return '%s<:%s'%(str(self.name), self.constraint)
class ParametricType(BoxedType):
    def __init__(self, name, constraints, elt):
        self.name = name; self.constraints = constraints; self.elt = elt
    def contains(self, ty, tenv=None): # todo
        if isinstance(ty, ParametricType): return ty is self
        elif isinstance(ty, RefinedType):
            if isinstance(ty, ParametricType):
                return (ty.elt is self and
                        all(cns.contains(arg, tenv)
                            for cns, arg in zip(self.constraints, ty.args)))
        assert tenv is not None; tenv = Env(tenv)
        for cns in self.constraints: tenv.add(cns.name, [cns.constraint])
        return self.elt.contains(ty, tenv)
    def desc(self):
        return '(%s => %s)'%(' '.join([str(self.name), ' '.join(self.params)]), self.elt.desc())
class RefinedType(BoxedType):
    def __init__(self, elt, args): self.elt = elt; self.args = args
    def contains(self, ty, tenv):
        if isinstance(ty, RefinedType):
            return (self.elt is ty.elt and
                    all(arg.contains(targ, tenv)
                        for arg, targ in zip(self.args, ty.args)))
        elif isinstance(self.elt, ParametricType):
            assert tenv is not None; tenv = Env(tenv)
            for cns, arg in zip(self.elt.constraints, self.args):
                tenv.add(cns.name, [arg])
            return self.elt.elt.contains(ty, tenv)
        return False
    def desc(self):
        return '(%s)'%' '.join([self.elt.desc(), ' '.join(self.args)])
