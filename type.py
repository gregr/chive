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
def getDiscrim(val): return getTy(val).discrim(val)
class Type:
    def contains(self, ty, tenv=None): return self is ty
    def checkTy(self, val):
        if not self.contains(getTy(val)):
            typeErr(None, "expected '%s', given '%s'"%
                    (self, getTy(val)))
    def checkIndex(self, idx, msg, exact=False):
        ni = self.numIndices()
        if ni is None and not exact: return
        if (exact and (idx != ni)) or idx<0 or idx>self.numIndices():
            typeErr(None, msg+" '%d'; %s has %d elements"% (idx, self, ni))
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
    def discrim(self, val): raise NotImplementedError
    def __str__(self): raise NotImplementedError
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self)
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
    def __init__(self, name, pred=lambda _: True):
        self.name = name; self.pred = pred
    def new(self, val):
        if not self.pred(val): typeErr(None, "invalid scalar '%r'"%val)
        return typed(self, val)
    def discrim(self, val): return getVal(val)
    def __str__(self): return str(self.name)
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
    def __str__(self): return '&%s'%self.elt
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
        assert self.cnt is None or idx>=0 and idx<self.cnt, (idx, self)
        return self.elt, idx*self.elt.size()
    def __str__(self):
        if self.cnt is None: pref = '';
        else: pref = '%d * '%self.cnt
        return '#[%s]'%(pref+self.elt)
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
    def __str__(self): return '#{%s}'%' '.join(elt for elt in self.elts)
structType = cachedType(StructType)
################################################################
# boxed types (runtime tagging without parametric polymorphism for now)
class BoxedType(Type):
    def size(self): return 1
    def unpack(self, mem, offset):
        box = mem_read(mem, offset); self.checkTy(box); return box
    def pack(self, mem, offset, box):
        self.checkTy(box); mem_write(mem, offset, box)
class AnyType(BoxedType):
    def contains(self, ty, tenv=None): return isinstance(ty, BoxedType)
    def __str__(self): return 'Any'
anyTy = AnyType()
class VariantType(BoxedType):
    def __init__(self, elts=None):
        if elts is not None: self.init(elts)
    def init(self, elts):
        assert all(isinstance(elt, NodeType) for elt in elts), elts
        self.elts = elts
    def __str__(self): return '(%s)'%'|'.join(str(elt) for elt in self.elts)
    def contains(self, ty, tenv=None):
        if isinstance(ty, VariantType):
            return all(self.contains(rhs, tenv) for rhs in ty.elts)
        else: return any(elt.contains(ty) for elt in self.elts)
class NodeType(BoxedType):
    def discrim(self, val): return getTy(val)
class ProductType(NodeType):
    def __init__(self, name, elts=None, fields=()):
        self.name = name
        if elts is not None: return self.init(elts, fields)
        self.elts = None; self.fields = {}
    def init(self, elts, fields=()):
        self.elts = elts; self.eltSize = sum(elt.size() for elt in elts)
        assert len(fields) <= len(elts), (fields, elts)
        for idx, fname in enumerate(fields):
            if fname is None: continue
            if fname in self.fields:
                typeErr(None, "type '%s' has duplicate field name: '%s'"
                              %(self.name, fname))
            self.fields[fname] = idx
    def contains(self, ty, tenv=None): return ty is self
    def checkValid(self):
        if self.elts is None:
            typeErr(None, "attempted to use undefined tag: '%s'"%self.name)
    def numIndices(self): self.checkValid(); return len(self.elts)
    def index(self, idx): self.checkValid(); return struct_index(self, idx)
    def fieldIndex(self, fname): return self.fields.get(fname)
    def new(self, *args):
        self.checkIndex(len(args), 'invalid number of constructor args', True)
        mem = mem_alloc(self.eltSize)
        offset = 0
        for elt, arg in zip(self.elts, args):
            elt.pack(mem, offset, arg); offset += elt.size()
        return typed(self, mem)
    def __str__(self): return str(self.name)
class ProcType(NodeType):
    def __init__(self, inTy=None, outTy=None):
        if outTy is not None: self.init(inTy, outTy)
    def init(self, inTy, outTy): self.inTy = inTy; self.outTy = outTy
    def contains(self, ty, tenv=None):
        return (isProc(ty) and ty.inTy.contains(self.inTy, tenv) and
                self.outTy.contains(ty.outTy, tenv))
    def appliedTy(self, remainingApps, arity):
        ty = self; argts = []
        while remainingApps != 0 and arity != 0:
            assert isinstance(ty, ProcType), ty
            argts.append(ty.inTy); ty = ty.outTy; remainingApps-=1; arity-=1
        return ty, argts, arity
    def __str__(self): return '(%s -> %s)'%(self.inTy, self.outTy)
def isProc(v): return isTyped(v) and isinstance(getTy(v), ProcType)
procType = cachedType(ProcType)
def curryProcType(paramts, rett, constr=procType):
    for paramt in reversed(paramts): rett = constr(paramt, rett)
    return rett
class SpecificProcType(ProcType):
    def __init__(self, name, *args): super().__init__(*args); self.name = name
    def contains(self, ty, tenv=None): return self is ty
    def new(self, proc): return typed(self, proc)
    def __str__(self): return ('%s::%s')%(str(self.name), super().__str__())
def currySpecificProcType(name, paramts, rett):
    return curryProcType(paramts, rett,
                         (lambda *args: SpecificProcType(name, *args)))
