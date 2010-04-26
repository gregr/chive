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

from data import *

def evalTy(ctx, ty): return type_type(ty.eval(ctx))
def evalTys(ctx, tys): return (evalTy(ctx, ty) for ty in tys)
class ConsTyExpr:
    def preEval(self): return type_new(self.ty)
    def eval(self, ctx): raise NotImplementedError
class ConsTyVar(ConsTyExpr):
    def __init__(self, ctx, name): self.name = EnvKey(getDen(ctx, name))
    def preEval(self): return None
    def eval(self, ctx):
        ty = type_type(ctx.env.get(self.name))
        if ty is None: typeErr(ctx, "unbound type name: '%s'"%self.name)
        return type_new(ty)
class ConsTyProduct(ConsTyExpr):
    def __init__(self, ctx, name, elts, fields):
        assert len(elts) >= len(fields), (elts, fields)
        self.ty = ProductType(name); self.elts = elts; self.fields = fields
    def eval(self, ctx):
        self.ty.init(tuple(evalTys(ctx, self.elts)), self.fields)
        addConsDen(ctx, self.ty.name.sym, self.ty); return type_new(self.ty)
class ConsTyVariant(ConsTyExpr):
    def __init__(self, ctx, elts): self.ty = VariantType(); self.elts = elts
    def eval(self, ctx, fields=None):
        self.ty.init(list(evalTys(ctx, self.elts))); return type_new(self.ty)
class ConsTyProc(ConsTyExpr):
    def __init__(self, ctx, inTy, outTy):
        self.ty = ProcType(); self.inTy = inTy; self.outTy = outTy
    def eval(self, ctx):
        self.ty.init(*list(evalTys(ctx, (self.inTy, self.outTy))))
        return type_new(self.ty)
ubTyConsTy, tyConsTy, toTyCons, fromTyCons = basicTy('TypeCons', object)
def isTyCons(val): return isTyped(val) and getTy(val) is tyConsTy
def getTyCons(ctx, name):
    ty = getVar(ctx, name)
    if isTyCons(ty): return fromTyCons(ty)
    return None
def tycproc(name):
    def handleTyCProc(tycp): addPrim(name, toTyCons(tycp)); return tycp
    return handleTyCProc
@tycproc('#Product')
def tyConsProduct(ctx, body, name):
    if name is None: typeErr(ctx, "product type requires a name: '%s'"%body)
    fields = []
    return ConsTyProduct(ctx, EnvKey(name), tuple(parseType(ctx, form, fields)
                                                  for form in body), fields)
@tycproc('#Variant')
def tyConsVariant(ctx, body, _):
    return ConsTyVariant(ctx, tuple(parseType(ctx, form) for form in body))
@tycproc('#Proc')
def tyConsProc(ctx, body, _):
    if len(body) != 2: typeErr(ctx, "proc type requires two args: '%s'"%body)
    return ConsTyProc(ctx, parseType(ctx, body[0]), parseType(ctx, body[1]))
def parseType(ctx, body, fields=None, name=None):
    ctx, body = syncloExpand(ctx, body)
    if isSymbol(body):
        if fields is not None: fields.append(None)
        return ConsTyVar(ctx, body)
    elif isListCons(body):
        body = tuple(fromList(body, ctx))
        hdCtx, hd = syncloExpand(ctx, body[0])
        if isSymbol(hd):
            tyCons = getTyCons(ctx, hd)
            if tyCons is not None:
                if fields is not None: fields.append(None)
                return tyCons(ctx, body[1:], name)
        if len(body) == 2:
            ty, field = body
            if fields is not None:
                if not isSymbol(field):
                    typeErr(ctx, "invalid field name: '%s'"%pretty(field))
                fields.append(field)
                return parseType(ctx, ty)
    typeErr(ctx, "invalid type constructor: '%s'"%pretty(body))
def bindTypes(ctx, consTyForms):
    exprs = []; aliases = []
    for form in consTyForms:
        if isListCons(form):
            form = tuple(fromList(form, ctx))
            if len(form) == 2:
                name, body = form
                expr = parseType(ctx, body, name=name)
                ty = expr.preEval()
                if ty is None: aliases.append((name, expr))
                else: defTy(ctx, name, ty); exprs.append(expr)
                continue
        typeErr(ctx, "invalid type binder: '%s'"%pretty(form))
    # todo: try sorting aliases topologically, otherwise error
    for name, expr in aliases: defTy(ctx, name, expr.eval(ctx))
    for expr in exprs: expr.eval(ctx)

class ConsArray(Constr): pass

################################################################
class Access(Expr): pass
class NodeAccess(Access):
    def __init__(self, ty, index, node, ctx):
        ty.checkIndex(index, 'node index out of bounds:')
        self.ty = ty; self.index = index; self.node = node
    def _evalNode(self, ctx):
        return evalExpr(ctx, self.node, self.ty)
    def freeVars(self): return self.node.freeVars()
    def subst(self, subs): self.node.subst(subs)
class NodeUnpack(NodeAccess):
    def eval(self, ctx):
        return final(self.ty.unpackEl(self._evalNode(ctx), self.index))
class NodePack(NodeAccess):
    def __init__(self, rhs, *args):
        super().__init__(*args); self.rhs = rhs
    def freeVars(self): return super().freeVars()+self.rhs.freeVars()
    def subst(self, subs): super().subst(subs); self.rhs.subst(subs)
    def eval(self, ctx):
        self.ty.packEl(self._evalNode(ctx), self.index,
                       evalExpr(ctx, self.rhs))
        return final(unit)
# todo: array access

################################################################
class Seq(Expr):
    def __init__(self, exprs): self.exprs = exprs[:-1]; self.last = exprs[-1]
    def eval(self, ctx):
        for expr in self.exprs: evalExpr(ctx, expr)
        return cont(ctx, self.last)
class Apply(Expr):
    def __init__(self, proc, args): self.proc = proc; self.args = args
    def freeVars(self): return accFreeVars(self.args)
    def subst(self, subs): mapSubst(subs, self.args)
    def eval(self, ctx): return applyFull(ctx, self.proc, self.args)
# todo: extensible dispatch-proc?
class Switch(Expr): 
    def __init__(self, discrim, default, alts):
        self.discrim = discrim; self.default = default; self.alts = alts
        # todo: if default is None, default = expr to raise a type error
    def _children(self):
        return [body for _,body in self.alts]+[self.default, self.discrim]
    def freeVars(self): return accFreeVars(self._children())
    def subst(self, subs): mapSubst(subs, self._children())
    def eval(self, ctx):
        discrim = getDiscrim(evalExpr(ctx, self.discrim))
        body = self.alts.get(discrim)
        if body is None: body = self.default
        return cont(ctx, body)
class Let(Expr):
    def __init__(self, nonrec, rec, body):
        self.nonrec = nonrec; self.rec = rec # run-time bindings
        self.body = body
    def eval(self, ctx):
        newCtx = ctx.extendValues()
        for name, rhs in self.nonrec: newCtx.env.add(name, evalExpr(ctx, rhs))
        for name, rhs in self.rec: newCtx.env.add(name, evalExpr(newCtx, rhs))
        return cont(newCtx, self.body)
################################################################
class Unwind(Expr):
    def eval(self, ctx): raise UnwindExc
class CatchUnwind(Expr):
    def __init__(self, cnsq, altrn): self.cnsq = cnsq; self.altrn = altrn
    def eval(self, ctx):
        try: return final(evalExpr(ctx, self.cnsq))
        except UnwindExc: return cont(ctx, self.altrn)
