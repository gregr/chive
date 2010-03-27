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

class ConsTyExpr:
    def preEval(self): return self.ty
    def eval(self, ctx): raise NotImplementedError
class ConsTyVar(ConsTyExpr):
    def __init__(self, ctx, name):
        self.name = EnvKey(getDen(ctx.tenv, name))
    def preEval(self): return None
    def eval(self, ctx):
        ty = ctx.env.get(self.name)
        if ty is None: typeErr(ctx, "unbound type name: '%s'"%self.name)
        return ty
class ConsTyProduct(ConsTyExpr):
    def __init__(self, ctx, name, elts, fields):
        assert len(elts) >= len(fields), (elts, fields)
        self.ty = ProductType(name); self.elts = elts; self.fields = fields
    def eval(self, ctx):
        self.ty.init(tuple(elt.eval(ctx) for elt in self.elts), self.fields)
        if len(self.ty.elts) == 0: val = node(self.ty);
        else: val = constr_new(ctx, self.ty)
        bindVar(ctx, self.ty.name.sym, val); return self.ty
class ConsTyVariant(ConsTyExpr):
    def __init__(self, ctx, elts): self.ty = VariantType(); self.elts = elts
    def eval(self, ctx, fields=None):
        self.ty.init([elt.eval(ctx) for elt in self.elts]); return self.ty
class ConsTyProc(ConsTyExpr):
    def __init__(self, ctx, inTy, outTy):
        self.ty = ProcType(); self.inTy = inTy; self.outTy = outTy
    def eval(self, ctx):
        self.ty.init(self.inTy.eval(ctx), self.outTy.eval(ctx))
        return self.ty
ubKindTy, kindTy, toKind, fromKind = basicTy('Kind', object)
def isKind(val): return isTyped(val) and getTy(val) is kindTy
def getKind(ctx, name):
    ty = ctx.env.get(EnvKey(getDen(ctx.tenv, name)))
    if isKind(ty): return fromKind(ty)
    return None
def kindproc(name):
    def handleKP(kp): addPrimTy(name, toKind(kp)); return kp
    return handleKP
@kindproc('#product')
def kindProduct(ctx, body, name):
    if name is None: typeErr(ctx, "product type requires a name: '%s'"%body)
    fields = []
    return ConsTyProduct(ctx, EnvKey(name), tuple(parseType(ctx, form, fields)
                                                  for form in body), fields)
@kindproc('#variant')
def kindVariant(ctx, body, _):
    return ConsTyVariant(ctx, tuple(parseType(ctx, form) for form in body))
@kindproc('#proc')
def kindProc(ctx, body, _):
    if len(body) != 2: typeErr(ctx, "proc type requires two args: '%s'"%body)
    return ConsTyProc(ctx, parseType(ctx, body[0]), parseType(ctx, body[1]))
def parseType(ctx, body, fields=None, name=None):
    ctx, body = syncloExpand(ctx, body) # todo: shouldn't have to copy
    if isSymbol(body):
        if fields is not None: fields.append(None)
        return ConsTyVar(ctx, body)
    elif isListCons(body):
        body = tuple(fromList(body))
        hdCtx, hd = syncloExpand(ctx, body[0]) # todo: copy here too
        if isSymbol(hd):
            kind = getKind(ctx, hd)
            if kind is not None:
                if fields is not None: fields.append(None)
                return kind(ctx, body[1:], name)
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
            form = tuple(fromList(form))
            if len(form) == 2:
                name, body = form
                expr = parseType(ctx, body, name=name)
                ty = expr.preEval()
                if ty is None: aliases.append((name, expr))
                else: bindTy(ctx, name, ty); exprs.append(expr)
                continue
        typeErr(ctx, "invalid type binder: '%s'"%pretty(form))
    # todo: try sorting aliases topologically, otherwise error
    for name, expr in aliases: bindTy(ctx, name, expr.eval(ctx))
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
#class Seq(Expr): # todo: replace with a macro-generated proc?
#    def __init__(self, exprs): self.exprs = exprs[:-1]; self.last = exprs[-1]
#    def eval(self, ctx):
#        for expr in self.exprs: evalExpr(ctx, expr)
#        return cont(ctx, self.last)
class Apply(Expr):
    def __init__(self, proc, args): self.proc = proc; self.args = args
    def freeVars(self): return accFreeVars(self.args)
    def subst(self, subs): mapSubst(subs, self.args)
    def eval(self, ctx): return applyFull(ctx, self.proc, self.args)
# todo: extensible dispatch-proc?
class Switch(Expr): 
    def __init__(self, discrimTy, discrim, default, alts):
        self.discrimTy = discrimTy
        self.discrim = discrim; self.default = default; self.alts = alts
    def _children(self):
        return [body for _,body in self.alts]+[self.default, self.discrim]
    def freeVars(self): return accFreeVars(self._children())
    def subst(self, subs): mapSubst(subs, self._children())
    def eval(self, ctx):
        discrim = getDiscrim(evalExpr(ctx, self.discrim, self.discrimTy))
        body = self.alts.get(discrim)
        if body is None: body = self.default
        return cont(ctx, body)
class Let(Expr):
    def __init__(self, immed, nonrec, rec, body):
        self.immed = immed # compile-time bindings
        self.nonrec = nonrec; self.rec = rec # run-time bindings
        self.body = body
    def eval(self, ctx):
#        newCtx = ... # todo
        return cont(newCtx, self.body)
################################################################
class Throw(Expr): pass # could be a proc
class Catch(Expr): pass

################################################################
class Delay(Expr): pass
class Force(Expr): pass # could be a proc (eval then update)

################################################################
# class Meta(Expr):
#     def __init__(self, senv, env, form):
#         self.senv = senv; self.env = env; self.form = form
#     def _evalArgs(self, ctx):
#         senv = evalExpr(ctx, self.senv, envTy)
#         env = evalExpr(ctx, self.env, envTy)
# form = evalExpr(ctx, self.form) # todo: check proper form tag
#         ctx = ctx.copy()
#         ctx.hist = nil
#         ctx.senv = fromEnv(senv)
#         ctx.env = fromEnv(env)
#         return ctx, form
# class Expand(Meta):
#     def eval(self, ctx):
#         ctx, form = expand(*self._evalArgs(ctx))
#         return final(synclo_new(toCtx(ctx), nil, form))
