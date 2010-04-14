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

from expr import *
from syntax import toAttr, fromAttr
from data import *

def attr_head(attr):
    if fromAttr(attr).subs is nil: return attr
    else: return cons_head(fromAttr(attr).subs)
def attr_tail(attr):
    if fromAttr(attr).subs is nil: return nil
    else: return cons_tail(fromAttr(attr).subs)
def withSubCtx(f, ctx, attr, xs):
    ctx = ctx.copy()
    ctx.attr = attr
    return f(ctx, xs)
def headSubCtx(f, ctx, xs):
    return withSubCtx(f, ctx, attr_head(ctx.attr), cons_head(xs))
def mapRest(f, ctx, xs):
    xs0 = list(fromList(cons_tail(xs)))
    attr0 = list(fromList(attr_tail(ctx.attr)))
    attr0 += [ctx.attr]*(len(xs0)-len(attr0))
    return [f(ctx, aa, xx) for aa, xx in zip(attr0, xs0)]
def checkIsForm(ctx, xs): return formTy.contains(getTy(xs))
def expandBasic(tyn):
    def ex(ctx, val):
        ubval = toList((symbol('#unbox'), val))
        return ctx, primSC(toList([symbol(tyn), ubval]))
    return ex
litExpanders = dict((ty, expandBasic(ty.name))
                    for ty in (intTy,floatTy,charTy))
def expand(ctx, xs):
    while True:
        checkIsForm(ctx, xs) 
        ctx, xs = syncloExpand(ctx, xs)
        ctx.histAppend(xs)
        if isListCons(xs):
            hdCtx, hd = headSubCtx(expand, ctx, xs)
            if isSymbol(hd):
                den = hdCtx.senv.get(EnvKey(hd))
                if den is not None:
                    val = hdCtx.env.get(EnvKey(den))
                    if val is not None:
                        if isSemantic(val): break
                        elif isMacro(val):
                            xs = applyMacro(ctx, val, cons(hd, cons_tail(xs)))
                            continue
            def wrap(ctx_, xx):
                if ctx_ != ctx: xx = synclo_new(toCtx(ctx_), nil, xx)
                return xx
            def wrapSub(ctx, aa, xx):
                return aa, wrap(*withSubCtx(expand, ctx, aa, xx))
            rest = mapRest(wrapSub, ctx, xs)
            if rest: attr1, xs1 = list(zip(*rest))
            else: attr1, xs1 = [], []
            xs = cons(wrap(hdCtx, hd), toList(xs1))
            ctx.attr = toAttr(fromAttr(ctx.attr).copy())
            fromAttr(ctx.attr).subs = cons(attr_head(ctx.attr), toList(attr1))
        else:
            ex = litExpanders.get(getTy(xs))
            if ex is not None: ctx, xs = ex(ctx, xs); continue
        break
    return ctx, xs

unitExpr = Var(EnvKey(unitDen))
def _semantize(ctx, xs):
    ctx, xs = syncloExpand(ctx, xs)
    checkIsForm(ctx, xs)
    if isListCons(xs):
        hdCtx, hd = headSubCtx(syncloExpand, ctx, xs)
        if isSymbol(hd):
            den = hdCtx.senv.get(EnvKey(hd))
            if den is not None:
                val = hdCtx.env.get(EnvKey(den))
                if val is not None and isSemantic(val):
                    return applySemantic(ctx, val, cons(hd, cons_tail(xs)))
        def semSub(ctx, aa, xx): return withSubCtx(_semantize, ctx, aa, xx)
        rest = mapRest(semSub, ctx, xs); hd = _semantize(hdCtx, hd)
        if isinstance(hd, Apply): hd.args.extend(rest); return hd
        else: return Apply(hd, rest)
    elif isSymbol(xs):
        den = getDen(ctx, xs); val = ctx.env.get(EnvKey(den))
        if isTyped(val) and isType(val):
            ty = type_type(val)
            if isinstance(ty, ProductType): den = ty.consDen
        return Var(EnvKey(den))
    elif xs is nil: return unitExpr
    else: typeErr(ctx, "invalid symbolic expression: '%s'"%pretty(xs))

def semantize(ctx, xs): return _semantize(*expand(ctx, xs))
def evaluate(ctx, xs, tag=None):
    xs = semantize(ctx, xs); return evalExpr(ctx, xs, tag)

def semproc(name):
    def install(f): addPrim(name, toSem(f)); return f
    return install
def primproc(name, *tys):
    def install(f):
        pty = currySpecificProcType(name, tys[:-1], tys[-1])
        addPrim(name, fproc_new(name, f, pty))
        return f
    return install
def stripOuterSynClo(xs):
    while isSynClo(xs): xs = synclo_form(xs)
    return xs
@semproc('#unbox')
def semUnbox(ctx, form):
    form = stripOuterSynClo(cons_head(cons_tail(form))); ty = getTy(form)
    if ty in (symTy, intTy, floatTy, charTy):
        return PrimVal(ty.unpackEl(form, 0))
    else: typeErr(ctx, "cannot unbox non-literal: '%s'"%form)
def toTy(ctx, form):
    ctx, form = expand(ctx, form)
    if not isSymbol(form): typeErr(ctx, "invalid type name: '%s'"%form)
    return type_type(ctx.env.get(EnvKey(ctx.senv.get(EnvKey(form)))))
# todo: semArgsTy
def semArgs(ctx, form, numArgs):
    args = tuple(fromList(cons_tail(form)))
    if len(args) != numArgs:
        typeErr(ctx, "semantic '%s' takes %d arguments but was given %d"%
                (pretty(cons_head(form)), numArgs, len(args)))
    return args
def semNodeAccess(ctx, ty, idx, node):
    ty = toTy(ctx, ty)
    idx = evaluate(ctx, idx, intTy)
    node = semantize(ctx, node)
    return ty, fromInt(idx), node, ctx
@semproc('#proc')
def semConsProc(ctx, form):
    binders, body = semArgs(ctx, form, 2)
    vars = []; paramts = []
    bodyCtx = ctx.copy(); bodyCtx.senv = Env(ctx.senv)
    for binder in fromList(binders):
        if isListCons(binder):
            var, ty = tuple(fromList(binder)); ty = toTy(ctx, ty)
        else: var = binder; ty = anyTy
        if not isSymbol(var): # todo: synclo?
            typeErr(ctx, "invalid proc binder: '%s'"%pretty(var))
        vars.append(EnvKey(newDen(bodyCtx.senv, var))); paramts.append(ty)
    return ConsProc(EnvKey(gensym()), vars,
                    semantize(bodyCtx, body), paramts, None)
@semproc('#switch')
def semSwitch(ctx, form):
    discrim, alts = semArgs(ctx, form, 2)#fromList(cons_tail(form))
    default = None
    dalts = {}
    for alt in fromList(alts):
        matches, body = tuple(fromList(alt))
        body = semantize(ctx, body)
        if matches is nil:
            if default is not None:
                typeErr(ctx, 'switch can only have one default')
            default = body
        else:
            for pat in fromList(matches):
                if isSymbol(pat): pat = toTy(ctx, pat)
                elif isListCons(pat): assert False, pat
                assert pat not in dalts, pat
                dalts[pat] = body
    return Switch(semantize(ctx, discrim), default, dalts)
@semproc('#node-unpack')
def semNodeUnpack(ctx, form):
    return NodeUnpack(*semNodeAccess(ctx, *semArgs(ctx, form, 3)))
@semproc('#node-pack')
def semNodePack(ctx, form):
    *rest, rhs = semArgs(ctx, form, 4); rhs = semantize(ctx, rhs)
    return NodePack(rhs, *semNodeAccess(ctx, *rest))
@semproc('#def-types')
def semDefTypes(ctx, form):
    bindTypes(ctx, fromList(cons_tail(form))); return unitExpr
@semproc('#def')
def semDef(ctx, form):
    binder, body = semArgs(ctx, form, 2)
    ctx.nspace.define(binder, evaluate(ctx, body)); return unitExpr
@semproc('#refer')
def semRefer(ctx, form):
    binder1, binder2 = semArgs(ctx, form, 2)
    ctx.nspace.refer(ctx, binder2, binder1); return unitExpr
@semproc('#def-op')
def semDefOp(ctx, form):
    name, fixity, assoc, prec = semArgs(ctx, form, 4)
    op = newOperator(name, symbol_name(fixity), assoc, fromInt(prec))
    ctx.nspace.defOp(name, op); return unitExpr
def evalModule(mod, onResult=lambda _: None):
    for expr, attr in mod:
        result = withSubCtx(evaluate, mod.curNS.ctx, attr, expr)
        onResult(result)
def interact(mod):
    from lex import LexError
    from syntax import ParseError, Parser
    from data import Env, makeStream, unit
    result = [unit]
    def onResult(res): result[0] = res; print(pretty(res))
    for stream in interactStreams('%s> '%os.path.basename(str(mod.name))):
        mod.setStream(stream)
        try: evalModule(mod, onResult)
        except LexError: raise
        except ParseError: raise
        except TypeError: raise
    return result
def _test():
    import sys
#    root = Root((os.getcwd(), ))
    root = Root(())
    if len(sys.argv) > 1:
        mod = root.getFileModule(sys.argv[1]); evalModule(mod)
    else: mod = root.rawModule('test')
    interact(mod); print('')
    return mod
if __name__ == '__main__': mod = _test()
