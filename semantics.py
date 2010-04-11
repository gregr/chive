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
        rest = [expr for _,expr in mapRest(semSub, ctx, xs)]
        hdCtx, hd = _semantize(hdCtx, hd)
        if isinstance(hd, Apply): hd.args.extend(rest); return ctx, hd
        else: return ctx, Apply(hd, rest)
    elif isSymbol(xs):
        den = getDen(ctx.senv, xs); val = ctx.env.get(EnvKey(den))
        if isTyped(val) and isType(val):
            ty = type_type(val)
            if isinstance(ty, ProductType): den = ty.consDen
        return ctx, Var(EnvKey(den))
    elif xs is nil: return ctx, unitExpr
    else: typeErr(ctx, "invalid symbolic expression: '%s'"%pretty(xs))

def semantize(ctx, xs): return _semantize(*expand(ctx, xs))
def evaluate(ctx, xs, tag=None):
    ctx, xs = semantize(ctx, xs); return evalExpr(ctx, xs, tag)

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
        return ctx, PrimVal(ty.unpackEl(form, 0))
    else: typeErr(ctx, "cannot unbox non-literal: '%s'"%form)
def toTy(ctx, form):
    ctx, form = expand(ctx, form)
    if not isSymbol(form): typeErr(ctx, "invalid type name: '%s'"%form)
    return ctx.env.get(EnvKey(ctx.tenv.get(EnvKey(form))))
def semArgs(ctx, form, numArgs):
    args = tuple(fromList(cons_tail(form)))
    if len(args) != numArgs:
        typeErr(ctx, "semantic '%s' takes %d arguments but was given %d"%
                (pretty(cons_head(form)), numArgs, len(args)))
    return args
def semNodeAccess(ctx, ty, idx, node):
    ty = toTy(ctx, ty)
    idx = evaluate(ctx, idx, intTy)
    ndCtx, node = semantize(ctx, node)
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
        den = alias_new(var); bodyCtx.senv.add(EnvKey(var), den)
        vars.append(EnvKey(den)); paramts.append(ty)
    return ctx, ConsProc(EnvKey(gensym()), vars,
                         semantize(bodyCtx, body)[1], paramts, None)
@semproc('#node-unpack')
def semNodeUnpack(ctx, form):
    return ctx, NodeUnpack(*semNodeAccess(ctx, *semArgs(ctx, form, 3)))
@semproc('#node-pack')
def semNodePack(ctx, form):
    *rest, rhs = semArgs(ctx, form, 4); rhsCtx, rhs = semantize(ctx, rhs)
    return ctx, NodePack(rhs, *semNodeAccess(ctx, *rest))
@semproc('#def-types')
def semDefTypes(ctx, form):
    bindTypes(ctx, fromList(cons_tail(form))); return ctx, unitExpr
def interactOnce(modName, ctx): # todo: break into smaller pieces
    import readline
    from io import StringIO
    buffer = []
    prompt1 = '%s> ' % modName
    prompt2 = ('.'*(len(prompt1)-1)) + ' '
    line = input(prompt1)
    while line:
        buffer.append(line+'\n')
        line = input(prompt2)
    return StringIO(''.join(buffer))
def interact(ctx):
    modName = 'test' # todo
    # todo: parser from ctx
    from lex import LexError
    from syntax import ParseError, Parser
    from data import Env, makeStream, unit
    parser = Parser(Env())
    try:
        while True:
            result = unit
            exprs = parser.parse(modName, interactOnce(modName, ctx))
            try:
                for expr, attr in exprs:
                    result = withSubCtx(evaluate, ctx, attr, expr)
                    print(pretty(result))
            except LexError: raise
            except ParseError: raise
            except TypeError: raise
    except EOFError: pass
    return result

def _test():
    ctx = primCtx
    interact(ctx)
    print('')
if __name__ == '__main__': _test()
