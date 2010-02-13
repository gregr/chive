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

from expr import evalExpr, Var, Apply
from data import (TypeError, typeErr,
                  nil, cons, cons_head, cons_tail,
                  toList, fromList, isListCons,
                  isSymbol, EnvKey, synclo_new, alias_new, syncloExpand,
                  isMacro, applyMacro, isSemantic, applySemantic, semantic_new,
                  checkIsNode, node_tag, addPrim, primCtx, pretty, unitDen)

def attr_head(attr):
    if attr.subs is nil: return attr
    else: return cons_head(attr.subs)
def attr_tail(attr):
    if attr.subs is nil: return nil
    else: return cons_tail(attr.subs)
def withSubCtx(f, ctx, attr, xs):
    ctx = ctx.copy()
    ctx.attr = attr
    return f(ctx, xs)
def headSubCtx(f, ctx, xs):
    return withSubCtx(f, ctx, attr_head(ctx.attr), cons_head(xs))
def mapRest(f, ctx, xs):
    xs0 = fromList(cons_tail(xs))
    attr0 = fromList(attr_tail(ctx.attr))
    attr0 += [ctx.attr]*(len(xs0)-len(attr0))
    return [f(ctx, aa, xx) for aa, xx in zip(attr0, xs0)]
litExpanders = {}
def expand(ctx, xs):
    while True:
        checkIsNode(ctx, xs)
        ctx.senv, xs = syncloExpand(ctx.senv, xs)
        ctx.histAppend(xs)
        if isListCons(xs):
            hdCtx, hd = headSubCtx(expand, ctx, xs)
            if isSymbol(hd):
                den = hdCtx.senv.get(EnvKey(hd))
                if den is not None:
                    val = hdCtx.env.get(den)
                    if val is not None:
                        if isSemantic(val): break
                        elif isMacro(val):
                            xs = applyMacro(ctx, val, cons(hd, cons_tail(xs)))
                            continue
            def wrap(ctx_, _, xx):
                if ctx_.senv is not ctx.senv:
                    xx = synclo_new(toEnv(ctx_.senv), nil, xx)
                return xx
            def wrapSub(ctx, aa, xx):
                return aa, wrap(*withSubCtx(expand, ctx, aa, xx))
            rest = mapRest(wrapSub, ctx, xs)
            if rest: attr1, xs1 = list(zip(*rest))
            else: attr1, xs1 = [], []
            xs = cons(wrap(hdCtx, None, hd), toList(xs1))
            ctx.attr = ctx.attr.copy();
            ctx.attr.subs = cons(attr_head(ctx.attr), toList(attr1))
        else:
            ex = litExpanders.get(node_tag(xs))
            if ex is not None: return ex(ctx, xs)
        break
    return ctx, xs

def syncloExCtx(ctx, expr):
    ctx.senv, expr = syncloExpand(ctx.senv, expr)
    return ctx, expr
def semantize(ctx, xs):
    ctx, xs = expand(ctx, xs)
    checkIsNode(ctx, xs)
    if isListCons(xs):
        hdCtx, hd = headSubCtx(syncloExCtx, ctx, xs)
        if isSymbol(hd):
            den = hdCtx.senv.get(EnvKey(hd))
            if den is not None:
                val = hdCtx.env.get(den)
                if val is not None and isSemantic(val):
                    return applySemantic(ctx, val, cons(hd, cons_tail(xs)))
        def semSub(ctx, aa, xx): return withSubCtx(semantize, ctx, aa, xx)
        rest = [expr for _,expr in mapRest(semSub, ctx, xs)]
        hdCtx, hd = semantize(hdCtx, hd)
        if isinstance(hd, Apply): hd.args.extend(rest); return ctx, hd
        else: return ctx, Apply(hdExpr, rest)
    elif isSymbol(xs):
        den = ctx.senv.get(EnvKey(xs))
        if den is None: den = alias_new(xs); ctx.senv.add(EnvKey(den), xs)
        return ctx, Var(EnvKey(den))
    elif xs is nil: return ctx, Var(EnvKey(unitDen))
    else: typeErr(ctx, "invalid symbolic expression: '%s'"%xs)

def evaluate(ctx, xs, tag=None):
    ctx, xs = semantize(ctx, xs); return evalExpr(ctx, xs, tag)

def semproc(name):
    def install(f): addPrim(name, semantic_new(f)); return f
    return install
def stripOuterSynClo(xs):
    while isSynClo(xs): xs = synclo_form(xs)
    return xs
@semproc('#unbox')
def semUnbox(ctx, form):
    # todo: validate form
    form = stripOuterSynClo(cons_head(cons_tail(form)))
    if node_tag(form) in (symTag, intTag, floatTag, charTag):
        return ctx, PrimVal(packPrimVal(form[1]))
    else: typeErr(ctx, "cannot unbox non-literal: '%s'"%form)
@semproc('#node')
def semNode(ctx, form):
    # todo: validate form
    cargs = [expr for _, expr in semantize(ctx, cons_tail(cons_tail(form)))]
    tag = evaluate(cons_head(cons_tail(form)), tagTag)
    return ctx, ConsNode(tag, cargs, ctx)

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
                    result = evaluate(ctx, expr); print(pretty(result))
            except LexError: raise
            except ParseError: raise
            except TypeError: raise
    except EOFError: pass
    return result

def _test():
    ctx = primCtx()
    interact(ctx)
    print('')
if __name__ == '__main__': _test()
