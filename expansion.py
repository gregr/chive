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

from data import (cons, cons_head, cons_tail, toList, fromList, isSymbol,
                  EnvKey, synclo_new, syncloExpand)

def attr_head(attr):
    if attr.subs is nil: return attr
    else: return cons_head(attr.subs)
def attr_tail(attr):
    if attr.subs is nil: return nil
    else: return cons_tail(attr.subs)

# todo: macro_apply, isMacro, isExprCons
litExpanders = {}
def expand(ctx, attr, xs):
    ctx = ctx.copy()
    while True:
        ctx.senv, xs = syncloExpand(ctx.senv, xs)
        if isListCons(xs):
            hdCtx, hd, hdAttr = expand(ctx, attr_head(attr), cons_head(xs))
            if isSymbol(hd):
                den = hdCtx.senv.get(EnvKey(hd))
                if den is not None:
                    val = hdCtx.env.get(den)
                    if val is not None:
                        if isExprCons(val): break
                        elif isMacro(val):
                            ctx, attr, xs = macro_apply(val, ctx, attr,
                                                        cons(head,
                                                             cons_tail(xs)))
                            continue
            def wrap(ctx_, _, xx):
                if ctx_.senv is not ctx.senv:
                    xx = synclo_new(toEnv(ctx_.senv), nil, xx)
                return xx
            xs0 = fromList(cons_tail(xs))
            attr0 = fromList(attr_tail(attr))
            attr0 += [attr]*(len(xs0)-len(attr0))
            rest = [(aa, wrap(*expand(ctx, aa, xx)))
                    for aa, xx in zip(attr0, xs0)]
            if rest: attr1, xs1 = list(zip(*rest))
            else: attr1, xs1 = [], []
            xs = cons(wrap(hdCtx, None, hd), toList(xs1))
            attr = attr.copy(); attr.subs = cons(hdAttr, toList(attr1))
        else:
            ex = litExpanders.get(node_tag(xs))
            if ex is not None: return ex(ctx, xs)
        break
    return ctx, attr, xs
