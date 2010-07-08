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
from data import *

def mapRest(f, ctx, xs):
    return [f(ctx, form) for form in fromList(cons_tail(xs), ctx)]
def checkIsForm(ctx, xs):
    if not formTy.contains(getTag(xs)):
        typeErr(ctx, "invalid form: '%s'"%pretty(xs))
def expandBasic(tyn):
    def ex(ctx, val):
        ubval = toList((symbol('_unbox'), val))
        return ctx, primSC(toList([symbol(tyn), ubval]))
    return ex
litExpanders = dict((ty, expandBasic(ty.name))
                    for ty in (intTy,floatTy,charTy))
def unitExpr(ctx): expr = Var(EnvKey(unitDen)); expr.ctx = ctx; return expr
def synclo_maybe(ctx0, ctx, form):
    if ctx0 != ctx: return synclo_new(toCtx(ctx), nil, form)
    return form
def _expand(ctx, xs):
    while True:
        checkIsForm(ctx, xs)
        ctx, xs = syncloExpand(ctx, xs)
        if isListCons(xs):
            hdCtx, hd = _expand(ctx.subHist(), cons_head(xs))
            if isSymbol(hd):
                den = hdCtx.senv.get(EnvKey(hd))
                if den is not None:
                    val = hdCtx.env.get(EnvKey(den))
                    if val is not None:
                        if isSemantic(val): break
                        elif isMacro(val):
                            ctx.hist.add(xs); mfrm = cons(hd, cons_tail(xs))
                            xs = applyMacro(ctx, val, mfrm); continue
            wrapped = toList(tuple(synclo_maybe(ctx, *expand(ctx, form))
                                   for form in fromList(cons_tail(xs), ctx)))
            xs = cons(synclo_maybe(ctx, hdCtx, hd), wrapped)
        else:
            ex = litExpanders.get(getTag(xs))
            if ex is not None: ctx, xs = ex(ctx, xs); continue
        break
    ctx.hist.finish(xs); return ctx, xs

def _semantize(ctx, xs):
    ctx, xs = syncloExpand(ctx, xs)
    checkIsForm(ctx, xs)
    if isListCons(xs):
        hdCtx, hd = syncloExpand(ctx, cons_head(xs))
        if isSymbol(hd):
            den = hdCtx.senv.get(EnvKey(hd))
            if den is not None:
                val = hdCtx.env.get(EnvKey(den))
                if val is not None and isSemantic(val):
                    expr = applySemantic(ctx, val, cons(hd, cons_tail(xs)))
                    expr.ctx = ctx; return expr
        hd = _semantize(hdCtx, hd); rest = fromList(cons_tail(xs), ctx)
        rest = [_semantize(ctx.subHist(), form) for form in rest]# todo: subHist?
        if isinstance(hd, Apply): hd.args.extend(rest); return hd
        else: expr = Apply(hd, rest)
    elif isSymbol(xs): expr = Var(EnvKey(getDen(ctx, xs)))
    elif isString(xs): expr = PrimVal(copyString(xs))
    elif xs is nil: return unitExpr(ctx)
    else: typeErr(ctx, "invalid symbolic expression: '%s'"%pretty(xs))
    expr.ctx = ctx; return expr

def expand(ctx, xs): return _expand(ctx.subHist(), xs)
def semantize(ctx, xs): return _semantize(*_expand(ctx.subHist(), xs))
def evaluate(ctx, xs, ty=None):
    xs = semantize(ctx, xs); return evalExpr(ctx, xs, ty)

def semproc(name):
    def install(f): addPrim(name, toSem(f)); return f
    return install
def primproc(name, *tys):
    def install(f):
        pty = currySpecificProcType(name, tys[:-1], tys[-1])
        addPrim(name, fproc_new(name, f, pty, len(tys)-1))
        return f
    return install
# todo: semArgsTy
def fromSrcForm(ctx, form):
    ctx1, form = syncloExpand(ctx, form)
    forms = tuple(synclo_maybe(ctx, ctx1, el) for el in fromList(form, ctx1))
    return forms
def semArgs(ctx, form, numArgs):
    args = fromSrcForm(ctx, form)
    if len(args)-1 != numArgs:
        typeErr(ctx, "semantic '%s' takes %d arguments but was given %d"%
                (pretty(cons_head(form)), numArgs, len(args)-1))
    return args[1:]
def tryUnbox(ctx, form):
    form = stripOuterSynClo(form); ty = getTag(form)
    if ty in (symTy, intTy, floatTy, charTy): return ty.unpackEl(form, 0)
    else: typeErr(ctx, "cannot unbox non-literal: '%s'"%pretty(form))
@semproc('_unbox')
def semUnbox(ctx, form):
    return PrimVal(tryUnbox(ctx, cons_head(cons_tail(form))))
@primproc('_expand', ctxTy, formTy, formTy)
def primExpand(ctx0, ctx, form):
    ctx, form = expand(fromCtx(ctx).withThread(ctx0.thread), form)
    return final(synclo_new(toCtx(ctx), nil, form))
@primproc('_eval', ctxTy, formTy, anyTy)
def primEval(ctx0, ctx, form):
    return final(evaluate(fromCtx(ctx).withThread(ctx0.thread), form, anyTy))
@primproc('_alias', symTy, symTy)
def primAlias(ctx0, sym): return final(alias_new(sym))
def repackSymbols(names):
    return toList(tuple(toSymbol(symbol_prim(name.sym)) for name in names))
def repackEnvSymbols(env):
    strat = nil
    for bs in env.stratified(): strat = cons(repackSymbols(bs.keys()), strat)
    return strat
@semproc('_ctx')
def semContext(ctx, form): semArgs(ctx, form, 0); return PrimVal(toCtx(ctx))
@primproc('_ctx-env', ctxTy, listTy)
def primCtxEnv(ctx0, ctx): return final(repackEnvSymbols(fromCtx(ctx).senv))
################################################################
# modules
@primproc('_module', ifaceTy, nspaceTy, modTy)
def primModule(ctx0, iface, nspace):
    return final(toMod(Module(fromIface(iface), fromNspace(nspace))))
@primproc('_mod-iface', modTy, ifaceTy)
def primModIface(ctx0, mod): return final(toIface(fromMod(mod).iface))
@primproc('_mod-nspace', modTy, nspaceTy)
def primModNspace(ctx0, mod): return final(toNspace(fromMod(mod).nspace))
@primproc('_mod-names', modTy, listTy)
def primModNames(ctx0, mod):
    return final(toList([nm.sym for nm in fromMod(mod).valNames()]))
@primproc('_mod-resolve', modTy, symTy, anyTy)
def primModResolve(ctx0, mod, sym): return final(fromMod(mod).valResolve(sym))
# todo: interface (exports?) and namespace (components?) introspection
@primproc('_export', listTy, listTy, listTy, ifaceTy)
def primExport(ctx0, valNames, typeNames, readerStrs):
    rss = tuple(fromString(rs) for rs in fromList(readerStrs))
    return final(toIface(ExportInterface(fromList(valNames),
                                         fromList(typeNames), rss)))
@primproc('_namespace', unitTy, nspaceTy)
def primNspace(ctx0, _): return final(toNspace(Namespace(ctx0.root)))
@primproc('_open', modTy, nspaceTy, unitTy)
def primOpen(ctx0, mod, nspace):
    fromMod(mod).openIn(fromNspace(nspace)); return final(unit)
@primproc('_file', stringTy, nspaceTy, unitTy)
def primFile(ctx0, path, nspace):
    # todo: path lookup
    args = fromNspace(nspace), fromString(path)
    FileSource(*args).eval(ctx0.thread, evaluate); return final(unit)
@primproc('_import', symTy, anyTy, nspaceTy, unitTy)
def primImport(ctx0, sym, val, nspace):
    fromNspace(nspace).defVar(sym, val); return final(unit)
# todo: _compound-iface, _inline, _text
# @primproc('_ctx-ns', ctxTy, nspaceTy)
# def primCtxNspace(ctx0, ctx): return final(toNspace(fromCtx(ctx).nspace))
# @primproc('_ns-ctx', nspaceTy, ctxTy)
# def primNspaceCtx(ctx0, ns): return final(toCtx(fromNspace(ns).ctx))
# @primproc('_ns-exports', nspaceTy, listTy)
# def primNspaceExports(ctx0, ns):
#     return final(repackSymbols(fromNspace(ns).exportedNames))
################################################################
# thread-local data
@primproc('_get-tl-data', symTy, anyTy)
def primGetTLData(ctx0, key):
    return final(ctx0.thread.getDataTLS(ctx0, EnvKey(key)))
@semproc('_init-tl-data')
def semInitTLData(ctx, form):
    key, body = semArgs(ctx, form, 2); key = EnvKey(evaluate(ctx, key))
    ctx.root.setInitTLS(ctx, key, semantize(ctx, body)); return unitExpr(ctx)
################################################################
# control flow
@semproc('_unwind')
def semUnwind(ctx, form): semArgs(ctx, form, 0); return Unwind()
@semproc('_catch-unwind')
def semCatchUnwind(ctx, form):
    return CatchUnwind(*tuple(semantize(ctx, frm)
                              for frm in semArgs(ctx, form, 2)))
@semproc('_seq')
def semSeq(ctx, form):
    return Seq(tuple(semantize(ctx, frm)
               for frm in fromSrcForm(ctx, form)[1:]))
def toTy(ctx, form):
    ctx, form = expand(ctx, form)
    if isSymbol(form):
        ty = getTy(ctx, form)
        if ty is not None: return type_type(ty)
    typeErr(ctx, "invalid type name: '%s'"%form)
@primproc('_force', anyTy, anyTy)
def primForce(ctx0, boxed): return final(force(ctx0, boxed))
@semproc('_delay') # todo: choose whether it's worth making a thunk
def semDelay(ctx, form):
    return ConsThunk(EnvKey(gensym()),
                     semantize(ctx, semArgs(ctx, form, 1)[0]))
@semproc('_proc')
def semConsProc(ctx, form):
    binders, body = semArgs(ctx, form, 2)
    vars = []; paramts = []; bodyCtx = ctx.extendSyntax()
    for binder in fromSrcForm(ctx, binders):
        bndr = stripSC(binder)
        if isListCons(bndr):
            var, ty = tuple(fromSrcForm(ctx, binder)); ty = toTy(ctx, ty)
            var = stripSC(var)
        else: var = bndr; ty = anyTy
        if not isSymbol(var):
            typeErr(ctx, "invalid proc binder: '%s'"%pretty(var))
        vars.append(EnvKey(newDen(bodyCtx, var))); paramts.append(ty)
    return ConsProc(EnvKey(gensym()), vars,
                    semantize(bodyCtx, body), paramts, None)
unboxDen = primDen('_unbox')
@semproc('_switch')
def semSwitch(ctx, form):
    discrim, alts = semArgs(ctx, form, 2)
    default = None; dalts = {}
    for alt in fromSrcForm(ctx, alts):
        matches, body = tuple(fromSrcForm(ctx, alt))
        body = semantize(ctx, body)
        matchesCtx, matches = syncloExpand(ctx, matches)
        if matches is nil:
            if default is not None:
                typeErr(ctx, 'switch can only have one default')
            default = body
        else:
            for pat in fromSrcForm(matchesCtx, matches):
                patCtx, pat = syncloExpand(ctx, pat)#stripOuterSynClo(pat)
                if isSymbol(pat): pat = toTy(patCtx, pat)
                elif isListCons(pat):
                    xpat = tuple(fromSrcForm(patCtx, pat))
                    if len(xpat) != 2:
                        typeErr(ctx, "invalid pattern: '%s'"%pretty(pat))
                    ubsym, val = xpat
                    ubsymCtx, ubsym = syncloExpand(patCtx, ubsym)
                    if symbol_eq(unboxDen, getDen(ubsymCtx, ubsym)):
                        pat = getVal(tryUnbox(ctx, val))
                assert pat not in dalts, pat
                dalts[pat] = body
    return Switch(semantize(ctx, discrim), default, dalts)
@semproc('_let')
def semLet(ctx, form):
    immed, nonrec, rec, body = semArgs(ctx, form, 4)
    immedCtx = ctx.extendSyntax(); bodyCtx = immedCtx.extendSyntax()
    immeds = []; recs = []; nonrecs = []
    for binding in fromSrcForm(ctx, immed):
        binder, rhs = tuple(fromSrcForm(ctx, binding))
        immeds.append((EnvKey(newDen(immedCtx, stripSC(binder))), rhs))
    for binder, rhs in immeds: ctx.env.add(binder, evaluate(immedCtx, rhs))
    for binding in fromSrcForm(ctx, nonrec):
        binder, rhs = tuple(fromSrcForm(ctx, binding))
        nonrecs.append((EnvKey(newDen(bodyCtx, stripSC(binder))),
                        semantize(immedCtx, rhs)))
    for binding in fromSrcForm(ctx, rec):
        binder, rhs = tuple(fromSrcForm(ctx, binding))
        recs.append([EnvKey(newDen(bodyCtx, stripSC(binder))), rhs])
    for recp in recs: recp[1] = semantize(bodyCtx, recp[1])
    return Let(nonrecs, recs, semantize(bodyCtx, body))
################################################################
# nodes
def semNodeAccess(ctx, ty, node):
    ty = toTy(ctx, ty); node = semantize(ctx, node); return ty, node
def semNodeIndex(ctx, ty, idx, node):
    ty, node = semNodeAccess(ctx, ty, node)
    if isinstance(ty, ProductType): idx = fromInt(evaluate(ctx, idx, ty=intTy))
    else: idx = semantize(ctx, idx)
    return idx, ty, node
@semproc('_unpack')
def semNodeUnpack(ctx, form):
    return NodeUnpack(*semNodeIndex(ctx, *semArgs(ctx, form, 3)))
@semproc('_pack')
def semNodePack(ctx, form):
    *rest, rhs = semArgs(ctx, form, 4); rhs = semantize(ctx, rhs)
    return NodePack(rhs, *semNodeIndex(ctx, *rest))
@semproc('_count')
def semCount(ctx, form):
    return NodeCount(*semNodeAccess(ctx, *semArgs(ctx, form, 2)))
@primproc('_tag', anyTy, tyTy)
def primNodeTag(ctx0, node): return final(ubTyTy.new(getTag(node)))
@primproc('_tag-pattern', ctxTy, symTy, listTy)
def primTagPattern(ctx0, ctx, tagSym):
    result = nil; tag = getTy(fromCtx(ctx), tagSym)
    if tag is not None:
        if isType(tag):
            ty = type_type(tag)
            if isinstance(ty, ProductType):
                result = toList([tag, toList([toInt(idx) for idx in
                                              range(ty.numIndices())])])
    return final(result)
@semproc('_coll-new') # todo: capacity hint for arrays?
def semCollNew(ctx, form):
    ty = toTy(ctx, semArgs(ctx, form, 1)[0]); return ConsColl(ty, ctx)
################################################################
# arrays
@semproc('_array-pop')
def semArrayPop(ctx, form):
    return ArrayPop(*semNodeAccess(ctx, *semArgs(ctx, form, 2)))
@semproc('_array-push')
def semArrayPush(ctx, form):
    *rest, rhs = semArgs(ctx, form, 3); rhs = semantize(ctx, rhs)
    return ArrayPush(rhs, *semNodeAccess(ctx, *rest))
def semSlice(ctx, ty, start, end, node):
    start = semantize(ctx, start); end = semantize(ctx, end)
    ty, node = semNodeAccess(ctx, ty, node)
    return start, end, ty, node
@semproc('_slice-unpack')
def semSliceUnpack(ctx, form):
    return ArraySliceUnpack(*semSlice(ctx, *semArgs(ctx, form, 4)))
@semproc('_slice-pack')
def semSlicePack(ctx, form):
    *rest, rhs = semArgs(ctx, form, 5); rhs = semantize(ctx, rhs)
    return ArraySlicePack(rhs, *semSlice(ctx, *rest))
################################################################
# tables
@semproc('_table-pop')
def semTableDel(ctx, form):
    return TableDelete(*semNodeIndex(ctx, *semArgs(ctx, form, 3)))
@semproc('_table-fold')
def semTableFold(ctx, form):
    ty, node, *rest = semArgs(ctx, form, 4)
    ty, node = semNodeAccess(ctx, ty, node)
    rest = tuple(semantize(ctx, xx) for xx in rest)
    return TableFold(*(rest+(ty, node)))
################################################################
# definitions
@semproc('_def-types')
def semDefTypes(ctx, form):
    bindTypes(ctx, fromList(cons_tail(form), ctx)); return unitExpr(ctx)
@semproc('_def')
def semDef(ctx, form):
    binder, body = semArgs(ctx, form, 2); ue = unitExpr(ctx)
    ctx.nspace.defVar(stripSC(binder), evaluate(ctx, body)); return ue
@semproc('_refer')
def semReferVar(ctx, form):
    binder1, binder2 = semArgs(ctx, form, 2)
    ctx.nspace.referVar(ctx, binder2, binder1); return unitExpr(ctx)
@semproc('_def-op')
def semDefOp(ctx, form):
    name, fixity, assoc, prec = stripSCs(semArgs(ctx, form, 4))
    op = newOperator(name, symbol_name(fixity), assoc, fromInt(prec))
    ctx.nspace.defOp(name, op); return unitExpr(ctx)
@semproc('_def-reader')
def semDefReader(ctx, form):
    readStr, body = semArgs(ctx, form, 2)
    ctx.nspace.defReader(fromString(stripSC(readStr)),
                         wrapReader(evaluate(ctx, body)))
    return unitExpr(ctx)
################################################################
# parser
def wrapReader(proc):
    def wrapped(parser, chs):
        tm = evalExpr(*applyDirect(parser.ctx, proc,
                                   (toParser(parser), toString(chs))))
        if tm is not unit and not isSynClo(tm): tm = srcWrap(parser, tm)
        return tm
    return wrapped
@primproc('_read-bracketed-form', parserTy, stringTy, formTy)
def primReadBracketedForm(ctx0, parser, closeBracket):
    closeBracket = fromString(closeBracket)
    return final(fromParser(parser).bracketedExpr(closeBracket))
# todo: expose other parser primitives
################################################################
# interaction
from lex import LexError
from syntax import ParseError, Parser
from data import Env, makeStream, unit
def interact(thread, mod):
    result = [unit]
    def evalPrint(ctx, expr):
        res = evaluate(ctx, expr); result[0] = res; print(pretty(res))
    for stream in interactStreams('%s> '%mod.name):
        try: DirectStreamSource(mod.nspace, mod.name, stream).eval(thread,
                                                                   evalPrint)
        except: raise
        # except LexError: raise
        # except ParseError: raise
        # except TyError: raise
    print(''); return result[0]
def evalFile(thread, mod, absPath):
    result = [unit]
    def evalSave(ctx, expr): result[0] = evaluate(ctx, expr)
    FileSource(mod.nspace, absPath).eval(thread, evalSave)
    return result[0]
debugOpts = [('halt', 'abort this computation', None)]; debugOptNames = set()
def dbgopt(name, desc): # todo: add help descriptions
    def mkdopt(f):
        assert name not in debugOptNames
        debugOptNames.add(name); debugOpts.append((name, desc, f))
        return f
    return mkdopt
def debugErr(ctx, exc):
    print('ERROR:', pretty(exc))
    while True:
        print('debug options:')
        for idx, (name, desc, opt) in enumerate(debugOpts):
            print('(%d)'%idx, name)
        while True:
            try:
                idx = input('choose an option by number (? to reprint): ')
                if idx.strip() == '?': break
                idx = int(idx)
                if 0 <= idx < len(debugOpts):
                    name, desc, dopt = debugOpts[idx]
                    if dopt is None: return
                    dopt(ctx); break
            except ValueError: pass
@dbgopt('help', 'describe debugging options')
def dbgHelp(ctx):
    print('debug option descriptions:')
    for idx, (name, desc, opt) in enumerate(debugOpts):
        print('(%d) %s - %s'%(idx, name, desc))
@dbgopt('trail', 'view a partial traceback')
def dbgTrail(ctx):
    print('evaluation trail (most recent expr last)')
    print(trailPretty(ctx.thread.fullTrail(), '  '))
# def debugErr(exc, ctx, expr): # todo: exit without resume?
#     root = ctx.nspace.mod.root
#     if root.debugging: return None
#     root.debugging = True; name = ctx.nspace.mod.name
#     print('ERROR:', exc); print(ctx.hist.show()); print(expr) # todo: pretty
#     if input('enter debug mode?: ').lower() in ('n', 'no'): return None
#     mod = root.moduleFromCtx('%s debug'%name, ctx)
#     result = interact(ctx.thread, mod)
#     root.debugging = False; return result
