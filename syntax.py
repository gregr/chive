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

from lex import SrcAttr, tokens
from data import (prodTy, isSymbol, symbol, Env, EnvKey, toList, fromList, pretty,
                  makeStream)
from type import *
from itertools import chain

class ParseError(Exception): pass
def parseErr(attr, msg): raise ParseError(attr, msg)

tokToAtomCons = dict(
    ident=(lambda _,tok: symbol(tok.val)),
    operator=(lambda ops,tok: makeOperator(ops, symbol(tok.val), tok.attr)),
    literal=(lambda _,tok: tok.val),
    )
ubAttrTy = PyType('#Attr', SrcAttr)
attrTy = prodTy('Attr', ubAttrTy)
def toAttr(at): return attrTy.new(ubAttrTy.new(at))
def fromAttr(at): return getVal(attrTy.unpackEl(at, 0))
def makeAtom(opsTable, tok):
    constr = tokToAtomCons.get(tok.ty)
    if constr is None: parseErr(tok.attr, 'invalid atom')
    return constr(opsTable, tok), toAttr(tok.attr)
def makeApp(terms, attr=None):
    if len(terms) > 0:
        def fromAt(at):
            at = getVal(attrTy.unpackEl(at, 0))
            return at.start, at
        subs = sorted(fromAt(at) for _,at in terms)
        srcs = []
        for (_,at) in subs:
            for atsrc in at.srcs:
                if atsrc not in srcs: srcs.append(atsrc)
        attr = SrcAttr(subs[0][1].streamName, srcs, subs[0][1].start,
                       subs[-1][1].end)
    assert attr is not None # attr=None only valid when len(terms)>0
    tas = list(zip(*terms))
    if not tas: tas = ([], [])
    attr.subs = toList(tas[1])
    return toList(tas[0]), toAttr(attr)

def maybeMakeApp(arg, attr=None):
    terms, hasOp = arg
    terms = list(terms)
    if len(terms) == 1 and hasOp: return terms[0]
    return makeApp(terms, attr)

def makeMacroApp(datum):
    def _makeMacroApp(arg, attr):
        terms, hasOp = arg
        datAt = SrcAttr(attr.streamName, attr.srcs, attr.start, attr.start)
        return makeApp(list(chain([(datum, toAttr(datAt))], terms)), attr)
    return _makeMacroApp

def newOperator(name, fixity, assoc, prec):
    return fixities[fixity](name, assoc, prec)

def tryMakeAtom(*args):
    try: return makeAtom(*args)
    except ParseError: return None, None
def isInfixOp(atom): return isinstance(atom[0], (InfixOp, InfixTightOp))

def unindented(ts): return (t for t in ts if t.ty != 'indentation')
class Datums: pass
openBraces = list('([{')
openBraces += ['#'+br for br in openBraces]
closeBraces = list(')]}')
openToCloseBraces = dict(zip(openBraces, 2*closeBraces))
class Parser:
    def __init__(self, opsTable):
        self.opsTable = opsTable
        self.brackets = {'(': maybeMakeApp}
        self.datums = Datums()
        self.setRhsSlice(None)
    def setRhsSlice(self, datum): self.datums.rhsSliceDatum = datum
    def addBracketDatums(self, bracketDatums):
        for brack, datum in bracketDatums:
            assert brack in openToCloseBraces
            self.brackets[brack] = makeMacroApp(datum)
    def parse(self, streamName, stream):
        return self.exprs(tokens(streamName, stream))
    def exprs(self, ts):
        ts = makeStream(iter(ts))
        for tok in ts:
            indent = tok.val
            assert tok.ty == 'indentation', (tok.ty, tok.attr)
            if indent < 0: break
            yield self.indentedExpr(indent, tok.attr, ts)
    def parseOps(self, ts):
        ts = makeStream(ts)
        rhs = []
        hasOp = False
        for term in ts:
            t, a = term
            if isinstance(t, Operator):
                hasOp = True
                rhs = t.parse(rhs, a, ts, self.datums)
            else: rhs.append(term)
        return rhs, hasOp
    def indentedExpr(self, i, a, ts):
        return maybeMakeApp((self.parseOps(self.indentedTerms(i,a,ts))[0],
                             True), a)
    def indentedTerms(self, indent, firstAttr, ts):
        subIndent = None
        for tok in ts:
            if tok.ty == 'indentation':
                if tok.val <= indent:
                    ts.put(tok) # parent has to handle this indent too
                    return
                else:
                    if subIndent is None: subIndent = tok.val
                    peek = next(ts)
                    atom = tryMakeAtom(self.opsTable, peek)
                    if isInfixOp(atom): yield atom
                    else:
                        ts.put(peek)
                        if subIndent > tok.val:
                            parseErr(tok.attr,
                                     'misaligned indentation; expected '+
                                     '%d or %d but found %d' %
                                     (subIndent, indent, tok.val))
                    yield self.indentedExpr(tok.val, tok.attr, ts)
            elif tok.ty == 'syntax':
                yield self.bracketedExpr(tok.val, tok.attr,
                                         ts.compose(unindented))
            else: yield makeAtom(self.opsTable, tok)
        parseErr(firstAttr, 'unexpected eof while parsing indented expr')
    def bracketedExpr(self, openBrace, attr, ts):
        makeExpr = self.brackets.get(openBrace)
        if makeExpr is None:
            if openBrace in closeBraces:
                parseErr(attr, 'unmatched %s'%openBrace)
            else: parseErr(attr, 'unknown syntax %s'%openBrace)
        closeBrace = openToCloseBraces.get(openBrace)
        return makeExpr(self.parseOps(self.bracketedTerms(closeBrace,
                                                          attr, ts)),
                        attr)
    def bracketedTerms(self, closeBrace, firstAttr, ts):
        for tok in ts:
            if tok.ty == 'syntax':
                if tok.val == closeBrace: return
                yield self.bracketedExpr(tok.val, tok.attr, ts)
            else: yield makeAtom(self.opsTable, tok)
        parseErr(firstAttr, 'unexpected eof while parsing bracketed expr')

def makeOperator(opsTable, name, attr):
    op = opsTable.get(EnvKey(name))
    if op is None: op = NullOp(name, symbol('none'), 0)
    return op

class Operator:
    def __init__(self, sym, assoc, prec):
        assert isSymbol(sym), sym
        assert type(prec) is int, prec
        assert isSymbol(assoc), assoc
        self.sym = sym
        self.assocRight = assoc is symbol('right') # todo: non-associative ops
        self.prec = prec
    def parse(self, lhs, attr, ts, dats): abstract

class NullOp(Operator): # undeclared op
    def parse(self, lhs, attr, ts, dats):
        if not lhs and ts.empty(): return [(self.sym, attr)]
        else: parseErr(attr, "unknown operator '%s'"%prettySymbol(self.sym))

class PrefixOp(Operator):
    def parse(self, lhs, attr, ts, dats):
        if ts.empty(): return lhs+[(self.sym, attr)] # slice
        t, a = next(ts)
        rhs = [(t,a)]
        if isinstance(t, Operator):
            if isinstance(t, PrefixOp): rhs = t.parse([], a, ts, dats)
            else: parseErr(a, 'unexpected operator while parsing prefix op')
        return lhs+[makeApp([(self.sym, attr)]+rhs)]

def makeReducedApp(terms): return maybeMakeApp((terms, True))

def makeInfixApp(sym, lhs, rhs, attr, dats):
    op = (sym, attr)
    if lhs:
        if rhs: return [makeApp([op,makeReducedApp(lhs),makeReducedApp(rhs)])]
        else: return [makeApp([op, makeReducedApp(lhs)])]
    elif rhs:
        datum = dats.rhsSliceDatum
        if datum is None: parseErr('rhs-slice handler is unspecified')
        return [makeApp([(datum, attr), op, makeReducedApp(rhs)])]
    else: return [op]

class InfixOp(Operator):
    def parse(self, lhs, attr, ts, dats):
        if ts.empty(): return makeInfixApp(self.sym, lhs, [], attr, dats)
        t, a = next(ts)
        rhs = [(t,a)]
        if isinstance(t, Operator):
            if isinstance(t, PrefixOp): rhs = t.parse([], a, ts, dats)
            else: parseErr(a, 'unexpected operator while parsing infix op')
        for term in ts:
            t, a = term
            if isinstance(t, Operator):
                if self.precLT(t): rhs = t.parse(rhs, a, ts, dats)
                else:
                    ts.put(term)
                    return makeInfixApp(self.sym, lhs, rhs, attr, dats)
            else: rhs.append(term)
        return makeInfixApp(self.sym, lhs, rhs, attr, dats)
    def precLT(self, op): return (isinstance(op, (PrefixOp, InfixTightOp))
                                  or (op.prec > self.prec) or
                                  ((op.prec == self.prec) and self.assocRight))

class InfixTightOp(Operator):
    def parse(self, lhs, attr, ts, dats):
        if lhs:
            rest = lhs[:-1]
            lhs = [lhs[-1]]
        else: rest = []
        if ts.empty(): return rest+makeInfixApp(self.sym, lhs, [], attr, dats)
        t, a = next(ts)
        rhs = [(t,a)]
        if isinstance(t, Operator):
            if isinstance(t, PrefixOp): rhs = t.parse([], a, ts, dats)
            else: parseErr(a, 'unexpected operator while parsing infix op')
        if not ts.empty():
            term = next(ts)
            t, a = term
            if isinstance(t, InfixTightOp) and self.precLT(t):
                rhs = t.parse(rhs, a, ts, dats)
            else: ts.put(term)
        return rest + makeInfixApp(self.sym, lhs, rhs, attr, dats)
    def precLT(self, op): return ((op.prec > self.prec) or
                                  ((op.prec == self.prec) and self.assocRight))

fixities = dict(prefix=PrefixOp, infixTight=InfixTightOp, infix=InfixOp)

def deepFromList(attr, seen=set()):
#    assert attr not in seen, attr
#    seen.add(attr)
    return attr, list(map(deepFromList, fromList(fromAttr(attr).subs)))

def _test(s):
    from io import StringIO
    ops = (
        ('$', 'prefix', symbol('left'), 5),
        ('!', 'prefix', symbol('left'), 5),
        ('.', 'infixTight', symbol('left'), 10),
        ('+', 'infix', symbol('left'), 5),
        ('-', 'infix', symbol('left'), 5),
        ('*', 'infix', symbol('left'), 6),
        ('->', 'infix', symbol('right'), 3),
        ('=', 'infix', symbol('right'), 2),
        )
    opsTable = Env()
    for op in ops:
        opName = symbol(op[0])
        opsTable.add(EnvKey(opName), newOperator(opName, *op[1:]))
    parser = Parser(opsTable); parser.addBracketDatums([('[', symbol('list'))])
    for t,a in parser.parse('syntax.test', StringIO(s)):
        print(pretty(t))
        print(deepFromList(a))

if __name__ == '__main__':
    _test('hello world\n  4+ 3\n\n  5 - 6\n  \nf 7-8+9 -10\n## comments\n\n')
    _test('hello world\n  4+ 3')
    _test('hello world\n  4+ ! 3 *5 + $7 + !')
    _test('hello world.tour\n  4+ ! 3 *5 + $7 + !')
    _test('hello world.tour\n  - 4+ ! 3 *5 + $7 + !')
    _test('1 * 2')
    _test('quote (1 . 2)')
    _test('abc [1 2 3]')
