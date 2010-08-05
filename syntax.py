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
from collections import namedtuple
import re

class ParseError(Exception): pass
def parseErr(src, msg): raise ParseError(src, msg)
nullTerm = unit
def makeIdent(_, s): # strip escapes
    sym = symbol('\\'.join(ss.replace('\\', '') for ss in s.split('\\\\')))
    if s == '_': sym = alias_new(sym) # each non-escaped underscore is unique
    return sym
def makeIdentOp(_, s): return makeIdent(s[1:-1])
def makeInt(_, s): return toInt(int(s)) # todo: Iu32, Is32, etc.
def makeFloat(_, s): return toFloat(float(s))
def makeChar(_, s): return toChar(eval(s))
def makeString(_, s): return toString(eval(s))
def makeOp(parser, s):
    sym = makeIdent(parser, s); op = parser.ctx.ops.get(EnvKey(sym))
    if op is None: return NullOp(sym)
    return op
def srcWrap_(src, term): return synclo_new(toCtx(nullCtx(src)), nil, term)
def srcWrap(parser, term): return srcWrap_(parser.stream.popRgn(), term)
SrcRgn = namedtuple('SrcRgn', 'name text start end')
SrcLoc = namedtuple('SrcLoc', 'row col')
def aggSrcs(srcs):
    assert not not srcs
    start = min(src.start for src in srcs); end = max(src.end for src in srcs)
    missing = '***MISSING TEXT***\n'; base = start.row
    name = srcs[0].name; text = [missing]*(end.row-start.row+1)
    for src in srcs:
        assert src.name == name, (name, src.name)
        text[src.start.row-base:src.end.row-base+1] = src.text
    for line in text:
        assert line is not missing
    return SrcRgn(name, text, start, end)
def makeExpr(terms, exprSrc=None):
    srcs = tuple(fromCtx(synclo_ctx(tm)).src for tm in terms)
    if not srcs: srcs = (exprSrc,)
    return srcWrap_(aggSrcs(srcs), toList(terms))
def makeExprNonSingle(terms, exprSrc=None):
    if len(terms) > 1: return makeExpr(terms, exprSrc)
    elif len(terms) == 1: return terms[0]
    return nullTerm
OpTerm = namedtuple('OpTerm', 'op term')
def mkTerm(f):
    def termMaker(parser, cs):
        tm = f(parser, cs)
        if isinstance(tm, Operator): tm = OpTerm(tm, srcWrap(parser, tm.sym))
        else: tm = srcWrap(parser, tm)
        return tm
    return termMaker
def makeTokClass(tokSpec): return (re.compile(tokSpec[0]), mkTerm(tokSpec[1]))
def makeTokClasses(tokSpecs): return [makeTokClass(c) for c in tokSpecs]
commentStr = '##'
operPat = '[~!@$%^&*=+|;:,.<>/?-]+'
identPat = r"([a-zA-Z_]|(\\.))([-]?(\w|(\\.)))*[!?]*[']*"
tokClassesNonDelimiter = makeTokClasses((
        (identPat, makeIdent),
        ('`%s`'%identPat, makeIdentOp),
        (r'-?(\d+\.\d+)([eE][+-]?\d+)?', makeFloat),
        (r'-?(0x)?\d+', makeInt),
        (r"'((\\.)|[^\\'])'", makeChar),
        (r'"((\\.)|[^\\"])*"', makeString),
        ))
tokClassesDelimiter = makeTokClasses((
        (operPat, makeOp),
        ))
tokClassesAll = tokClassesNonDelimiter+tokClassesDelimiter
def locRange(start, end):
    if start == end: return start, end
    if end.col != 0: return start, end
    return start, SrcLoc(end.row-1, -1)#max(start.row, end.row-1), 0)
def numRows(start, end):
    if start == end: return 0
    return end.row-start.row+1
class Stream:
    def __init__(self, name, ios, row=1, col=0):
        self.name = name; self.ios = ios; self.row = row; self.col = col
        self.lineBuf = None; self.lineHist = []; self.lenHist = None
        self.locHist = SrcLoc(row, col)
    def getln(self):
        if self.lineBuf is not None: line = self.lineBuf; self.lineBuf = None
        else: line = next(self.ios)
        if self.col == 0: self.lineHist.append(line)
        self.row+=1; self.lenHist = len(line)+self.col; self.col = 0
        return line
    def putln(self, line):
        if not line: return
        assert self.lenHist is not None
        assert self.lineBuf is None, self.lineBuf
        self.col = self.lenHist-len(line); self.lineBuf = line; self.row-=1
        if self.col == 0:
            assert self.lineHist, line
            self.lineHist.pop()
    def getch(self, num=1):
        line = self.getln(); self.putln(line[num:]); return line[:num]
    def putch(self, ch): line = ch+self.getln(); self.putln(line)
    def empty(self):
        try: self.putln(self.getln())
        except StopIteration: return True
        return False
    def popRgn(self):
        newLoc = SrcLoc(self.row, self.col); nlines = len(self.lineHist)
        rng = locRange(self.locHist, newLoc); nrows = numRows(*rng)
        assert ((nrows == nlines-1 and rng[0].col == rng[1].col)
                or nrows == nlines), (nlines, rng)
        src = SrcRgn(self.name, self.lineHist[:nrows], *rng)
        if self.col == 0: self.lineHist = []
        else: self.lineHist = [self.lineHist[-1]]
        self.locHist = newLoc; return src
def memoTrue(f):
    state = [False]
    def memo(*args):
        if not state[0] and f(*args): state[0] = True
        return state[0]
    return memo
class Parser:
    def __init__(self, ctx, stream):
        self.ctx = ctx; self.stream = stream
        self.indent = None; self.pendingTerm = None
    def parse(self):
        self.indent = self.skipSpace(0)
        while not self.stream.empty():
            term = self.term()
            if term is not nullTerm: yield term
    def delimit(self, cls=None):
        if cls is None or cls in tokClassesDelimiter:
            self.tokClasses = tokClassesAll
        else: self.tokClasses = tokClassesDelimiter
    def dispatch(self, ch=''):
        chs = ch+self.stream.getch(); proc = self.ctx.readers.get(chs)
        if proc is not None: return proc(self, chs)
        self.stream.putch(chs); return None
    def skipSpace(self, newlines=-1):
        sline = None
        while not sline:
            if self.stream.empty(): self.delimit(); return -1
            line = self.stream.getln(); sline = line.lstrip()
            if sline.startswith(commentStr): sline = ''
            if sline == '\\\n': sline = ''
            else: newlines += 1
        self.stream.putln(sline); self.stream.popRgn()
        diff = len(line)-len(sline)
        if newlines > 0 or diff > 0: self.delimit()
        if newlines > 0: return diff
    def expr(self, eoe, mkExpr):
        self.delimit(); terms = []; hasOp = False
        while not eoe():
            term = self.term()
            if termIs(term, Operator):
                terms = parseOp(term, self, terms, eoe); hasOp = True
            elif term is not nullTerm: terms.append(term)
        self.delimit();
        if hasOp: return makeExprNonSingle(terms)
        return mkExpr(terms, self.stream.popRgn())
    def indentedExpr(self, curIndent):
        @memoTrue
        def eoeIndented():
            if self.pendingTerm is not None: return False
            else:
                if self.indent is not None: indent = self.indent
                else: indent = self.skipSpace(); self.indent = indent
                if indent is None: return False
                else: return indent <= curIndent
        return self.expr(eoeIndented, makeExprNonSingle)
    def bracketedExpr(self, closeBracket):
        @memoTrue
        def eoeBracketed():
            if self.pendingTerm is not None: return False
            else:
                indent = self.skipSpace()
                if indent == -1: parseErr(None, 'unexpected end of stream')
                ch = self.stream.getch(len(closeBracket))
                if ch == closeBracket: return True
                else: self.stream.putch(ch); return False
        return self.expr(eoeBracketed, makeExpr)
    def putTerm(self, term):
        assert self.pendingTerm is None, self.pendingTerm
        self.pendingTerm = term
    def term(self):
        if self.pendingTerm is not None:
            term = self.pendingTerm; self.pendingTerm = None; return term
        if self.indent is not None:
            indent = self.indent; self.indent = None
            return self.indentedExpr(indent)
        term = self.dispatch()
        if term is not None: return term
        line = self.stream.getln()
        for tc in self.tokClasses:
            rxp, toTerm = tc; mtch = rxp.match(line)
            if mtch is not None:
                end = mtch.end(); self.stream.putln(line[end:])
                self.delimit(tc); return toTerm(self, line[:end])
        parseErr(line, 'term error') # todo
################################################################
# operators
def termIs(tm, cls): return isinstance(tm, OpTerm) and isinstance(tm.op, cls)
def parseOp(op, parser, terms, eoe):
    return op.op.parse(parser, op.term, terms, eoe)
class Operator:
    def __init__(self, sym, assoc, prec):
        assert isSymbol(sym), sym
        assert type(prec) is int, prec
        assert isSymbol(assoc), assoc
        assert any(symbol_eq(assoc, symbol(nm))
                   for nm in ('left', 'right', 'none'))
        self.sym = sym; self.prec = prec
        # todo: non-associative ops
        self.assocRight = symbol_eq(assoc, symbol('right'))
    def precLT(self, term): return self._precLT(term.op)
class NullOp(Operator): # undeclared op
    def __init__(self, sym): super().__init__(sym, symbol('none'), 0)
    def parse(self, parser, tm, lhs, eoe):
        if not lhs and eoe(): return [tm]
        else: parseErr(None, "unknown operator '%s'"%pretty(tm))
class PrefixOp(Operator):
    def parse(self, parser, tm, lhs, eoe):
        if eoe(): return lhs+[tm] # slice
        term = parser.term(); rhs = [term]
        if termIs(term, Operator):
            if termIs(term, PrefixOp): rhs = term.parse(parser, [], eoe)
            else: parseErr(None, 'unexpected operator while parsing prefix op')
        return lhs+[makeExpr([tm]+rhs)]
def infixTerms(op, lhs, rhs):
    if lhs:
        terms = [op, makeExprNonSingle(lhs)]
        if rhs: terms.append(makeExprNonSingle(rhs))
        return [makeExpr(terms)]
    elif rhs: parseErr(None, 'rhs-slice not yet supported')
    else: return [op]
class InfixOp(Operator):
    def parse(self, parser, tm, lhs, eoe):
        if eoe(): return infixTerms(tm, lhs, [])
        term = parser.term(); rhs = [term]
        if termIs(term, Operator):
            if termIs(term, PrefixOp): rhs = parseOp(term, parser, [], eoe)
            else: parseErr(None, 'unexpected operator while parsing infix op')
        while not eoe():
            term = parser.term()
            if termIs(term, Operator):
                if self.precLT(term): rhs = parseOp(term, parser, rhs, eoe)
                else:
                    parser.putTerm(term); return infixTerms(tm, lhs, rhs)
            else: rhs.append(term)
        return infixTerms(tm, lhs, rhs)
    def _precLT(self, op): return (isinstance(op, (PrefixOp, InfixTightOp))
                                   or (op.prec > self.prec) or
                                   ((op.prec == self.prec) and self.assocRight))
class InfixTightOp(Operator):
    def parse(self, parser, tm, lhs, eoe):
        if lhs: rest = lhs[:-1]; lhs = [lhs[-1]]
        else: rest = []
        if eoe(): return rest + infixTerms(tm, lhs, [])
        term = parser.term(); rhs = [term]
        if termIs(term, Operator):
            if termIs(term, PrefixOp): rhs = parseOp(term, parser, [], eoe)
            else: parseErr(None, 'unexpected operator while parsing infix op')
        if not eoe():
            term = parser.term()
            if termIs(term, InfixTightOp) and self.precLT(term):
                rhs = parseOp(term, parser, rhs, eoe)
            else: parser.putTerm(term)
        return rest + infixTerms(tm, lhs, rhs)
    def _precLT(self, op): return ((op.prec > self.prec) or
                                  ((op.prec == self.prec) and self.assocRight))
fixities = dict(prefix=PrefixOp, infixTight=InfixTightOp, infix=InfixOp)
def newOperator(name, fixity, assoc, prec):
    return fixities[fixity](name, assoc, prec)
################################################################
# standard dispatch
stdDispatchers = Env()
def dispAgain(parser, ch):
    f = parser.dispatch(ch)
    if f is None: parseErr(None, "invalid reader dispatch '%s'"%ch)
    return f
def addDisp(chs, f, dispatchers):
    while chs:
        disp = dispatchers.get(chs)
        assert disp is None or disp is dispAgain, disp
        dispatchers.add(chs, f); chs = chs[:-1]; f = dispAgain
def addStdDisp(chs, f): return addDisp(chs, f, stdDispatchers)
def stddisp(chs):
    def mkDisp(f): addStdDisp(chs, f); return f
    return mkDisp
@stddisp('(')
def parenExpr(parser, ch): return parser.bracketedExpr(')')
@stddisp(commentStr)
def commentLine(parser, ch):
    parser.stream.getln(); parser.stream.popRgn(); parser.stream.putln('\n')
    return nullTerm
################################################################
# testing
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
        (':', 'infix', symbol('right'), 4),
        )
    opsTable = Env()
    for op in ops:
        opName = symbol(op[0])
        opsTable.add(EnvKey(opName), newOperator(opName, *op[1:]))
    FakeCtx = namedtuple('FakeCtx', 'ops readers')
    parser = Parser(FakeCtx(opsTable, stdDispatchers),
                    Stream('test', StringIO(s)))
    for src, dat in parser.parse(): print(src, ':\n', pretty(dat))

if __name__ == '__main__':
    _test(open('boot.chive').read())
    # _test('hello world')
    # _test('1 * 2')
    # _test('quote (1 . 2)')
    # _test('hello world\n  4+ 3')
    # _test('hello world\n  4+ ! 3 *5 + $7 + !')
    # _test('hello world.tour\n  4+ ! 3 *5 + $7 + !')
    # _test('hello world\n  4+ 3\n\n  5 - 6\n  \nf 7-8+9 -10\n## comments\n\n')
#    _test('hello world.tour\n  - 4+ ! 3 *5 + $7 + !') # todo: rhs-slice
