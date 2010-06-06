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
nullTerm = (object(), object())
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
    sym = makeIdent(parser, s); op = parser.ops.get(EnvKey(sym))
    if op is None: return NullOp(sym)
    return op
def makeExpr(terms, exprSrc=None):
    if terms: srcs, dats = list(zip(*terms))
    else: srcs, dats = (), ()
    return SrcTerm(exprSrc, srcs), toList(dats)
def makeExprNonSingle(terms, exprSrc=None):
    if len(terms) > 1: return makeExpr(terms, exprSrc)
    elif len(terms) == 1: return terms[0]
    return nullTerm
def mkTerm(f):
    def termMaker(parser, cs):
        return (SrcTerm(parser.stream.popRgn(), ()), f(parser, cs))
    return termMaker
def makeTokClass(tokSpec): return (re.compile(tokSpec[0]), mkTerm(tokSpec[1]))
def makeTokClasses(tokSpecs): return [makeTokClass(c) for c in tokSpecs]
operPat = '[~!@$%^&*\\=+|;:,.<>/?-]+'
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
SrcRgn = namedtuple('SrcRgn', 'name lines start end')
SrcTerm = namedtuple('SrcTerm', 'rgn sub')
class Stream:
    def __init__(self, name, ios, row=1, col=0):
        self.name = name
        self.ios = ios; self.lineBuf = None; self.row = row; self.col = col
        self.lenHist = None; self.lineHist = []; self.locHist = (row, col)
    def getln(self, default=None):
        if self.lineBuf is not None: line = self.lineBuf; self.lineBuf = None
        elif default is not None: line = default
        else: line = next(self.ios); self.lineHist.append(line)
        self.row+=1; self.lenHist = len(line)+self.col; self.col = 0
        return line
    def putln(self, line):
        if not line: return
        assert self.lenHist is not None
        assert self.lineBuf is None, self.lineBuf
        self.col = self.lenHist-len(line); self.lineBuf = line; self.row-=1
    def getch(self): line = self.getln(); self.putln(line[1:]); return line[0]
    def putch(self, ch): line = ch+self.getln(''); self.putln(line)
    def empty(self):
        try: self.putln(self.getln())
        except StopIteration: return True
        return False
    def popRgn(self):
        newLoc = (self.row, self.col)
        src = SrcRgn(self.name, ''.join(self.lineHist), self.locHist, newLoc)
        if self.lineBuf is None: self.lineHist = []
        else: self.lineHist = self.lineHist[-1:]
        self.locHist = newLoc; return src
def memoTrue(f):
    state = [False]
    def memo(*args):
        if not state[0] and f(*args): state[0] = True
        return state[0]
    return memo
class Parser:
    def __init__(self, ops, dispatchers, stream):
        self.ops = ops; self.dispatchers = dispatchers; self.stream = stream
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
        chs = ch+self.stream.getch(); proc = self.dispatchers.get(chs)
        if proc is not None: return proc(self, chs)
        self.stream.putch(chs); return None
    def skipSpace(self, newlines=-1):
        sline = None
        while not sline:
            if self.stream.empty(): self.delimit(); return -1
            self.stream.popRgn()
            line = self.stream.getln(); sline = line.lstrip()
            if sline == '\\\n': sline = ''
            else: newlines += 1
        self.stream.putln(sline); diff = len(line)-len(sline)
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
            if self.indent is not None: indent = self.indent
            else: indent = self.skipSpace(); self.indent = indent
            if indent is None: return False
            return indent <= curIndent
        return self.expr(eoeIndented, makeExprNonSingle)
    def bracketedExpr(self, closeBracket):
        @memoTrue
        def eoeBracketed():
            if self.pendingTerm is not None: return False
            indent = self.skipSpace()
            if indent == -1: parseErr(None, 'unexpected end of stream')
            ch = self.stream.getch()
            if ch == closeBracket: return True
            self.stream.putch(ch); return False
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
def termIs(tm, cls): return isinstance(tm[1], cls)
def parseOp(op, parser, terms, eoe):
    src, op = op; return op.parse(parser, [src, op.sym], terms, eoe)
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
    def precLT(self, term): return self._precLT(term[1])
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
stdDispatchers = {}
def dispAgain(parser, ch):
    f = parser.dispatch(ch)
    if f is None: parseErr(None, "invalid reader dispatch '%s'"%ch)
    return f
def addStdDisp(chs, f):
    while chs:
        assert chs not in stdDispatchers or stdDispatchers[chs] is dispAgain
        stdDispatchers[chs] = f; chs = chs[:-1]; f = dispAgain
def stddisp(chs):
    def mkDisp(f): addStdDisp(chs, f); return f
    return mkDisp
@stddisp('(')
def parenExpr(parser, ch): return parser.bracketedExpr(')')
@stddisp('##')
def commentLine(parser, ch):
    parser.stream.getln(); parser.stream.popRgn(); parser.stream.putln('\n')
    return nullTerm
def stdParser(ops, stream): return Parser(ops, stdDispatchers.copy(), stream)
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
    parser = Parser(opsTable, stdDispatchers, Stream('test', StringIO(s)))
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
