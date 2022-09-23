"""Lambek parser"""

from collections import defaultdict


semantictypelist = {
    'dp': 'e',
    's': 't',
    'n': '(e;t)'
}


# a few helper functions
def findbracketpair(inputstring, bracketindex):
    searchindex = bracketindex
    if inputstring[bracketindex] == '(':
        bracketscore = 1
        while bracketscore > 0:
            searchindex += 1
            if inputstring[searchindex] == '(':
                bracketscore += 1
            elif inputstring[searchindex] == ')':
                bracketscore -= 1
    elif inputstring[bracketindex] == ')':
        bracketscore = -1
        while bracketscore < 0:
            searchindex -= 1
            if inputstring[searchindex] == '(':
                bracketscore += 1
            elif inputstring[searchindex] == ')':
                bracketscore -= 1
    else:
        raise Exception('Parenthesis not found, instead found: {}'.format(inputstring[bracketindex]))
    return searchindex


def stripbrackets(inputstring):
    if inputstring[0] == '(' and inputstring[-1] == ')' and findbracketpair(inputstring, 0) == len(inputstring) - 1:
        return inputstring[1:-1]
    else:
        return inputstring


# elimination rules, returns None if cannot combine
def leftelimination(type1, type2):
    if type2.slashtype == 'left':
        if type2.left.typestring == type1.typestring:
            return type2.right


def rightelimination(type1, type2):
    if type1.slashtype == 'right':
        if type1.right.typestring == type2.typestring:
            return type1.left


def elimination(left, right):
    result = leftelimination(left.syntactictype, right.syntactictype)
    if result is not None:
        return result, functionapplication(right.denotation, left.denotation)
    else:
        result = rightelimination(left.syntactictype, right.syntactictype)
        if result is not None:
            return result, functionapplication(left.denotation, right.denotation)
        else:
            return None, None


# takes in denotation
def functionapplication(function, argument):
    if function.semantictype.argument == argument.semantictype:
        return Denotation(function.semantictype.goal, function.function.replace(function.variable, argument.string))
    else:
        raise Exception("Function application cannot be applied.")


class SyntacticType:

    def __init__(self, inputstring):
        self.typestring = stripbrackets(inputstring.replace(' ', ''))
        self.isfunction = '\\' in self.typestring or '/' in self.typestring
        self.slashindex = None
        self.slashtype = None

        # right now, assumes that everything is properly bracketed!!
        if self.isfunction:
            searchindex = 0
            while self.slashindex is None:
                if self.typestring[searchindex] == '(':
                    searchindex = findbracketpair(self.typestring, searchindex) + 1
                elif self.typestring[searchindex] == '\\':
                    self.slashindex = searchindex
                    self.slashtype = 'left'
                elif self.typestring[searchindex] == '/':
                    self.slashindex = searchindex
                    self.slashtype = 'right'
                else:
                    searchindex += 1
                if searchindex >= len(self.typestring):
                    raise Exception("Invalid type: {}".format(self.typestring))

            self.left = SyntacticType(self.typestring[:self.slashindex])
            self.right = SyntacticType(self.typestring[self.slashindex + 1:])

    def print(self):
        if self.isfunction:
            self.left.print()
            if self.slashtype == 'left':
                print('\\')
            else:
                print('/')
            self.right.print()
        else:
            print(self.typestring)

    def __repr__(self):
        return self.typestring


class Semantictype:

    def __init__(self, syntactictype):
        self.syntactictype = syntactictype

        if not self.syntactictype.isfunction:
            self.typestring = semantictypelist[self.syntactictype.typestring]
        else:
            if self.syntactictype.slashtype == 'left':
                self.argument = Semantictype(self.syntactictype.left)
                self.goal = Semantictype(self.syntactictype.right)
            else:
                self.argument = Semantictype(self.syntactictype.right)
                self.goal = Semantictype(self.syntactictype.left)
            self.typestring = '(' + self.argument.typestring + ',' + self.goal.typestring + ')'

    def __repr__(self):
        return self.typestring

    def __eq__(self, other):
        return self.typestring == other.typestring


class Denotation:

    def __init__(self, semantictype, inputstring):

        self.semantictype = semantictype
        self.string = inputstring
        self.satiated = 'L' not in inputstring
        if not self.satiated:
            lindex = inputstring.index('L')
            dotindex = inputstring.index('.')
            self.variable = inputstring[lindex + 1:dotindex]
            self.function = inputstring[dotindex + 1:]
        else:
            self.variable = None
            self.function = None

    def __repr__(self):
        return self.string


class Lexicon:

    def __init__(self, lexiconstring):
        self.entrytypes = defaultdict(SyntacticType)
        self.entrydenotations = defaultdict(Denotation)
        for entry in lexiconstring.split('\n'):
            colonindex = entry.index(':')
            dashindex = entry.index('-')
            entryname = entry[:colonindex].strip()
            self.entrytypes[entryname] = SyntacticType(entry[colonindex + 1:dashindex])
            self.entrydenotations[entryname] = Denotation(Semantictype(self.entrytypes[entryname]),
                                                          entry[dashindex + 1:].strip())

    def print(self):
        for entry in self.entrytypes:
            print(entry, ':', self.entrytypes[entry], '-', self.entrydenotations[entry])


class Constituent:

    def __init__(self, syntactictype, denotation, startposition, endposition=None, subconstituents=None):
        self.syntactictype = syntactictype
        self.semantictype = Semantictype(self.syntactictype)
        self.denotation = denotation
        self.start = startposition
        if endposition is None:
            self.end = self.start + 1
        else:
            self.end = endposition
        self.length = self.end - self.start
        if subconstituents is None:
            self.subconstituents = []
        else:
            self.subconstituents = subconstituents

    def print(self):
        print(self.syntactictype, self.semantictype, self.denotation, str(self.start), ":", str(self.end))

    def returnchart(self, layer=0, lines=None, maxwordlength=14):
        if lines is None:
            lines = []
        dashlength = (maxwordlength + 1) * self.length - 1 - len(self.syntactictype.typestring)
        if len(lines) < layer + 1:
            lines.append('')
        while len(lines[layer]) < self.start * (maxwordlength + 1):
            lines[layer] += ' ' * (maxwordlength + 1)
        lines[layer] += self.syntactictype.typestring + '-' * dashlength + ' '
        for subconstituent in self.subconstituents:
            subconstituent.returnchart(layer + 1, lines, maxwordlength)
        if layer == 0:
            return lines

    def __repr__(self):
        return self.syntactictype.typestring + ' ' + self.semantictype.typestring + ' ' + self.denotation.string


class Chart:

    def __init__(self, lexicon, sentence):
        self.lexicon = lexicon
        self.words = sentence.split(' ')
        self.agenda = []
        self.constituents = []
        self.position = 0

        while self.position < len(self.words):
            self.interpretword()
            while len(self.agenda) > 0:
                self.addconstituent(self.agenda[0])
                self.agenda.pop(0)
            self.position += 1

    def interpretword(self):
        self.agenda.append(Constituent(self.lexicon.entrytypes[self.words[self.position]],
                                       self.lexicon.entrydenotations[self.words[self.position]], self.position))

    def addconstituent(self, constituent):
        # add constituent
        self.constituents.append(constituent)

        '''are arcs needed?'''

        # try adding constituent immediately (every rule is binary branching)
        # calling it an arc but it is really just a constituent, since a single constituent is one constituent
        # away from being a completed arc
        for arc in self.constituents:
            if arc.end == constituent.start:
                syntacticcombo, denotationcombo = elimination(arc, constituent)
                if syntacticcombo is not None:
                    self.agenda.append(Constituent(syntacticcombo, denotationcombo, arc.start, constituent.end, [arc, constituent]))

    def printconstituents(self):
        for constituent in self.constituents:
            constituent.print()

    def printstructure(self, maxwordlength=14):
        for constituent in self.constituents:
            if constituent.syntactictype.typestring == 's' and constituent.start == 0 and \
                    constituent.end == len(self.words):
                chartstructure = constituent.returnchart(0, [], maxwordlength)
                for line in chartstructure:
                    print(line)
                for word in self.words:
                    print(word + ' ' * (maxwordlength - len(word)), end=' ')
                print('\n')


lexiconsource = '''john : dp - j
snores: dp\\s - L1.snore(1)
walter : dp - w
kevin : dp - k
knows : (dp\\s)/dp - L1.L2.know(2,1)
saw : (dp\\s)/dp - L1.L2.see(2,1)
saidthat : (dp\\s)/s - L1.L2.said(2,1)
knowsthat : (dp\\s)/s - L1.L2.know(2,1)
faintly : (dp\\s)\\(dp\\s) - L1.faintly(1)
everyone : s/(dp\\s) - L1.Ax:1(x)&person(x)'''
# TODO: add a way to check if function application still applies (multiple times) ex. everyone
# TODO: add a global variable counter to avoid alpha conversion


testlexicon = Lexicon(lexiconsource)
# testlexicon.print()

testchart = Chart(testlexicon, 'everyone knowsthat kevin snores faintly')
testchart.printstructure(15)
testchart.printconstituents()

testchart2 = Chart(testlexicon, 'kevin snores faintly')
testchart2.printstructure(15)
testchart2.printconstituents()

