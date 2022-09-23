"""Parser using Sequent Calculus

Use chart.printstructure() for derivations. If any derivation is found, True is printed; if none, then False.
Any boxes in the derivation correspond to multiple proofs for the same sequent."""
# TODO: define variables for syntactic categories, like ditransitive

from collections import defaultdict
import itertools

language = 'english'
lexiconfilename = 'lexicon/' + language + '_lexicon.txt'
sentencefilename = 'sentences/' + language + '_sentences.txt'


varcounter = 0  # counter used to uniquely name syntactic variables (for abstraction)
qrlimit = 1  # maximum number of times qr can be used in a branch of a derivation
cooldownperiod = 2  # how many lines must be between abstraction out and in
semvarcounter = 0  # counter to uniquely name semantic variables
uniquedenotations = True  # remove a denotation if it is equivalent to another


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


def cool(number):
    if number > 0:
        return number - 1
    else:
        return 0


def newsemanticvariable():
    global semvarcounter
    semvarcounter += 1
    return semvarcounter


class SyntacticType:

    def __init__(self, inputstring):
        self.typestring = stripbrackets(inputstring.replace(' ', ''))
        self.isfunction = '\\' in self.typestring or '/' in self.typestring
        self.isgap = 'l' in self.typestring or 'v' in self.typestring
        self.slashindex = None
        self.slashtype = None
        self.gaptype = None
        self.varname = None

        # right now, assumes that everything is properly bracketed!
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

            if self.slashtype == 'right':
                self.top = self.left
                self.bottom = self.right
            else:
                self.top = self.right
                self.bottom = self.left

        if self.isgap:
            global varcounter
            if 'l' in self.typestring:
                self.gaptype = 'lambda'
                varcounter += 1
            else:
                self.gaptype = 'variable'
            self.varname = str(varcounter)
            self.typestring += self.varname

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

    def __eq__(self, other):
        if not (self.isfunction and other.isfunction):
            return self.typestring == other.typestring
        else:
            return self.left == other.left and self.right == other.right


class Denotation:

    # if one argument, denotation is simple
    # if two arguments, denotation is inputstring as function, and replacer as argument
    # if three arguments, denotation is inputstring as base, with replacer replacing replacee wherever replacee occurs
    # inputstring should be str, replacer and replacee should be denotations
    def __init__(self, inputstring, replacer=None, replacee=None):
        if inputstring[0] == '[' and inputstring[-1] == ']':
            self.string = inputstring[1:-1]
        else:
            self.string = inputstring
        self.denotationtype = 'simple'
        self.simplification = None
        self.reducedform = None
        self.body = self.lambdavar = self.replacer = self.replacee = None

        if replacer is not None:
            # replacer is argument to function

            self.body = Denotation(self.string)
            self.replacer = replacer

            if replacee is None:
                if self.body.denotationtype == 'lambda':
                    self.string = self.body.body.string.replace(self.body.lambdavar, str(self.replacer))
                    self.simplification = Denotation(self.string)
                else:
                    self.string = str(self.body) + '(' + str(self.replacer) + ')'

            # replacee is to be replaced by replacer
            else:
                # replacement

                self.replacee = replacee
                if str(replacee) in self.string:
                    self.string = self.string.replace(str(replacee), str(replacer))
                    self.simplification = Denotation(self.string)
                else:
                    self.string += '[' + str(replacer) + '/' + str(replacee) + ']'

        # if denotation is a lambda expression
        elif self.string[0] == 'L':
            self.denotationtype = 'lambda'
            dotindex = self.string.index('.')
            varname = self.string[1:dotindex]

            # variable numbers are surrounded with < > to prevent incorrect replacement
            # such as 'v2' being found in 'v23'
            if varname[0] == '<' and varname[-1] == '>':
                varindex = self.string.find(varname, dotindex)
                # TODO: IF YOU REPLACE FIND WITH INDEX, CREATES ERROR. WHY?
                # eta equivalence
                if self.string[varindex - 1] == '(' and varindex + len(varname) + 1 == len(self.string):
                    self.simplification = Denotation(self.string[dotindex+1:varindex-1])
                else:
                    self.lambdavar = varname
                    self.body = Denotation(self.string[dotindex + 1:])
            else:
                self.lambdavar = '<' + str(newsemanticvariable()) + '>'
                self.body = Denotation(self.string[dotindex + 1:].replace(varname, self.lambdavar))
                self.string = 'L' + self.lambdavar + '.' + str(self.body)

        # if denotation is a semantic variable, assign it a unique number
        elif self.string == 'var':
            self.denotationtype = 'variable'

            self.body = None
            self.string = '<' + str(newsemanticvariable()) + '>'

        if self.simplification is not None:
            if self.simplification.reducedform is None:
                self.reducedform = self.simplification
            else:
                self.reducedform = self.simplification.reducedform

    def __repr__(self):
        if self.reducedform is not None:
            return str(self.reducedform)
        else:
            return self.string

    def __eq__(self, other):
        if self.string == other.string:
            return True
        elif '<' in self.string:
            selfreducedstring = reducestring(self.string)
            otherreducedstring = reducestring(other.string)
            return selfreducedstring == otherreducedstring
        else:
            return False


def reducestring(string):
    reducedstring = string
    reducedvarcounter = 0
    while '<' in reducedstring:
        leftindex = reducedstring.find('<')
        rightindex = reducedstring.find('>', leftindex)
        varnumber = reducedstring[leftindex + 1:rightindex]
        reducedstring = reducedstring.replace('<' + varnumber + '>', '{' + str(reducedvarcounter) + '}')
        reducedvarcounter += 1
    return reducedstring


# define lexicon as a string, one entry per line. entries are of the form:
# word : type - denotation
class Lexicon:

    def __init__(self, lexiconstring):
        self.entrytypes = defaultdict(list)
        self.denotations = defaultdict(list)
        for entryline in lexiconstring.split('\n'):
            entry = entryline.replace(' ', '')
            if entry is not '' and entry[0] is not '#':
                colonindex = entry.index(':')
                dashindex = entry.index('-')
                entryname = entry[:colonindex].strip()
                self.entrytypes[entryname].append(SyntacticType(entry[colonindex + 1: dashindex].strip()))
                self.denotations[entryname].append(entry[dashindex + 1:].strip())

    def print(self):
        for entry in self.entrytypes:
            print(entry, ':', self.entrytypes[entry], '-', self.denotations[entry])


class Constituent:

    def __init__(self, syntactictype, denotation):
        self.syntactictype = syntactictype
        self.denotation = denotation

    def print(self):
        print(self.syntactictype)

    def __repr__(self):
        return repr(self.syntactictype)


# a list of constituents and the goal type
class Sequence:

    def __init__(self, constituentlist, goaltype, rule, qrcount=0, cooldown=0):
        self.constituents = constituentlist
        self.goal = goaltype
        self.subtrees = []
        self.isvalid = False
        self.denotations = []
        self.ruleused = rule
        self.qrcount = qrcount
        self.cooldown = cooldown
        # print(self.constituents)

        # check axiom
        if len(self.constituents) == 1 and self.constituents[0].syntactictype == self.goal and not self.goal.isfunction:
            # apply axiom
            self.isvalid = True
            self.adddenotation(self.constituents[0].denotation)
        elif len(self.constituents) == 0:
            self.isvalid = False
        else:

            # check right rules
            if self.goal.isfunction:
                # apply right rules
                newdenotation = Denotation('var')
                if self.goal.slashtype == 'left':
                    # apply right backslash
                    subsequence = Sequence([Constituent(self.goal.left, newdenotation)] + self.constituents,
                                           self.goal.right, '\\R', self.qrcount, cool(self.cooldown))
                else:
                    # apply right slash
                    subsequence = Sequence(self.constituents + [Constituent(self.goal.right, newdenotation)],
                                           self.goal.left, '/R', self.qrcount, cool(self.cooldown))
                if subsequence.isvalid:
                    self.subtrees.append([subsequence])
                    self.isvalid = True
                    for denotation in subsequence.denotations:
                        self.adddenotation(Denotation('L' + str(newdenotation) + '.' + str(denotation)))

            # check left rules
            for counter in range(len(self.constituents)):
                constituent = self.constituents[counter]
                if constituent.syntactictype.isfunction:
                    if constituent.syntactictype.slashtype == 'left':
                        # apply left backslash
                        for i in range(counter - 1, -1, -1):
                            subsequence1 = Sequence(self.constituents[i:counter], constituent.syntactictype.left, '\\L',
                                                    self.qrcount, cool(self.cooldown))
                            if subsequence1.isvalid:
                                newdenotation = Denotation('var')
                                subsequence2 = Sequence(self.constituents[0:i] +
                                                        [Constituent(constituent.syntactictype.right, newdenotation)] +
                                                        self.constituents[counter + 1:], self.goal, '\\L', self.qrcount,
                                                        cool(self.cooldown))
                                if subsequence2.isvalid:
                                    self.subtrees.append([subsequence1, subsequence2])
                                    self.isvalid = True
                                    for denotation2 in subsequence2.denotations:
                                        for denotation1 in subsequence1.denotations:
                                            self.adddenotation(
                                                Denotation(str(denotation2),
                                                           Denotation(str(constituent.denotation), denotation1),
                                                           newdenotation))
                    else:
                        # apply left slash
                        for i in range(counter + 1, len(self.constituents), 1):
                            subsequence1 = Sequence(self.constituents[counter + 1:i + 1],
                                                    constituent.syntactictype.right, '/L', self.qrcount,
                                                    cool(self.cooldown))
                            if subsequence1.isvalid:
                                newdenotation = Denotation('var')
                                subsequence2 = Sequence(self.constituents[:counter] +
                                                        [Constituent(constituent.syntactictype.left, newdenotation)] +
                                                        self.constituents[i + 1:], self.goal, '/L', self.qrcount,
                                                        cool(self.cooldown))
                                if subsequence2.isvalid:
                                    self.subtrees.append([subsequence1, subsequence2])
                                    self.isvalid = True
                                    for denotation2 in subsequence2.denotations:
                                        for denotation1 in subsequence1.denotations:
                                            self.adddenotation(
                                                Denotation(str(denotation2),
                                                           Denotation(str(constituent.denotation), denotation1),
                                                           newdenotation))

            # check qr rules
            if self.qrcount < qrlimit:
                for counter in range(len(self.constituents)):
                    # only try QR on functions
                    constituent = self.constituents[counter]
                    if counter < len(self.constituents) - 1:
                        nextconstituent = self.constituents[counter + 1]
                    else:
                        nextconstituent = constituent
                    if constituent.syntactictype.isfunction and \
                            nextconstituent.syntactictype.gaptype is not 'lambda':
                        # and constituent.syntactictype.bottom.isfunction ---add this for quantifier types
                        # ensure that you don't abstract a term twice in a row (may cause problems??)
                        # checks whether the next constituent is a lambda (which would indicate abstraction already)
                        subsequence = Sequence([constituent, Constituent(SyntacticType('l'), Denotation('l'))] +
                                               self.constituents[:counter] +
                                               [Constituent(SyntacticType('v'), Denotation('v'))] +
                                               self.constituents[counter + 1:], self.goal, 'ABS out',
                                               self.qrcount + 1, cooldownperiod)
                        if subsequence.isvalid:
                            self.subtrees.append([subsequence])
                            self.isvalid = True
                            for denotation in subsequence.denotations:
                                self.adddenotation(denotation)

            if self.cooldown == 0 and len(self.constituents) > 2:
                for counter in range(len(self.constituents)):
                    if self.constituents[counter].syntactictype.gaptype == 'lambda' and counter > 0:
                        lambdaname = self.constituents[counter].syntactictype.varname
                        # it seems that the way I programmed the line below only allows abstraction in when
                        # lambda is in 2nd position
                        # note: adding '''self.constituents[:counter - 1] + ''' after in fixes it i think?
                        # TODO: but do we need to? it seems to add extra derivations...
                        # perhaps not needed if only using top-level abstraction
                        # print('full: ', self.constituents)
                        # print('selection: ', self.constituents[:counter - 1] + self.constituents[counter + 1:])
                        subsequence = Sequence([self.constituents[counter - 1]
                                                if constituent.syntactictype.typestring == 'v' + lambdaname
                                                else constituent for constituent in self.constituents[:counter - 1] +
                                                self.constituents[counter + 1:]],
                                               self.goal, 'ABS in', self.qrcount, 0)
                        if subsequence.isvalid:
                            self.subtrees.append([subsequence])
                            self.isvalid = True
                            for denotation in subsequence.denotations:
                                self.adddenotation(denotation)

    def adddenotation(self, denotation):
        if uniquedenotations:
            denotationexist = False
            for denotationtocheck in self.denotations:
                if denotationtocheck == denotation:
                    denotationexist = True
            if not denotationexist:
                self.denotations.append(denotation)
        else:
            self.denotations.append(denotation)

    def printstructure(self, layer=0, noindent=False):
        if not noindent:
            print('    ' * layer, end=' ')
        print(self, '   by', self.ruleused, len(self.denotations), self.denotations)
        for subtree in self.subtrees:
            if len(self.subtrees) > 1:
                print('    ' * (layer + 1), '--------')
            for subsequence in subtree:
                if len(self.subtrees) > 1:
                    print('    ' * (layer + 1), '|', end='')
                    subsequence.printstructure(layer + 1, True)
                else:
                    subsequence.printstructure(layer + 1)
            if len(self.subtrees) > 1:
                print('    ' * (layer + 1), '--------')

    def __repr__(self):
        returnstring = ''
        for item in self.constituents:
            returnstring += repr(item.syntactictype) + ' '
        returnstring += '⊦ ' + repr(self.goal)
        return returnstring


class Chart:

    def __init__(self, lexicon, sentence, goaltype=None):

        self.lexicon = lexicon
        self.words = sentence.split(' ')
        if goaltype is None:
            self.goaltype = SyntacticType('s')
        else:
            self.goaltype = goaltype
        self.constituents = []
        self.basesequences = []
        self.isvalid = False

        for word in self.words:
            wordtypes = self.lexicon.entrytypes[word]
            denotations = self.lexicon.denotations[word]
            self.constituents.append([])
            for i in range(len(wordtypes)):
                self.constituents[-1].append(Constituent(wordtypes[i], Denotation(denotations[i])))

        self.agenda = itertools.product(*self.constituents)
        for constituentlist in self.agenda:
            testbasesequence = Sequence(list(constituentlist), self.goaltype, 'LEX')
            if testbasesequence.isvalid:
                self.basesequences.append(testbasesequence)
                self.isvalid = True

    def printstructure(self):
        denotationlist = []
        for basesequence in self.basesequences:
            basesequence.printstructure()
            print(str(self), len(basesequence.denotations), basesequence.denotations)
            denotationlist += basesequence.denotations
        print(str(self), 'TOTAL:', len(denotationlist), denotationlist)
        # NOTE: this does not (yet) reduce duplicate denotations

    def printsentence(self):
        print(repr(self))

    def __repr__(self):
        return ' '.join(self.words)


lexiconsource = Lexicon(open(lexiconfilename, 'r').read())
sentencelist = open(sentencefilename, 'r').read().split('\n')

for line in sentencelist:
    if line[-1] == '?' or line[-1] == '？':
        chart = Chart(lexiconsource, line[:-1], SyntacticType('q'))
    else:
        chart = Chart(lexiconsource, line)
    print(chart, '  ', chart.isvalid)
    chart.printstructure()
