#!/usr/bin/env python
import sys, io, re, math, random
from collections import deque
from tkinter import Tk, Frame, Button, Checkbutton, Scale, Entry, BOTH, Canvas


###    DFA STUFF    ##########################################################

class State(object):
    """ A particular DFA state.
    Members:
            name:        a string containing the name of the State;
            accepting:   a boolean, whether the state accepts or not;
        transitions: a map from alphabet symbols to the names of states. """

    # We allow stateNames not to be provided in order to facilitate the
    # iterative construction of a machine where the final set of states is not
    # known until we are done building states
    def __init__(self, name, accepting, transitions, alphabet, stateNames=None):
        self.name = name
        self.accepting = accepting

        # Require this to be a state of a DFA, in particular.
        if sorted(alphabet) != sorted(transitions.keys()):
            raise ValueError("Each state of a DFA requires exactly one transition for each symbol in the alphabet.")
        if stateNames is not None:
            for stateName in transitions.values():
                if stateName not in stateNames:
                    raise ValueError("Transition to state \"" + stateName + "\" not in machine.")
        self.transitions = transitions

    def transition(self, symbol):
        """ Transitions take a symbol and return the name of the state to transition to. """

        if symbol not in self.transitions.keys():
            raise ValueError("Symbol \"" + symbol + "\" not an available transition from state \"" + self.name + "\".")
        else:
            return self.transitions[symbol]

    def copy(self):
        return State(self.name, self.accepting, dict(self.transitions), list(self.transitions.keys()))


class Error(object):
    """ Defines a non-accepting error state which transitions to itself on all input. """

    def __init__(self):
        self.name = "_ERR_"
        self.accepting = False

    def transition(self, symbol):
        """ Transition to self on all input. """
        return self.name


class DFA(object):
    """ A DFA.
        Members:
            states:     a map from state names to State objects;
            startName:  the name of the start state;
            alphabet:   a list of the strings which compose the alphabet. Symbols can be multiple characters long. """

    def __init__(self, states, startName, alphabet):
        self.states = states
        self.alphabet = alphabet

        if startName not in states:
            raise ValueError("Start state \"" + startName + "\" is not a state of the machine.")
        self.startName = startName

    def checkString(self, s, verbose=True):
        """ Run this DFA on the given string. Returns true if the string is accepted, false otherwise.
            Parameters:
                s:          the string to process;
                verbose:    if True, an execution trace is printed; if False, the result is returned silently. """

        current = self.states[self.startName]

        # Verbose is the same as non-verbose, save for printing the trace.
        # For each character in the input string, follow the appropriate transition until string exhausted.
        # If a transition fails, e.g. if the current symbol is not in the alphabet, go to an inescapable error state.
        if not verbose:
            for c in s:
                try:
                    current = self.states[current.transition(c)]
                except ValueError:
                    current = self.error()
        else:
            # length of symbol and state names for formatting purposes.

            maxStN = max([len(state) for state in self.states])
            maxSyN = 0
            if len(self.alphabet) != 0:
                maxSyN = max([len(c) for c in self.alphabet])

            for i in range(len(s)):
                print(s[:i] + " "*(len(s) - i + 2) + current.name + " "*(maxStN - len(current.name)), end="")
                print(" -- " + s[i] + " "*(maxSyN - len(s[i])) + " --> ", end="")

                # If a character not in the alphabet is tried, transition to an inescapable error state
                # which self-loops on all input.
                try:
                    current = self.states[current.transition(s[i])]
                except ValueError:
                    current = self.error()

                print(" "*(maxStN - len(current.name)) + current.name + "   " + s[i+1:])

            print("accepted") if current.accepting else print("rejected")

        # Clean up the error state, if it exists.
        e = Error().name
        if e in self.states:
            del self.states[e]

        return current.accepting

    def error(self):
        """ Adds to the set of states a non-accepting error state."""
        e = Error()
        self.states[e.name] = e
        return e

    def copy(self):
        return DFA({name: self.states[name].copy() for name in self.states.keys()}, self.startName, list(self.alphabet))

    def description(self):
        """ Returns a description of this DFA in the format specified in the assignment specification. """
        description = io.StringIO()

        names = sorted(list(self.states.keys()))
        alphabet = sorted(self.alphabet)

        description.write(",".join(names) + '\n')
        description.write(",".join(alphabet) + '\n')
        description.write(self.startName + '\n')
        description.write(",".join([n for n in names if self.states[n].accepting])  + '\n')

        for n in names:
            description.write(",".join([self.states[n].transitions[s] for s in alphabet]) + '\n')

        out = description.getvalue()
        description.close()

        return out

    def describe(self):
        print(self.description(), end="")

    def startTransClosure(self):
        """ Returns a list of all states reachable by transitions from the start state in BFS order. """
        reachableStates = []
        toProcess = deque([self.startName])

        while len(toProcess) != 0:
            current = toProcess.popleft()
            reachableStates.append(current)

            for name in self.states[current].transitions.values():
                if not (name in reachableStates or name in toProcess):
                    toProcess.append(name)

        return reachableStates

    def immStateEquivalence(self, sName1, sName2):
        """ Returns the immediate equivalence of two states.
            Two states are distinct if their accept statuses differ.
            If they share accept status, but their transitions differ, we draw no conclusion
            If they share accept status, and have identical transitions, they are equivalent.
        """
        s1 = self.states[sName1]
        s2 = self.states[sName2]

        if s1.accepting != s2.accepting:
            return False

        if s1.transitions != s2.transitions:
            return -1 # -1 represents indeterminacy

        return True

    def minimised(self, debug=False):
        """ Return the equivalent minimal DFA. """

        machine = self.copy()

        if debug:
            machine.renameStates()

        # First remove any orphaned subgraphs. Handles some cases the table-filling algorithm misses.
        reachables = machine.startTransClosure()
        stateNames = list(machine.states.keys())
        for name in stateNames:
            if name not in reachables:
                del machine.states[name]


        #Use the table-filling algorithm to determine equivalence classes.
        stateNames = list(machine.states.keys())
        equivalences = {stateNames[i]: {stateNames[i]: -1 for i in range(len(stateNames))} for i in range(len(stateNames))}

        # Accepting/non-accepting distinction:
        for state1 in stateNames:
            for state2 in stateNames:
                equivalences[state1][state2] = equivalences[state2][state1] = machine.immStateEquivalence(state1, state2)

        # Determine all inequivalences
        newResults = True
        while newResults:
            newResults = False

            for state1 in stateNames:
                for state2 in stateNames:
                    if state1 == state2:
                        continue

                    equivalence = equivalences[state1][state2]

                    # If the equivalence of two states in undetermined, we can look for transitions of the two states
                    #  on the same symbol, where the destinations are known to be distinct. If such transitions are
                    #  found, the original states are known to be distinct also.
                    if equivalence == -1:
                        for letter in machine.alphabet:
                            if equivalences[machine.states[state1].transition(letter)][machine.states[state2].transition(letter)] == False:
                                equivalences[state1][state2] = equivalences[state2][state1] = False
                                newResults = True
                                continue
                    # If certain states are equivalent, they must share equivalence relations with all other states.
                    elif equivalence == True:
                        for name in stateNames:
                            if equivalences[state1][name] != equivalences[state2][name]:
                                newResults = True
                                if equivalences[state1][name] == -1:
                                    equivalences[state1][name] = equivalences[state2][name]
                                else:
                                    equivalences[state2][name] = equivalences[state1][name]

        # Anything left is an equivalence.
        for state1 in stateNames:
            for state2 in stateNames:
                if equivalences[state1][state2] == -1:
                    equivalences[state1][state2] = True

        # Build a list of equivalence classes, for easier processing.
        eqClasses = []
        for state in stateNames:
            redundant = False
            for eqClass in eqClasses:
                if state in eqClass:
                    redundant = True
                    break
            if redundant:
                continue

            eqClass = []
            for k, v in equivalences[state].items():
                if v:
                    eqClass.append(k)
            eqClasses.append(sorted(eqClass))

        # Consolidate the DFA

        # Redirect the start state
        for eqClass in eqClasses:
            if machine.startName in eqClass:
                machine.startName = eqClass[0]

        # Remove redundant states from the machine
        for eqClass in eqClasses:
            if len(eqClass) > 1:
                for name in eqClass[1:]:
                    del machine.states[name]

        # Redirect transitions to redundant states
        for state in machine.states.values():
            for k, v in state.transitions.items():
                for eqClass in eqClasses:
                    if v in eqClass:
                        state.transitions[k] = eqClass[0]

        # Table-filling algorithm debug output.
        if debug:
            print("  ", end="")
            for k in equivalences.keys():
                print(k, end=" ")
            print()

            for k, v in equivalences.items():
                print(k, end=" ")
                for u in v.values():
                    if u == True: print("T", end=" ")
                    elif u == -1: print("0", end=" ")
                    else: print("_", end=" ")
                print()

            print(eqClasses)

            print(machine.states.keys())
            for state in machine.states.values():
                print(state.name, state.transitions.items())

        return machine

    def toNFA(self):
        """ Return an equivalent NFA-representation of this machine. """
        alphabet = list(self.alphabet)
        startName = self.startName

        states = {}
        for name, state in self.states.items():
            transitions = {s: [state.transitions[s]] for s in state.transitions}
            transitions[NFAState.epsilon] = []
            states[name] = NFAState(state.name, state.accepting, transitions, alphabet)

        return NFA(states, startName, alphabet)

    def renameStates(self):
        """ Rename all the states of this machine. Substitute: capital letter strings.
            The start state is labeled A, its children are labelled from B onwards, etc: BFS ordering. """

        # Determine the order in which to rename states.
        order = self.startTransClosure()
        for state in self.states:
            if state not in order:
                order.append(state)

        # old names -> new names
        mapping = dict(zip(order, letterRange(len(order))))

        self.startName = mapping[self.startName]

        newStates = {}

        for name in self.states:
            newStates[mapping[name]] = self.states[name]

        self.states = newStates

        # Now that states have been remapped in the machine, also switch all transitions.
        for name, state in self.states.items():
            state.name = name
            for symbol, destination in state.transitions.items():
                state.transitions[symbol] = mapping[destination]

    def shortestPath(self, orig, dest):
        """ Returns a string that represents a shortest path between two nodes. """

        if orig == dest:
            return ""

        # Modified BFS: save the node from which each node was discovered, and the symbol defining the transition.
        q = deque([orig])
        discovered = [orig]
        previous = {orig: None}

        pathfound = False

        while len(q) > 0:
            current = self.states[q.popleft()]

            for symbol in current.transitions:
                n = current.transitions[symbol]
                if n not in discovered:
                    q.append(n)
                    previous[n] = [current.name, symbol]
                    discovered.append(n)
                    if n == dest:
                        q.clear()
                        pathfound = True
                        break

        if not pathfound:
            return None

        current = dest
        path = ""

        # Now walk backwards from destination to start state to find the path.
        while previous[current] is not None:
            path = previous[current][1] + path
            current = previous[current][0]

        return path

    def removestate(self, stateName):
        """ Removes a state of this DFA: broken transitions become self-loops."""

        # If we remove the start state, DFA accepts the empty language.
        if stateName == self.startName:
            newStart = State("empty", False, {symbol: "empty" for symbol in self.alphabet}, self.alphabet)
            self.startName = "empty"
            self.states = {"empty": newStart}
            return

        del self.states[stateName]

        for state in self.states.values():
            for symbol, dest in state.transitions.items():
                if stateName == dest:
                    state.transitions[symbol] = state.name


def parseDFA(d):
    """ Takes the description of a DFA, as a string, d. Returns the corresponding DFA object."""

    buf = io.StringIO(d)

    stateNames = [s.strip() for s in buf.readline().split(",")]
    alphabet = [s.strip() for s in buf.readline().split(",")]
    startName = buf.readline().strip()
    acceptStates = [s.strip() for s in buf.readline().split(",")]

    if alphabet == ['']: alphabet = []
    if acceptStates == ['']: acceptStates = []

    transitions = []
    for line in buf:
        transitions.append([s.strip() for s in line.split(",")])

    buf.close()

    if len(stateNames) == 0 or stateNames == ['']:
        raise ValueError("At least one state required.")

    states = {stateNames[i]: State(stateNames[i], stateNames[i] in acceptStates, dict(zip(alphabet, transitions[i])), alphabet, stateNames) for i in range(len(stateNames))}

    return DFA(states, startName, alphabet)



###    NFA STUFF    ##########################################################

class NFAState(object):
    """ A particular NFA state.
        Members:
            name:           the name of the State;
            accepting:      whether the state accepts or not;
            transitions:    a map from alphabet symbols plus epsilon to the names of states. """

    epsilon = ""

    def __init__(self, name, accepting, transitions, alphabet, stateNames=None):
        self.name = name
        self.accepting = accepting

        # Require this to be a state of an NFA, in particular.
        if sorted(alphabet + [NFAState.epsilon]) != sorted(transitions.keys()):
            raise ValueError("State should contain exactly one (possibly empty) transition for each symbol in the alphabet, plus epsilon.")
        if stateNames is not None:
            for stateName in [item for sublist in transitions.values() for item in sublist]:
                if stateName not in stateNames:
                    raise ValueError("Transition to state \"" + stateName + "\" not in machine.")

        self.transitions = transitions

    def copy(self):
        transitions = {symbol: list(destinations) for symbol, destinations in self.transitions.items()}
        return NFAState(self.name, self.accepting, transitions, [symbol for symbol in self.transitions.keys() if symbol != NFAState.epsilon])


class NFA(object):
    """ Represents an NFA. To run it, convert to a DFA first. """

    def __init__(self, states, startName, alphabet):
        self.states = states
        self.alphabet = alphabet

        if startName not in states:
            raise ValueError("Start state \"" + startName + "\" is not a state of the machine.")
        self.startName = startName

    def epsilonClosure(self, initStateNames):
        """ Given a set of NFA states, return the names of all states reachable by zero or more epsilon-transitions. """

        closure = []
        toProcess = list(initStateNames)

        while len(toProcess) != 0:
            current = toProcess.pop()
            if current not in closure:
                closure.append(current)

                for trans in self.states[current].transitions[NFAState.epsilon]:
                    if trans not in toProcess:
                        toProcess.append(trans)

        # Returns the sorted list so stuff can be compared easily later without resorting.
        return sorted(closure)

    def nextNFAStates(self, presentStateNames, symbol):
        """ Given a set of states of the NFA, return all possible destinations after processing a given symbol. """

        destStateNames = []

        for name in self.epsilonClosure(presentStateNames):
            for dest in self.states[name].transitions[symbol]:
                if dest not in destStateNames:
                    destStateNames.append(dest)

        return self.epsilonClosure(destStateNames)

    def toDFA(self):
        """ Return a DFA equivalent to this machine. """

        # map, names -> states, to be passed to the DFA State constructor
        DFAStates = {}

        # map, DFA State names -> sets of NFA state names; for tracking the names of states we have already met
        transitionSets = {}

        # NFA state sets yet to be processed into the TransitionSets map
        toProcess = []

        # Add the start state
        toProcess.append(self.epsilonClosure([self.startName]))
        startName = candidateName("".join(toProcess[0]), transitionSets)

        while len(toProcess) != 0:
            currentState = toProcess.pop()
            if currentState in transitionSets.values():
                continue

            # Determine the transition set for the DFA State we are building
            stateTransitions = {}

            # Find all states reachable from the current state set on a given letter.
            for symbol in self.alphabet:
                nextState = self.nextNFAStates(currentState, symbol)

                preexists = False
                for k, v in transitionSets.items():
                    if v == nextState:
                        preexists = True
                        stateTransitions[symbol] = k

                if not preexists:
                    stateTransitions[symbol] = candidateName("".join(nextState), transitionSets)

                if not (preexists or nextState in toProcess):
                    toProcess.append(nextState)

            cName = candidateName("".join(currentState), transitionSets)
            transitionSets[cName] = currentState

            accepting = False
            for s in currentState:
                if self.states[s].accepting:
                    accepting = True
                    break

            DFAStates[cName] = State(cName, accepting, stateTransitions, self.alphabet)

        return DFA(DFAStates, startName, self.alphabet)

    def description(self):
        """ Returns a description of this NFA in the format specified in the assignment specification. """
        description = io.StringIO()

        names = sorted(list(self.states.keys()))
        alphabet = sorted(self.alphabet)

        description.write(",".join(names) + '\n')
        description.write(",".join(alphabet) + '\n')
        description.write(self.startName + '\n')
        description.write(",".join([n for n in names if self.states[n].accepting])  + '\n')

        for n in names:
            description.write(",".join(["{"+",".join(self.states[n].transitions[s])+"}" for s in alphabet + [NFAState.epsilon]]) + '\n')

        out = description.getvalue()
        description.close()

        return out

    def describe(self):
        print(self.description(), end="")

    def copy(self):
        return NFA({name: self.states[name].copy() for name in self.states.keys()}, self.startName, list(self.alphabet))

    def renameStates(self):
        """ Redesignates the states of this machine, if they have become unmanageably long unreadable strings. """

        mapping = dict(zip(self.states, letterRange(len(self.states))))

        self.startName = mapping[self.startName]

        newStates = {}

        for name in self.states:
            newStates[mapping[name]] = self.states[name]

        self.states = newStates

        for name, state in self.states.items():
            state.name = name
            for symbol, destinations in state.transitions.items():
                state.transitions[symbol] = [mapping[d] for d in destinations if d != '']

    def removestate(self, stateName):
        if stateName == self.startName:
            newStart = NFAState("empty", False, {symbol: [] for symbol in self.alphabet + [NFAState.epsilon]}, self.alphabet)
            self.stateName = "empty"
            self.states = {"empty":newStart}

        del self.states[stateName]

        for state in self.states.values():
            for dests in state.transitions.values():
                if stateName in dests:
                    dests.remove(stateName)


def parseNFA(n):
    """ Takes the description of an NFA, as a string, n. Returns a corresponding DFA."""

    buf = io.StringIO(n)

    stateNames = [s.strip() for s in buf.readline().split(",")]
    alphabet = [s.strip() for s in buf.readline().split(",")]
    startName = buf.readline().strip()
    acceptStates = [s.strip() for s in buf.readline().split(",")]

    if alphabet == ['']: alphabet = []
    if acceptStates == ['']: acceptStates = []

    transitions = []
    for line in buf:
        tList = [s.strip()[1:-1].split(",") for s in re.split(r"\s*,\s*(?={.*})", line)]
        for i, dest in enumerate(tList):
            if dest == ['']:
                tList[i] = []
        transitions.append(tList)

    buf.close()

    if len(stateNames) == 0 or stateNames == ['']:
        raise ValueError("At least one state required.")

    states = {stateNames[i]: NFAState(stateNames[i], stateNames[i] in acceptStates, dict(zip(alphabet + [NFAState.epsilon], transitions[i])), alphabet, stateNames) for i in range(len(stateNames))}

    return NFA(states, startName, alphabet)



###    LANGUAGE OPERATIONS    ##########################################################

def union(machine1, machine2):
    """ Takes two machines, returns a DFA accepting the union of their languages. """

    if isinstance(machine1, NFA):
        machine1 = machine1.toDFA().minimised()
    else:
        machine1 = machine1.minimised()

    if isinstance(machine2, NFA):
        machine2 = machine2.toDFA().minimised()
    else:
        machine1 = machine1.minimised()


    # Build the common alphabet
    a1 = set(machine1.alphabet)
    a2 = set(machine2.alphabet)

    alphabet = a1 | a2
    absent1 = a2-a1
    absent2 = a1-a2

    alphabet = list(alphabet)

    # Build the set of states for the united machine
    unionStates = {}

    stateNames = []
    for name in machine1.states:
        stateNames.append("1" + name)
    for name in machine2.states:
        stateNames.append("2" + name)

    # Construct the new start state, with epsilon transitions to the start states of the constituent machines
    startName = candidateName("st", stateNames)
    stateNames.append(startName)

    startTransitions = {}
    for symbol in alphabet:
        startTransitions[symbol] = []
    startTransitions[NFAState.epsilon] = ["1" + machine1.startName, "2" + machine2.startName]

    unionStates[startName] = NFAState(startName, False, startTransitions, alphabet, stateNames)

    # Construct an error state, required if the input machines are defined over different alphabets
    errorName = candidateName("er", stateNames)
    stateNames.append(errorName)

    errorTransitions = {}
    for symbol in alphabet + [NFAState.epsilon]:
        errorTransitions[symbol] = [errorName]

    unionStates[errorName] = NFAState(errorName, False, errorTransitions, alphabet, stateNames)

    # States of each constituent machine have a numeral prepended to guarantee uniqueness in the united machine
    # Where a symbol was not defined in the alphabet of one of the machines, transition on that symbol to a common error state.
    for name, state in machine1.states.items():
        newTransitions = {}
        for symbol, dest in state.transitions.items():
            newTransitions[symbol] = ["1" + dest]

        for symbol in absent1:
            newTransitions[symbol] = [errorName]

        newTransitions[NFAState.epsilon] = []

        unionStates["1" + name] = NFAState("1" + name, state.accepting, newTransitions, alphabet, stateNames)

    for name, state in machine2.states.items():
        newTransitions = {}
        for symbol, dest in state.transitions.items():
            newTransitions[symbol] = ["2" + dest]

        for symbol in absent2:
            newTransitions[symbol] = [errorName]

        newTransitions[NFAState.epsilon] = []

        unionStates["2" + name] = NFAState("2" + name, state.accepting, newTransitions, alphabet, stateNames)

    return NFA(unionStates, startName, alphabet).toDFA().minimised()


def complement(m):
    """ Given a machine accepting L, returns a DFA accepting the complement of L. """
    if isinstance(m, NFA):
        machine = m.toDFA()
    else:
        machine = m.copy()

    for state in machine.states.values():
        state.accepting = not state.accepting

    return machine


def intersection(m1, m2):
    return complement(union(complement(m1), complement(m2)))
    # Note, no minimisation required here, since the union produces the minimal DFA,
    #  and the complement of a minimal DFA is also minimal.
    #  (otherwise you could find the complement of a minimal DFA, minimise it,
    #   and take the complement to find a smaller DFA equivalent to the minimal one: a contradiction )


def star(m):
    """ Given a machine accepting L, returns a machine accepting L* """
    if isinstance(m, DFA):
        machine = m.toNFA()
    else:
        machine = m.copy()

    #add epsilons from accept states back to start
    for state in machine.states.values():
        if state.accepting:
            state.transitions[NFAState.epsilon] = [machine.startName]

    #add new start state
    startName = candidateName("st*", machine.states, "*")

    startTransitions = {}
    for symbol in machine.alphabet:
        startTransitions[symbol] = []
    startTransitions[NFAState.epsilon] = [machine.startName]

    machine.states[startName] = NFAState(startName, True, startTransitions, machine.alphabet)
    machine.startName = startName

    return machine.toDFA()


def concatenation(machine1, machine2):
    """ Takes two machines, returns a DFA accepting the concatenation of their languages. """

    if isinstance(machine1, NFA):
        machine1 = machine1.toDFA().minimised()
    if isinstance(machine2, NFA):
        machine2 = machine2.toDFA().minimised()


    # Build the common alphabet
    a1 = set(machine1.alphabet)
    a2 = set(machine2.alphabet)

    alphabet = a1 | a2
    absent1 = a2-a1
    absent2 = a1-a2

    alphabet = list(alphabet)

    # Build the set of states for the united machine
    concatStates = {}

    stateNames = []
    for name in machine1.states:
        stateNames.append("1" + name)
    for name in machine2.states:
        stateNames.append("2" + name)

    # Construct an error state, required if the input machines are defined over different alphabets
    errorName = candidateName("er", stateNames)
    stateNames.append(errorName)

    errorTransitions = {}
    for symbol in alphabet + [NFAState.epsilon]:
        errorTransitions[symbol] = [errorName]

    concatStates[errorName] = NFAState(errorName, False, errorTransitions, alphabet, stateNames)

    # States of each constituent machine have a numeral prepended to guarantee uniqueness in the united machine
    # Where a symbol was not defined in the alphabet of one of the machines, transition on that symbol to a common error state.
    for name, state in machine1.states.items():
        newTransitions = {}
        for symbol, dest in state.transitions.items():
            newTransitions[symbol] = ["1" + dest]

        for symbol in absent1:
            newTransitions[symbol] = [errorName]

        if state.accepting:
            newTransitions[NFAState.epsilon] = ["2" + machine2.startName]
        else:
            newTransitions[NFAState.epsilon] = []

        concatStates["1" + name] = NFAState("1" + name, False, newTransitions, alphabet, stateNames)

    for name, state in machine2.states.items():
        newTransitions = {}
        for symbol, dest in state.transitions.items():
            newTransitions[symbol] = ["2" + dest]

        for symbol in absent2:
            newTransitions[symbol] = [errorName]

        newTransitions[NFAState.epsilon] = []

        concatStates["2" + name] = NFAState("2" + name, state.accepting, newTransitions, alphabet, stateNames)

    return NFA(concatStates, "1" + machine1.startName, alphabet).toDFA().minimised()


def reversal(m):
    """ Returns the reversed machine. That is, the new machine accepts any string the original one does, backwards.
        According the Brzozowski, the new machine is guaranteed to be minimal.
        Although I am not sure my implementation actually produces a minimal machine. """

    if isinstance(m, DFA):
        machine = m.toNFA()
        m = m.toNFA()
    else:
        machine = m.copy()

    # Construct new start state with epsilon transitions to the previously accepting states
    startName = candidateName("st<>", machine.states, "<>")
    startTransitions = {}
    for symbol in machine.alphabet:
        startTransitions[symbol] = []
    epsilonTransitions = []
    for state in machine.states.values():
        if state.accepting:
            epsilonTransitions.append(state.name)
            state.accepting = False
    startTransitions[NFAState.epsilon] = epsilonTransitions

    # The new accept state is what was the start state
    machine.states[machine.startName].accepting = True

    # First clear all transitions
    for state in machine.states.values():
        for name in state.transitions:
            state.transitions[name] = []

    # Then substitute the reverses
    for state in m.states.values():
        for symbol, destinations in state.transitions.items():
            for dest in destinations:
                machine.states[dest].transitions[symbol].append(state.name)

    # Post-reversal, add the new start state
    machine.states[startName] = NFAState(startName, False, startTransitions, machine.alphabet)
    machine.startName = startName

    machine = machine.toDFA()

    # Discard any now-unreachable states
    reachables = machine.startTransClosure()
    stateNames = list(machine.states.keys())
    for name in stateNames:
        if name not in reachables:
            del machine.states[name]

    return machine


def empty(machine):
    """ A machine is empty if, when minimised, it contains no accept states. """
    for state in machine.minimised().states.values():
        if state.accepting:
            return False
    return True
    # Note: I only do this out of paranoia. There is no need to be exhaustive like this
    #  if the machine is minimal, and minimisation is only needed to eliminate orphans.


def full(machine):
    """ Determines whether a machine accepts all strings. """
    for state in machine.minimised().states.values():
        if not state.accepting:
            return False
    return True


def equivalent(machine1, machine2, example=False):
    """ Two machines are equivalent if the intersections of one and the complement of the other
        and vice versa are empty.
        If example is True and the two input machines are not equivalent, a string
        on which the two machines differ will be printed."""

    if isinstance(machine1, NFA):
        machine1 = machine1.toDFA()
    if isinstance(machine2, NFA):
        machine2 = machine2.toDFA()

    machine1 = machine1.minimised()
    machine2 = machine2.minimised()

    c1 = complement(machine1)
    c2 = complement(machine2)

    if empty(intersection(machine1, c2)) and empty(intersection(machine2, c1)):
        return True

    if example:
        # The complement of a machine which accepts any input is empty
        #  so its intersection with another machine is empty, but then we miss
        #  strings rejected by the second machine, which are naturally accepted by the first.
        # Similarly, if the second machine is empty, we'll miss strings accepted by the first.
        if full(machine1):
            s = findAcceptedString(c2)
        elif empty(machine2):
            s = findAcceptedString(machine1)
        else:
            s = findAcceptedString(intersection(c1, machine2))

        print('Machines differ on "' + s + '".')

    return False



###    UTILITY FUNCTIONS ##########################################################

def clamp(n, minn, maxn):
    return max(minn, min(maxn, n))


def candidateName(candidate, nameSet, addend="_"):
    """ Small utility function for finding a name which does not conflict with existing names.
        Since many names are built from atomic concatenations, conflicts are conceivable.
        e.g. a1+a2+a3 == a1a+2a3 """

    cName = candidate

    # Handling the empty set, as empty strings are used for epsilon, etc.
    if cName == "":
        cName = "()"

    while cName in nameSet:
        cName += addend

    return cName


def letterRange(n):
    """ Produces a list of capital letter strings: [A, B, C, ..., AB, BB, ...] """
    alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    l = len(alphabet)

    outlist = []

    for i in range(n):
        t = i
        s = ""
        while True:
            s += alphabet[t%l]
            if t < l:
                break
            t //= l
        outlist.append(s)

    return outlist


def findAcceptedString(machine):
    """ Returns a string accepted by the given machine. """
    if isinstance(machine, NFA):
        machine = machine.toDFA()
    machine = machine.minimised()

    if empty(machine):
        return None

    dest = None

    for state in machine.states.values():
        if state.accepting:
            dest = state.name

    return machine.shortestPath(machine.startName, dest)


def loadFA(filename):
    """ Given a filename, returns the machine described in that file. """
    with open(filename, 'r') as f:
        s = f.read()
        if "{" in s:
            return parseNFA(s).toDFA().minimised()
        else:
            return parseDFA(s)

    return None



###    RENDERING THINGS  ##########################################################

class Draggable(object):
    """ For storing information of the entity currently being dragged by the user. """

    def __init__(self, coords, clickcoords, item=None):
        self.coords = [c for c in coords]
        self.clickoffset = [c-d for c, d in zip(coords, clickcoords)]
        self.item = item

    def height(self):
        return self.coords[3]-self.coords[1]

    def width(self):
        return self.coords[2]-self.coords[0]


class FAContext(Frame):
    """ Contains all the required information and methods for drawing a DFA in a window. """

    def __init__(self, parent, w, h, machine, renameStates=True, annealing=True, springdist=100, gravdist=280, edgeLabels=True, stateLabels=False):

        Frame.__init__(self, parent, background="white")

        self.width = w
        self.height = h
        self.parent = parent

        self.parent.geometry('%dx%d+%d+%d' % (w, h, 300, 300))

        self.stateLabels = stateLabels
        self.edgeLabels = edgeLabels

        self.annealing = annealing

        self.naturalSpring = springdist
        self.gravdist = gravdist
        self.springConstant = 0.06
        self.gravConstant = 0.02

        self.dragged = None

        if isinstance(machine, NFA):
            self.machine = machine.toDFA()
        else:
            self.machine = machine.copy()
        if renameStates:
            self.machine.renameStates()

        self.pack(fill=BOTH, expand=1)
        self.parent.focus_force()

        self.initUI()
        self.buildMachineGraph()
        self.annealGraph()

    def moveConnections(self, item):
        """ Upon moving a node, update the positions of all its connections and labels. """

        dest = self.getItemCentre(item)
        name = self.canvas.gettags(item)[0]

        outgoing = self.canvas.find_withtag("o" + name)
        incoming = self.canvas.find_withtag("d" + name)
        loops = self.canvas.find_withtag("i" + name)

        for line in outgoing:
            coords = self.canvas.coords(line)
            coords[0] = dest[0]
            coords[1] = dest[1]
            self.canvas.coords(line, *coords)
            self.canvas.tag_lower(line)

            for tag in self.canvas.gettags(line):
                if tag[0] == "s":
                    symbol = tag[1:]
                elif tag[0] == "d":
                    distal = tag[1:]

            labels = self.canvas.find_withtag("l" + str(line))
            for label in labels:
                if self.canvas.itemcget(label, "text") == symbol:
                    self.canvas.coords(label, *self.proxpoint(coords[:2], self.getItemCentre(self.canvas.find_withtag(distal)[0])))
                self.canvas.tag_raise(label)


        for line in incoming:
            coords = self.canvas.coords(line)
            coords[2] = dest[0]
            coords[3] = dest[1]
            self.canvas.coords(line, *coords)
            self.canvas.tag_lower(line)

            for tag in self.canvas.gettags(line):
                if tag[0] == "s":
                    symbol = tag[1:]
                elif tag[0] == "o":
                    proximal = tag[1:]

            labels = self.canvas.find_withtag("l" + str(line))
            for label in labels:
                if self.canvas.itemcget(label, "text") == symbol:
                    self.canvas.coords(label, *self.proxpoint(self.getItemCentre(self.canvas.find_withtag(proximal)[0]), coords[2:]))
                self.canvas.tag_raise(label)

        for loop in loops:
            coords = self.getBoxByCentre([dest[0], dest[1]-20], 10)
            self.canvas.coords(loop, *coords)
            self.canvas.tag_lower(loop)

            labels = self.canvas.find_withtag("l" + str(loop))
            for label in labels:
                #if self.canvas.itemcget(label, "text") == symbol:
                self.canvas.coords(label, *[dest[0], dest[1]-30])
                self.canvas.tag_raise(label)


        stateLabel = self.canvas.find_withtag("n" + name)
        if stateLabel != ():
            stateLabel = stateLabel[0]
            labelCoords = self.canvas.coords(stateLabel)
            labelCoords[0] = dest[0]
            labelCoords[1] = dest[1]
            self.canvas.coords(stateLabel, *labelCoords)
            self.canvas.tag_raise(stateLabel)

        self.canvas.tag_lower(self.deleteText)
        self.canvas.tag_lower(self.deleteRectangle)

    def mouseClick(self, event):
        clickcoords = [self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)]
        clicked = self.canvas.find_withtag("current")

        self.dragged = None
        if clicked == ():
            return

        immovable = False
        for tag in self.canvas.gettags(clicked):
            if tag[0] == "i" or tag[0] == "n" or tag == "delete":
                immovable = True
                break

        if not (self.canvas.type(clicked) == "line" or immovable): # or self.canvas.type(clicked) == "text"): # Uncomment if text should not be movable
            self.canvas.tag_raise(clicked)
            self.dragged = Draggable(self.canvas.coords(clicked), clickcoords, clicked)

    def moveClick(self, event):
        """ Handle the user moving the mouse with the mouse button held down. """
        if self.dragged is not None:
            x = clamp(self.canvas.canvasx(event.x) + self.dragged.clickoffset[0], 0, self.width - 40)
            y = clamp(self.canvas.canvasy(event.y) + self.dragged.clickoffset[1], 0, self.height - 40)

            if len(self.dragged.coords) == 2:
                self.dragged.coords = [x, y]
            else:
                w = self.dragged.width()
                h = self.dragged.height()
                self.dragged.coords = [x, y, x+w, y+h]

            self.canvas.coords(self.dragged.item, *self.dragged.coords)
            self.moveConnections(self.dragged.item)

    def releaseClick(self, event):
        if self.dragged is not None:
            if self.canvas.type(self.dragged.item) == "oval":
                deleteCoords = self.canvas.coords(self.deleteRectangle)
                itemCoords = self.canvas.coords(self.dragged.item)

                if (itemCoords[0] > deleteCoords[0] and itemCoords[0] < deleteCoords[2]-40 and
                    itemCoords[1] > deleteCoords[1] and itemCoords[1] < deleteCoords[3]):
                    self.machine.removestate(self.canvas.gettags(self.dragged.item)[0])
                    self.buildMachineGraph()

        self.dragged = None

    def resizeCanvas(self, event):
        """ Update the bounds of the canvas when the window is resized. """
        self.width = event.width
        self.height = event.height

        self.gravScale.place(x=120, y=self.height-70)
        self.springScale.place(x=10, y=self.height-70)

        self.gravEntry.place(x=350, y=self.height-36)
        self.gravEntryButton.place(x=400, y=self.height-36)

        self.springEntry.place(x=235, y=self.height-36)
        self.springEntryButton.place(x=285, y=self.height-36)

        self.edgeLabelCheck.place(x=self.width-200, y=10)
        self.stateLabelCheck.place(x=self.width-100, y=10)

        self.quitButton.place(x=self.width-40, y=self.height-95)

        self.fileEntry.place(x=self.width-155, y=self.height-65)
        self.fileEntryButton.place(x=self.width-220, y=self.height-65)

        self.checkEntry.place(x=self.width-155, y=self.height-36)
        self.checkEntryButton.place(x=self.width-243, y=self.height-36)

    def getItemCentre(self, item):
        coords = self.canvas.coords(item)
        return [sum(x)/2 for x in zip(coords[:2], coords[2:])]

    def getBoxByCentre(self, p, radius):
        return [p[0]-radius, p[1]-radius, p[0]+radius, p[1]+radius]

    def proxpoint(self, p1, p2):
        """ Produce the coordinates of a point near p1 on the line between it and p2. """

        desired = 40
        length = math.sqrt((p2[0]-p1[0])**2 + (p2[1]-p1[1])**2)

        if length < 3*desired:
            return [(2*x[0]/3) + (x[1]/3) for x in zip(p1, p2)]

        scale = length/desired
        if scale == 0:
            scale = 0.1

        return [p1[0] + (p2[0]-p1[0])/scale, p1[1] + (p2[1]-p1[1])/scale]

    def toggleStateLabels(self):
        self.stateLabels = not self.stateLabels

        labels = self.canvas.find_withtag("tsLabel")

        newState = "hidden"

        if self.stateLabels:
            newState = "normal"

        for label in labels:
            self.canvas.itemconfig(label, state=newState)

    def toggleEdgeLabels(self):
        self.edgeLabels = not self.edgeLabels

        labels = self.canvas.find_withtag("teLabel")

        newState = "hidden"

        if self.edgeLabels:
            newState = "normal"

        for label in labels:
            self.canvas.itemconfig(label, state=newState)

    def toggleAnnealing(self):
        self.annealing = not self.annealing

        if self.annealing:
            self.simButton.config(relief="sunken")
            self.parent.after(17, self.annealGraph)
        else:
            self.simButton.config(relief="groove")

    def updategravdist(self, val):
        self.gravdist = int(val)

    def updatespringdist(self, val):
        self.naturalSpring = int(val)

    def updatespringconstant(self):
        self.springConstant = float(self.springEntry.get())
        self.parent.focus()

    def updategravconstant(self):
        self.gravConstant = float(self.gravEntry.get())
        self.parent.focus()

    def annealGraph(self):
        """ Settles the graph into a possibly-more-pleasing shape than a random splatter.
            It is a little rubbish at the moment, though. """

        newCoords = []

        numNodes = len(self.nodes)

        # There is no force exerted by a single node or fewer.
        if numNodes < 2:
            return

        # Calculate forces for every node in the graph.
        for i in range(numNodes):
            springVectors = []
            gravVectors = []
            forces = []

            centre = self.getItemCentre(self.nodes[i])
            selfname = self.canvas.gettags(self.nodes[i])[0]

            # Find the vectors to this node from every other node in the graph.
            for p in self.nodes[:i] + self.nodes[i+1:]:
                exocentre = self.getItemCentre(p)
                diff = [exocentre[0]-centre[0], exocentre[1]-centre[1]]

                gravVectors.append(diff)

                distname = self.canvas.gettags(p)[0]
                if distname not in self.machine.states[selfname].transitions.values():
                    if selfname not in self.machine.states[distname].transitions.values():
                        continue
                springVectors.append(diff)

            # Calculate the forces on this node from all nodes connected to it by an edge.
            for v in springVectors:
                scale = math.sqrt(v[0]**2 + v[1]**2)/self.naturalSpring

                if scale == 0:
                    scale = 0.001

                relaxed = [v[0]/scale, v[1]/scale]

                x = (v[0] - relaxed[0])*self.springConstant
                y = (v[1] - relaxed[1])*self.springConstant

                forces.append([x, y])

            # Every node in the graph exerts a force on every other node, more weakly than springs.
            for v in gravVectors:
                scale = math.sqrt(v[0]**2 + v[1]**2)/self.gravdist

                if scale == 0:
                    scale = -0.001

                relaxed = [v[0]/scale, v[1]/scale]

                x = (v[0] - relaxed[0])*self.gravConstant
                y = (v[1] - relaxed[1])*self.gravConstant

                forces.append([x, y])

            force = [sum(component) for component in zip(*forces)]

            centre = [clamp(centre[0]+force[0], 20, self.width - 20), clamp(centre[1]+force[1], 20, self.height - 20)]
            newCoords.append(self.getBoxByCentre(centre, 20))

        # Move the nodes according to the net force on them, but don't move items currently being dragged.
        for node, coord in zip(self.nodes, newCoords):
            if self.dragged is not None:
                if node == self.dragged.item[0]:
                    continue
            self.canvas.coords(node, *coord)
            self.moveConnections(node)

        if self.annealing:
            self.parent.after(17, self.annealGraph)

    def buildMachineGraph(self):
        """ Creates and tags all the nodes, labels, interconnections for drawing the given machine. """

        self.canvas.delete("all")

        self.nodes = []

        edgeLabelState = "normal" if self.edgeLabels else "hidden"
        stateLabelState = "normal" if self.stateLabels else "hidden"

        for state in self.machine.states.values():
            name = state.name
            thickness = 1
            colour = "#ccc"
            activecolour = "#eee"

            if state.accepting:
                thickness = 3

            pattern = []

            if state.name == self.machine.startName:
                pattern = [15, 8]
                colour = "#fff"
                activecolour = "#fee"

            x = random.randrange(self.width-40)
            y = random.randrange(40, self.height-80)


            self.nodes.append(self.canvas.create_oval(x, y, x+40, y+40, outline="#444", fill=colour, activefill=activecolour, tag=name, width=thickness, dash=pattern))

            self.canvas.create_text(x+20, y+20, fill="#444", font=("Purisa", 14), text=name, tags=("n"+name, "tsLabel"), state=stateLabelState)

            for sym, dest in state.transitions.items():
                labelOffset = random.choice(['n', 'e', 's', 'w'])
                loopOffset = random.choice(['center', 'sw', 'se'])

                if name == dest:
                    l = self.canvas.create_oval(x+10, y-10, x+30, y+10, fill="", tags=("i" + name, "s" + sym))
                    self.canvas.create_text(x+20, y-10, fill="#334", font=("Purisa", 13), text=sym, tags=("l"+str(l), "teLabel"), anchor=loopOffset, state=edgeLabelState)
                    self.canvas.tag_lower(l)
                else:
                    l = self.canvas.create_line(x, y, x+40, y+40, fill="#555", smooth=1, arrow="last", arrowshape=[21, 26, 3], tags=("o" + name, "d" + dest, "s" + sym))
                    self.canvas.create_text(x+20, y+20, anchor=labelOffset, fill="#334", font=("Purisa", 13), text=sym, tags=("l"+str(l), "teLabel"), state=edgeLabelState)
                    self.canvas.tag_lower(l)

        for node in self.nodes:
            self.moveConnections(node)


        self.deleteText = self.canvas.create_text([15, 45], anchor='nw', text="Delete\nNode", font=("Helvetica, 10"), width=50, tag="delete")
        self.canvas.tag_lower(self.deleteText)
        self.deleteRectangle = self.canvas.create_rectangle([10, 40, 70, 100], fill="#ddd", tag="delete")
        self.canvas.tag_lower(self.deleteRectangle)


    def describeActiveMachine(self):
        self.machine.describe()
        print()

    def checkActiveMachine(self):
        self.machine.checkString(self.checkEntry.get())
        self.checkEntry.delete(0, "end")
        print()

    def modActiveMachine(self, transform, sim=True):
        """ Replaces the current machine with a transformed version."""
        if self.annealing:
            self.toggleAnnealing()
            self.parent.after(100, self.modActiveMachine, transform)
            return

        if transform == "minimise":
            self.machine = self.machine.minimised()
        elif transform == "complement":
            self.machine = complement(self.machine)
        elif transform == "reverse":
            self.machine = reversal(self.machine.minimised())
        elif transform == "star":
            self.machine = star(self.machine.minimised())
        elif transform == "rename":
            self.machine.renameStates()
        elif transform == "load":
            self.loadActiveMachine(self.fileEntry.get()) #TODO: Work out why I couldn't pass this as an argument

        self.buildMachineGraph()

        self.parent.focus()

        if sim:
            self.toggleAnnealing()

    def loadActiveMachine(self, filename):
        """ Replaces the currently-active machine with one defined in filename, if it is valid. """
        try:
            with open(filename, 'r') as f:
                s = f.read()
                if "{" in s:
                    self.machine = parseNFA(s).toDFA().minimised()
                else:
                    self.machine = parseDFA(s)
        except:
            self.fileEntry.delete(0, "end")

    def initUI(self):
        """ Build the interface. """

        self.parent.title("DFA Viz")
        self.parent.bind("<Escape>", lambda e: self.parent.destroy())
        self.bind("<Configure>", self.resizeCanvas)

        self.canvas = Canvas(self, background="white")
        self.canvas.bind("<Button-1>", self.mouseClick)
        self.canvas.bind("<B1-Motion>", self.moveClick)
        self.canvas.bind("<ButtonRelease-1>", self.releaseClick)

        bFont = ("Helvetica", 10)

        self.simButton = Button(self, font=bFont, padx=0, pady=0, text="Toggle Sim", relief="sunken", command=self.toggleAnnealing)
        self.simButton.place(x=10, y=10)


        self.gravScale = Scale(self, from_=20, to=500, orient="horizontal", label="grav radius", command=self.updategravdist)
        self.gravScale.set(self.gravdist)
        self.gravScale.place(x=120, y=self.height-70)

        self.springScale = Scale(self, from_=20, to=500, orient="horizontal", label="spring radius", command=self.updatespringdist)
        self.springScale.set(self.naturalSpring)
        self.springScale.place(x=10, y=self.height-70)


        self.springEntry = Entry(self, font=bFont, width=6, justify="right", bg="#eee")
        self.springEntry.place(x=235, y=self.height-36)
        self.springEntry.insert(0, str(self.springConstant))
        self.springEntryButton = Button(self, font=bFont, padx=0, pady=0, text="spr const", command=self.updatespringconstant)
        self.springEntryButton.place(x=285, y=self.height-36)
        self.springEntry.bind("<Return>", lambda e: self.updatespringconstant())

        self.gravEntry = Entry(self, font=bFont, width=6, justify="right", bg="#eee")
        self.gravEntry.place(x=350, y=self.height-36)
        self.gravEntry.insert(0, str(self.gravConstant))
        self.gravEntryButton = Button(self, font=bFont, padx=0, pady=0, text="grav const", command=self.updategravconstant)
        self.gravEntryButton.place(x=400, y=self.height-36)
        self.gravEntry.bind("<Return>", lambda e: self.updategravconstant())

        self.stateLabelCheck = Checkbutton(self, text="State Labels", command=self.toggleStateLabels)
        self.stateLabelCheck.place(x=self.width-100, y=10)
        if self.stateLabels:
            self.stateLabelCheck.select()

        self.edgeLabelCheck = Checkbutton(self, text="Edge Labels", command=self.toggleEdgeLabels)
        self.edgeLabelCheck.place(x=self.width-200, y=10)
        if self.edgeLabels:
            self.edgeLabelCheck.select()


        self.minButton = Button(self, text="Minimise", font=bFont, padx=0, pady=0, command=lambda: self.modActiveMachine("minimise"))
        self.minButton.place(x=90, y=10)

        self.compButton = Button(self, text="Complement", font=bFont, padx=0, pady=0, command=lambda: self.modActiveMachine("complement"))
        self.compButton.place(x=160, y=10)

        self.revButton = Button(self, text="Reverse", font=bFont, padx=0, pady=0, command=lambda: self.modActiveMachine("reverse"))
        self.revButton.place(x=250, y=10)

        self.starButton = Button(self, text="Star", font=bFont, padx=0, pady=0, command=lambda: self.modActiveMachine("star"))
        self.starButton.place(x=310, y=10)

        self.renameButton = Button(self, text="Redesignate", font=bFont, padx=0, pady=0, command=lambda: self.modActiveMachine("rename"))
        self.renameButton.place(x=350, y=10)

        self.describeButton = Button(self, text="Describe", font=bFont, padx=0, pady=0, command=self.describeActiveMachine)
        self.describeButton.place(x=435, y=10)

        self.quitButton = Button(self, text="Quit", font=bFont, padx=0, pady=0, command=self.parent.destroy)
        self.quitButton.place(x=self.width-45, y=self.height-106)


        self.fileEntry = Entry(self, font=bFont, bg="#eee")
        self.fileEntry.place(x=self.width-155, y=self.height-70)
        self.fileEntryButton = Button(self, text="Load File", font=bFont, padx=0, pady=0, command=lambda: self.modActiveMachine("load"))
        self.fileEntryButton.place(x=self.width-220, y=self.height-70)
        self.fileEntry.bind("<Return>", lambda e: self.modActiveMachine("load"))


        self.checkEntry = Entry(self, font=bFont, bg="#eee")
        self.checkEntry.place(x=self.width-155, y=self.height-36)
        self.checkEntryButton = Button(self, text="Check String", font=bFont, padx=0, pady=0, command=self.checkActiveMachine)
        self.checkEntryButton.place(x=self.width-243, y=self.height-36)
        self.checkEntry.bind("<Return>", lambda e: self.checkActiveMachine())

        self.deleteRectangle = self.canvas.create_rectangle([10, 40, 70, 100], fill="#ddd", tag="delete")
        self.deleteText = self.canvas.create_text([15, 45], anchor='nw', text="Delete\nNode", font=bFont, width=50, tag="delete")

        self.canvas.pack(fill=BOTH, expand=1)


def drawDFA(machine, rename=True, grav=280, spring=100, eLabels=True, sLabels=False):
    """ Draws and anneals the given machine. """
    root = Tk()
    win = FAContext(root, 800, 600, machine, renameStates=rename, gravdist=grav, springdist=spring, edgeLabels=eLabels, stateLabels=sLabels)
    root.mainloop()


###    RUNTIME THINGS    ##########################################################

def defaultMachine(s):
    """ Checks a string on the machine accepting input of length 3, or which does not contain the substring '101' """

    # We could build the machine from scratch if we wished, in this way:
    # Assuming L1.dfa and L4.dfa exist, with the correct contents.
    # union(loadFA("L1.dfa"), loadFA("L2.dfa")).checkString(s)

    description = ("A,C,F,J,N,gamma,alpha,beta\n"  # States
                   "0,1\n"                         # Alphabet
                   "A\n"                           # Start State
                   "A,C,F,J,gamma,alpha,beta\n"    # Accept States
                   "gamma,C\n"                     # A
                   "F,alpha\n"                     # C
                   "gamma,J\n"                     # F
                   "N,N\n"                         # J
                   "N,N\n"                         # N
                   "gamma,alpha\n"                 # gamma
                   "beta,alpha\n"                  # alpha
                   "gamma,N\n")                    # beta

    parseDFA(description).checkString(s)


def demo():
    """ A demonstration function, runs most available functions one way or another. """

    print("NFA Parsing\n-----------\n")

    abcString = (
        "S,A,B,C\n"
        "a,b,c\n"
        "S\n"
        "C\n"
        "{A},{},{},{}\n"
        "{},{B},{},{}\n"
        "{},{},{C},{}\n"
        "{},{},{},{}\n")

    abc = parseNFA(abcString)

    print("An NFA accepting 'abc': \n" + abcString + "\nOn 'abc':")
    abc.toDFA().checkString("abc")
    print("\nOn 'cba':")
    abc.toDFA().checkString("cba")



    print("\n\n\nExtra-Alphabetic Symbol Handling\n--------------------------------\n")
    print("The previous machine is defined only on [abc], but dynamically transitions to an error state for other input.\n")

    abc.toDFA().checkString("abFabc")



    print("\n\n\nNFA <-> DFA Conversion\n----------------------\n")
    print("If we convert the previous NFA to a DFA, we get the following description:\n")
    abc.toDFA().describe()
    print("\nWhere '()' has been substituted for the empty set.\n")

    print("If we define a DFA, for example:\n")

    dfa1String = (
        "A,B,C\n"
        "s,t\n"
        "A\n"
        "B\n"
        "B,A\n"
        "C,A\n"
        "C,B\n")

    dfa1 = parseDFA(dfa1String)

    print(dfa1String + "\nWe can represent this in the NFA format as well:\n")

    dfa1.toNFA().describe()


    print("\n\n\nDFA Minimisation\n----------------\n")
    print("Let us define a relatively large NFA. The following represents L1 U L2 from Task 1:\n")

    t1String = ("S,L11,L12,L13,L21,L22,L23,L24,U\n"
                "0,1\n"
                "S\n"
                "L11,L12,L13,L24\n"
                "{},{},{L11,L21}\n"
                "{L11},{L12},{}\n"
                "{L13},{L12},{}\n"
                "{L11},{U},{}\n"
                "{L22},{L22},{}\n"
                "{L23},{L23},{}\n"
                "{L24},{L24},{}\n"
                "{U},{U},{}\n"
                "{U},{U},{}\n")

    t1 = parseNFA(t1String)

    print(t1String + "\nWe may convert this to a DFA, yielding:\n")

    t2 = t1.toDFA()

    t2.describe()

    print("\nWhich itself can be minimised to this 8-state machine:\n")

    t3 = t2.minimised()
    t3.describe()

    print("\nOr, with the states renamed,\n")

    t3.renameStates()
    t3.describe()

    print("\nHence, we can check strings against the NFA by using the equivalent DFA:\n")

    t3.checkString("101")
    print()
    t3.checkString("1010")



    print("\n\n\nLanguage Operations\n-------------------\n")
    print("We can obtain a machine derived from the union of two other machines.")
    print("Further, we are able to do this even when the alphabets of the constituent machines differ.")
    print("For example, here are the descriptions of two DFAs on different alphabets:\n")


    numString = ("1,2,3,4\n"
                "0,1\n"
                "1\n"
                "1,2,3\n"
                "1,2\n"
                "3,2\n"
                "1,4\n"
                "4,4\n")

    alphanumString = (
        "A,B,C\n"
        "a,b,0\n"
        "A\n"
        "B\n"
        "B,A,B\n"
        "C,A,C\n"
        "C,B,A\n")

    numerical = parseDFA(numString)
    alphanumerical = parseDFA(alphanumString)

    print(numString)
    print(alphanumString)

    print("And their union is:\n")

    u = union(numerical, alphanumerical)
    u.describe()

    print("\nNotice that the alphabet is the union of the alphabets, and an extra state 'er' has been added,")
    print("which indicates the state a machine transitions to on a symbol it does not recognise.")

    print("\nIt would not be very interesting to demonstrate complement, intersection, star closure, reversal, and concatenation individually.")
    print("So, we will construct a machine equivalent to the regex (?abc(cba|01)*ccc)(?^(abc01ccc));")
    print("So we need machines which accept 'cba', '01', 'ccc' and 'abc01ccc'.")
    print("We already have the one for 'abc'. 'cba' is 'abc' reversed, and 'abc01ccc' may be obtained by concatenation.")
    print("So we only need machines for '01' and 'ccc', which are:\n")

    ohOneString = ("S,O,F\n"
                   "0,1\n"
                   "S\n"
                   "F\n"
                   "{O},{},{}\n"
                   "{},{F},{}\n"
                   "{},{},{}\n")

    cccString = ("C1,C2,C3,C4\n"
                 "c\n"
                 "C1\n"
                 "C4\n"
                 "{C2},{}\n"
                 "{C3},{}\n"
                 "{C4},{}\n"
                 "{},{}\n")

    print(ohOneString + "\n")
    print(cccString +"\n")

    ohOne = parseNFA(ohOneString).toDFA().minimised()
    ccc = parseNFA(cccString).toDFA().minimised()

    print("The machine for the regex looks like this:\n")

    regex = intersection(concatenation(abc, concatenation(star(union(reversal(abc), ohOne)), ccc)), complement(concatenation(concatenation(abc, ohOne), ccc)))
    regex.describe()

    print("\nOr, renamed:\n")
    regex.renameStates()
    regex.describe()



    print("\n\nEquality of Machines\n--------------------\n")
    print("We can verify the equality of machines with this program easily enough.")
    print("But a cute feature available is that if they differ, we can return a string which one accepts and the other rejects.")
    print("For example, the following ", end="")
    a1s = ("A,B,C,D\n"
          "a,b,c\n"
          "A\n"
          "C,D\n"
          "B,B,A\n"
          "A,C,D\n"
          "D,A,D\n"
          "D,B,D\n")

    a2s = ("1,2,3\n"
          "a,b,c\n"
          "1\n"
          "3\n"
          "1,2,2\n"
          "3,2,1\n"
          "1,2,1\n")

    a1 = parseDFA(a1s)
    a2 = parseDFA(a2s)

    equivalent(a1, a2, True)

    print("\n" + a1s + "\n" + a2s)

    print("In a similar vein, we can find the shortest string that will transition between any two states in a machine.")
    print("In particular, it's useful for finding an example string which is accepted by a machine, if such a string exists.")
    print("For example, the above regex machine accepts the string '", end="")
    print(findAcceptedString(regex) + "'.")



    print("\n\nVisualisation\n-------------\n")
    print("We can display visually the machine for the task 2. Click the Minimise button to get the machine for task 3.")
    print("Drag nodes around with the mouse.")
    print("\nSome other attractive examples are available by uncommenting lines in the source.")
    print("You can also see your own machines, if they have been defined in files, by using the input on the lower right,")
    print("or by invoking the program with the arguments '--draw filename', and filename can be empty.\n")
    print("Be careful with the star and reversal operations on large machines.\nSee the source for more exhaustive notes.\n")
    print("-|-\n/ \\\n")

    drawDFA(t2, rename=False, sLabels=True)
    drawDFA(abc)

    florette = ("""O,A,B,C,D,E,AL,AR,AC,BL,BR,BC,CL,CR,CC,DL,DR,DC,EL,ER,EC
                ;,:,',",.   
                O
                A,B,C,D,E
                A,B,C,D,E
                AL,AR,B,E,O
                BL,BR,C,A,O
                CL,CR,D,B,O
                DL,DR,E,C,O
                EL,ER,A,D,O
                AR,AR,AR,AR,AR
                AL,AL,AL,AL,AL
                AL,AR,AC,AC,AC
                BR,BR,BR,BR,BR
                BL,BL,BL,BL,BL
                BL,BR,BC,BC,BC
                CR,CR,CR,CR,CR
                CL,CL,CL,CL,CL
                CL,CR,CC,CC,CC
                DR,DR,DR,DR,DR
                DL,DL,DL,DL,DL
                DL,DR,DC,DC,DC
                ER,ER,ER,ER,ER
                EL,EL,EL,EL,EL
                EL,ER,EC,EC,EC""")

    # This will remove the error state of the regex DFA and draw it -- though broken transitions will become self-loops.
    counts = {state: 0 for state in regex.states}
    for state in regex.states.values():
        for dest in state.transitions.values():
            counts[dest] += 1
    maximum = max(counts.values())
    maxIncoming = [n for n in counts if counts[n] == maximum][0]
    regex.removestate(maxIncoming)

    # Other examples
    #drawDFA(parseDFA(florette), rename=False, spring=20, grav=220, eLabels=False)
    #drawDFA(regex, rename=False)
    #drawDFA(u)


if __name__ == '__main__':
    if len(sys.argv) >= 3:
        if sys.argv[1] == "--draw":
            drawDFA(loadFA(sys.argv[2]), rename=False)
        elif len(sys.argv) == 4:
            if sys.argv[1] == "--union":
                drawDFA(union(loadFA(sys.argv[2]), loadFA(sys.argv[3])))
            elif sys.argv[1] == "--concat":
                drawDFA(concatenation(loadFA(sys.argv[2]), loadFA(sys.argv[3])))
            elif sys.argv[1] == "--intersect":
                drawDFA(intersection(loadFA(sys.argv[2]), loadFA(sys.argv[3])))
            else:
                loadFA(sys.argv[2]).checkString(sys.argv[1])
        else:
            loadFA(sys.argv[2]).checkString(sys.argv[1])
    elif len(sys.argv) == 2:
        if sys.argv[1] == "--demo":
            demo()
        elif sys.argv[1] == "--draw":
            drawDFA(parseDFA(".\n\n.\n\n\n"))
        else:
            defaultMachine(sys.argv[1])
    else:
        print("rejected")
