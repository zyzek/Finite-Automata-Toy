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

    # We allow state_names not to be provided in order to facilitate the
    # iterative construction of a machine where the final set of states is not
    # known until we are done building states
    def __init__(self, name, accepting, transitions, alphabet, state_names=None):
        self.name = name
        self.accepting = accepting

        # Require this to be a state of a DFA, in particular.
        if sorted(alphabet) != sorted(transitions.keys()):
            raise ValueError("Each state of a DFA requires exactly one transition for each symbol in the alphabet.")
        if state_names is not None:
            for state_name in transitions.values():
                if state_name not in state_names:
                    raise ValueError("Transition to state \"" + state_name + "\" not in machine.")
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
            start_name:  the name of the start state;
            alphabet:   a list of the strings which compose the alphabet. Symbols can be multiple characters long. """

    def __init__(self, states, start_name, alphabet):
        self.states = states
        self.alphabet = alphabet

        if start_name not in states:
            raise ValueError("Start state \"" + start_name + "\" is not a state of the machine.")
        self.start_name = start_name

    def check_string(self, s, verbose=True):
        """ Run this DFA on the given string. Returns true if the string is accepted, false otherwise.
            Parameters:
                s:          the string to process;
                verbose:    if True, an execution trace is printed; if False, the result is returned silently. """

        current = self.states[self.start_name]

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

            max_st = max([len(state) for state in self.states])
            max_sy = 0
            if len(self.alphabet) != 0:
                max_sy = max([len(c) for c in self.alphabet])

            for i in range(len(s)):
                print(s[:i] + " "*(len(s) - i + 2) + current.name + " "*(max_st - len(current.name)), end="")
                print(" -- " + s[i] + " "*(max_sy - len(s[i])) + " --> ", end="")

                # If a character not in the alphabet is tried, transition to an inescapable error state
                # which self-loops on all input.
                try:
                    current = self.states[current.transition(s[i])]
                except ValueError:
                    current = self.error()

                print(" "*(max_st - len(current.name)) + current.name + "   " + s[i+1:])

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
        return DFA({name: self.states[name].copy() for name in self.states.keys()}, self.start_name, list(self.alphabet))

    def description(self):
        """ Returns a description of this DFA in the format specified in the assignment specification. """
        description = io.StringIO()

        names = sorted(list(self.states.keys()))
        alphabet = sorted(self.alphabet)

        description.write(",".join(names) + '\n')
        description.write(",".join(alphabet) + '\n')
        description.write(self.start_name + '\n')
        description.write(",".join([n for n in names if self.states[n].accepting])  + '\n')

        for n in names:
            description.write(",".join([self.states[n].transitions[s] for s in alphabet]) + '\n')

        out = description.getvalue()
        description.close()

        return out

    def describe(self):
        print(self.description(), end="")

    def start_trans_closure(self):
        """ Returns a list of all states reachable by transitions from the start state in BFS order. """
        reachables = []
        to_process = deque([self.start_name])

        while len(to_process) != 0:
            current = to_process.popleft()
            reachables.append(current)

            for name in self.states[current].transitions.values():
                if not (name in reachables or name in to_process):
                    to_process.append(name)

        return reachables

    def imm_state_equiv(self, sName1, sName2):
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
            machine.rename_states()

        # First remove any orphaned subgraphs. Handles some cases the table-filling algorithm misses.
        reachables = machine.start_trans_closure()
        state_names = list(machine.states.keys())
        for name in state_names:
            if name not in reachables:
                del machine.states[name]


        #Use the table-filling algorithm to determine equivalence classes.
        state_names = list(machine.states.keys())
        equivalences = {state_names[i]: {state_names[i]: -1 for i in range(len(state_names))} for i in range(len(state_names))}

        # Accepting/non-accepting distinction:
        for state1 in state_names:
            for state2 in state_names:
                equivalences[state1][state2] = equivalences[state2][state1] = machine.imm_state_equiv(state1, state2)

        # Determine all inequivalences
        new_results = True
        while new_results:
            new_results = False

            for state1 in state_names:
                for state2 in state_names:
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
                                new_results = True
                                continue
                    # If certain states are equivalent, they must share equivalence relations with all other states.
                    elif equivalence == True:
                        for name in state_names:
                            if equivalences[state1][name] != equivalences[state2][name]:
                                new_results = True
                                if equivalences[state1][name] == -1:
                                    equivalences[state1][name] = equivalences[state2][name]
                                else:
                                    equivalences[state2][name] = equivalences[state1][name]

        # Anything left is an equivalence.
        for state1 in state_names:
            for state2 in state_names:
                if equivalences[state1][state2] == -1:
                    equivalences[state1][state2] = True

        # Build a list of equivalence classes, for easier processing.
        eq_classes = []
        for state in state_names:
            redundant = False
            for eq_class in eq_classes:
                if state in eq_class:
                    redundant = True
                    break
            if redundant:
                continue

            eq_class = []
            for k, v in equivalences[state].items():
                if v:
                    eq_class.append(k)
            eq_classes.append(sorted(eq_class))

        # Consolidate the DFA

        # Redirect the start state
        for eq_class in eq_classes:
            if machine.start_name in eq_class:
                machine.start_name = eq_class[0]

        # Remove redundant states from the machine
        for eq_class in eq_classes:
            if len(eq_class) > 1:
                for name in eq_class[1:]:
                    del machine.states[name]

        # Redirect transitions to redundant states
        for state in machine.states.values():
            for k, v in state.transitions.items():
                for eq_class in eq_classes:
                    if v in eq_class:
                        state.transitions[k] = eq_class[0]

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

            print(eq_classes)

            print(machine.states.keys())
            for state in machine.states.values():
                print(state.name, state.transitions.items())

        return machine

    def nfa(self):
        """ Return an equivalent NFA-representation of this machine. """
        alphabet = list(self.alphabet)
        start_name = self.start_name

        states = {}
        for name, state in self.states.items():
            transitions = {s: [state.transitions[s]] for s in state.transitions}
            transitions[NFAState.epsilon] = []
            states[name] = NFAState(state.name, state.accepting, transitions, alphabet)

        return NFA(states, start_name, alphabet)

    def rename_states(self):
        """ Rename all the states of this machine. Substitute: capital letter strings.
            The start state is labeled A, its children are labelled from B onwards, etc: BFS ordering. """

        # Determine the order in which to rename states.
        order = self.start_trans_closure()
        for state in self.states:
            if state not in order:
                order.append(state)

        # old names -> new names
        mapping = dict(zip(order, letter_range(len(order))))

        self.start_name = mapping[self.start_name]

        new_states = {}

        for name in self.states:
            new_states[mapping[name]] = self.states[name]

        self.states = new_states

        # Now that states have been remapped in the machine, also switch all transitions.
        for name, state in self.states.items():
            state.name = name
            for symbol, destination in state.transitions.items():
                state.transitions[symbol] = mapping[destination]

    def shortest_path(self, orig, dest):
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

    def remove_state(self, state_name):
        """ Removes a state of this DFA: broken transitions become self-loops."""

        # If we remove the start state, DFA accepts the empty language.
        if state_name == self.start_name:
            new_start = State("empty", False, {symbol: "empty" for symbol in self.alphabet}, self.alphabet)
            self.start_name = "empty"
            self.states = {"empty": new_start}
            return

        del self.states[state_name]

        for state in self.states.values():
            for symbol, dest in state.transitions.items():
                if state_name == dest:
                    state.transitions[symbol] = state.name


def parse_dfa(d):
    """ Takes the description of a DFA, as a string, d. Returns the corresponding DFA object."""

    buf = io.StringIO(d)

    state_names = [s.strip() for s in buf.readline().split(",")]
    alphabet = [s.strip() for s in buf.readline().split(",")]
    start_name = buf.readline().strip()
    accept_states = [s.strip() for s in buf.readline().split(",")]

    if alphabet == ['']: alphabet = []
    if accept_states == ['']: accept_states = []

    transitions = []
    for line in buf:
        transitions.append([s.strip() for s in line.split(",")])

    buf.close()

    if len(state_names) == 0 or state_names == ['']:
        raise ValueError("At least one state required.")

    states = {state_names[i]: State(state_names[i], state_names[i] in accept_states, dict(zip(alphabet, transitions[i])), alphabet, state_names) for i in range(len(state_names))}

    return DFA(states, start_name, alphabet)



###    NFA STUFF    ##########################################################

class NFAState(object):
    """ A particular NFA state.
        Members:
            name:           the name of the State;
            accepting:      whether the state accepts or not;
            transitions:    a map from alphabet symbols plus epsilon to the names of states. """

    epsilon = ""

    def __init__(self, name, accepting, transitions, alphabet, state_names=None):
        self.name = name
        self.accepting = accepting

        # Require this to be a state of an NFA, in particular.
        if sorted(alphabet + [NFAState.epsilon]) != sorted(transitions.keys()):
            raise ValueError("State should contain exactly one (possibly empty) transition for each symbol in the alphabet, plus epsilon.")
        if state_names is not None:
            for state_name in [item for sublist in transitions.values() for item in sublist]:
                if state_name not in state_names:
                    raise ValueError("Transition to state \"" + state_name + "\" not in machine.")

        self.transitions = transitions

    def copy(self):
        transitions = {symbol: list(destinations) for symbol, destinations in self.transitions.items()}
        return NFAState(self.name, self.accepting, transitions, [symbol for symbol in self.transitions.keys() if symbol != NFAState.epsilon])


class NFA(object):
    """ Represents an NFA. To run it, convert to a DFA first. """

    def __init__(self, states, start_name, alphabet):
        self.states = states
        self.alphabet = alphabet

        if start_name not in states:
            raise ValueError("Start state \"" + start_name + "\" is not a state of the machine.")
        self.start_name = start_name

    def epsilon_closure(self, state_names):
        """ Given a set of NFA states, return the names of all states reachable by zero or more epsilon-transitions. """

        closure = []
        to_process = list(state_names)

        while len(to_process) != 0:
            current = to_process.pop()
            if current not in closure:
                closure.append(current)

                for trans in self.states[current].transitions[NFAState.epsilon]:
                    if trans not in to_process:
                        to_process.append(trans)

        # Returns the sorted list so stuff can be compared easily later without resorting.
        return sorted(closure)

    def next_nfa_states(self, start_names, symbol):
        """ Given a set of states of the NFA, return all possible destinations after processing a given symbol. """

        dest_names = []

        for name in self.epsilon_closure(start_names):
            for dest in self.states[name].transitions[symbol]:
                if dest not in dest_names:
                    dest_names.append(dest)

        return self.epsilon_closure(dest_names)

    def dfa(self):
        """ Return a DFA equivalent to this machine. """

        # map, names -> states, to be passed to the DFA State constructor
        dfa_states = {}

        # map, DFA State names -> sets of NFA state names; for tracking the names of states we have already met
        transition_sets = {}

        # NFA state sets yet to be processed into the transition_sets map
        to_process = []

        # Add the start state
        to_process.append(self.epsilon_closure([self.start_name]))
        start_name = new_name("".join(to_process[0]), transition_sets)

        while len(to_process) != 0:
            current_state = to_process.pop()
            if current_state in transition_sets.values():
                continue

            # Determine the transition set for the DFA State we are building
            state_transitions = {}

            # Find all states reachable from the current state set on a given letter.
            for symbol in self.alphabet:
                next_state = self.next_nfa_states(current_state, symbol)

                preexists = False
                for k, v in transition_sets.items():
                    if v == next_state:
                        preexists = True
                        state_transitions[symbol] = k

                if not preexists:
                    state_transitions[symbol] = new_name("".join(next_state), transition_sets)

                if not (preexists or next_state in to_process):
                    to_process.append(next_state)

            cname = new_name("".join(current_state), transition_sets)
            transition_sets[cname] = current_state

            accepting = False
            for s in current_state:
                if self.states[s].accepting:
                    accepting = True
                    break

            dfa_states[cname] = State(cname, accepting, state_transitions, self.alphabet)

        return DFA(dfa_states, start_name, self.alphabet)

    def description(self):
        """ Returns a description of this NFA in the format specified in the assignment specification. """
        description = io.StringIO()

        names = sorted(list(self.states.keys()))
        alphabet = sorted(self.alphabet)

        description.write(",".join(names) + '\n')
        description.write(",".join(alphabet) + '\n')
        description.write(self.start_name + '\n')
        description.write(",".join([n for n in names if self.states[n].accepting])  + '\n')

        for n in names:
            description.write(",".join(["{"+",".join(self.states[n].transitions[s])+"}" for s in alphabet + [NFAState.epsilon]]) + '\n')

        out = description.getvalue()
        description.close()

        return out

    def describe(self):
        print(self.description(), end="")

    def copy(self):
        return NFA({name: self.states[name].copy() for name in self.states.keys()}, self.start_name, list(self.alphabet))

    def rename_states(self):
        """ Redesignates the states of this machine, if they have become unmanageably long unreadable strings. """

        mapping = dict(zip(self.states, letter_range(len(self.states))))

        self.start_name = mapping[self.start_name]

        new_states = {}

        for name in self.states:
            new_states[mapping[name]] = self.states[name]

        self.states = new_states

        for name, state in self.states.items():
            state.name = name
            for symbol, destinations in state.transitions.items():
                state.transitions[symbol] = [mapping[d] for d in destinations if d != '']

    def remove_state(self, state_name):
        if state_name == self.start_name:
            new_start = NFAState("empty", False, {symbol: [] for symbol in self.alphabet + [NFAState.epsilon]}, self.alphabet)
            self.state_name = "empty"
            self.states = {"empty":new_start}

        del self.states[state_name]

        for state in self.states.values():
            for dests in state.transitions.values():
                if state_name in dests:
                    dests.remove(state_name)


def parse_nfa(n):
    """ Takes the description of an NFA, as a string, n. Returns a corresponding DFA."""

    buf = io.StringIO(n)

    state_names = [s.strip() for s in buf.readline().split(",")]
    alphabet = [s.strip() for s in buf.readline().split(",")]
    start_name = buf.readline().strip()
    accept_states = [s.strip() for s in buf.readline().split(",")]

    if alphabet == ['']: alphabet = []
    if accept_states == ['']: accept_states = []

    transitions = []
    for line in buf:
        tlist = [s.strip()[1:-1].split(",") for s in re.split(r"\s*,\s*(?={.*})", line)]
        for i, dest in enumerate(tlist):
            if dest == ['']:
                tlist[i] = []
        transitions.append(tlist)

    buf.close()

    if len(state_names) == 0 or state_names == ['']:
        raise ValueError("At least one state required.")

    states = {state_names[i]: NFAState(state_names[i], state_names[i] in accept_states, dict(zip(alphabet + [NFAState.epsilon], transitions[i])), alphabet, state_names) for i in range(len(state_names))}

    return NFA(states, start_name, alphabet)



###    LANGUAGE OPERATIONS    ##########################################################

def union(machine1, machine2):
    """ Takes two machines, returns a DFA accepting the union of their languages. """

    if isinstance(machine1, NFA):
        machine1 = machine1.dfa().minimised()
    else:
        machine1 = machine1.minimised()

    if isinstance(machine2, NFA):
        machine2 = machine2.dfa().minimised()
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
    union_states = {}

    state_names = []
    for name in machine1.states:
        state_names.append("1" + name)
    for name in machine2.states:
        state_names.append("2" + name)

    # Construct the new start state, with epsilon transitions to the start states of the constituent machines
    start_name = new_name("st", state_names)
    state_names.append(start_name)

    start_transitions = {}
    for symbol in alphabet:
        start_transitions[symbol] = []
    start_transitions[NFAState.epsilon] = ["1" + machine1.start_name, "2" + machine2.start_name]

    union_states[start_name] = NFAState(start_name, False, start_transitions, alphabet, state_names)

    # Construct an error state, required if the input machines are defined over different alphabets
    error_name = new_name("er", state_names)
    state_names.append(error_name)

    error_transitions = {}
    for symbol in alphabet + [NFAState.epsilon]:
        error_transitions[symbol] = [error_name]

    union_states[error_name] = NFAState(error_name, False, error_transitions, alphabet, state_names)

    # States of each constituent machine have a numeral prepended to guarantee uniqueness in the united machine
    # Where a symbol was not defined in the alphabet of one of the machines, transition on that symbol to a common error state.
    for name, state in machine1.states.items():
        new_transitions = {}
        for symbol, dest in state.transitions.items():
            new_transitions[symbol] = ["1" + dest]

        for symbol in absent1:
            new_transitions[symbol] = [error_name]

        new_transitions[NFAState.epsilon] = []

        union_states["1" + name] = NFAState("1" + name, state.accepting, new_transitions, alphabet, state_names)

    for name, state in machine2.states.items():
        new_transitions = {}
        for symbol, dest in state.transitions.items():
            new_transitions[symbol] = ["2" + dest]

        for symbol in absent2:
            new_transitions[symbol] = [error_name]

        new_transitions[NFAState.epsilon] = []

        union_states["2" + name] = NFAState("2" + name, state.accepting, new_transitions, alphabet, state_names)

    return NFA(union_states, start_name, alphabet).dfa().minimised()


def complement(m):
    """ Given a machine accepting L, returns a DFA accepting the complement of L. """
    if isinstance(m, NFA):
        machine = m.dfa()
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
        machine = m.nfa()
    else:
        machine = m.copy()

    #add epsilons from accept states back to start
    for state in machine.states.values():
        if state.accepting:
            state.transitions[NFAState.epsilon] = [machine.start_name]

    #add new start state
    start_name = new_name("st*", machine.states, "*")

    start_transitions = {}
    for symbol in machine.alphabet:
        start_transitions[symbol] = []
    start_transitions[NFAState.epsilon] = [machine.start_name]

    machine.states[start_name] = NFAState(start_name, True, start_transitions, machine.alphabet)
    machine.start_name = start_name

    return machine.dfa()


def concatenation(machine1, machine2):
    """ Takes two machines, returns a DFA accepting the concatenation of their languages. """

    if isinstance(machine1, NFA):
        machine1 = machine1.dfa().minimised()
    if isinstance(machine2, NFA):
        machine2 = machine2.dfa().minimised()


    # Build the common alphabet
    a1 = set(machine1.alphabet)
    a2 = set(machine2.alphabet)

    alphabet = a1 | a2
    absent1 = a2-a1
    absent2 = a1-a2

    alphabet = list(alphabet)

    # Build the set of states for the united machine
    concat_states = {}

    state_names = []
    for name in machine1.states:
        state_names.append("1" + name)
    for name in machine2.states:
        state_names.append("2" + name)

    # Construct an error state, required if the input machines are defined over different alphabets
    error_name = new_name("er", state_names)
    state_names.append(error_name)

    error_transitions = {}
    for symbol in alphabet + [NFAState.epsilon]:
        error_transitions[symbol] = [error_name]

    concat_states[error_name] = NFAState(error_name, False, error_transitions, alphabet, state_names)

    # States of each constituent machine have a numeral prepended to guarantee uniqueness in the united machine
    # Where a symbol was not defined in the alphabet of one of the machines, transition on that symbol to a common error state.
    for name, state in machine1.states.items():
        new_transitions = {}
        for symbol, dest in state.transitions.items():
            new_transitions[symbol] = ["1" + dest]

        for symbol in absent1:
            new_transitions[symbol] = [error_name]

        if state.accepting:
            new_transitions[NFAState.epsilon] = ["2" + machine2.start_name]
        else:
            new_transitions[NFAState.epsilon] = []

        concat_states["1" + name] = NFAState("1" + name, False, new_transitions, alphabet, state_names)

    for name, state in machine2.states.items():
        new_transitions = {}
        for symbol, dest in state.transitions.items():
            new_transitions[symbol] = ["2" + dest]

        for symbol in absent2:
            new_transitions[symbol] = [error_name]

        new_transitions[NFAState.epsilon] = []

        concat_states["2" + name] = NFAState("2" + name, state.accepting, new_transitions, alphabet, state_names)

    return NFA(concat_states, "1" + machine1.start_name, alphabet).dfa().minimised()


def reversal(m):
    """ Returns the reversed machine. That is, the new machine accepts any string the original one does, backwards.
        According the Brzozowski, the new machine is guaranteed to be minimal.
        Although I am not sure my implementation actually produces a minimal machine. """

    if isinstance(m, DFA):
        machine = m.nfa()
        m = m.nfa()
    else:
        machine = m.copy()

    # Construct new start state with epsilon transitions to the previously accepting states
    start_name = new_name("st<>", machine.states, "<>")
    start_transitions = {}
    for symbol in machine.alphabet:
        start_transitions[symbol] = []
    epsilon_transitions = []
    for state in machine.states.values():
        if state.accepting:
            epsilon_transitions.append(state.name)
            state.accepting = False
    start_transitions[NFAState.epsilon] = epsilon_transitions

    # The new accept state is what was the start state
    machine.states[machine.start_name].accepting = True

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
    machine.states[start_name] = NFAState(start_name, False, start_transitions, machine.alphabet)
    machine.start_name = start_name

    machine = machine.dfa()

    # Discard any now-unreachable states
    reachables = machine.start_trans_closure()
    state_names = list(machine.states.keys())
    for name in state_names:
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
        machine1 = machine1.dfa()
    if isinstance(machine2, NFA):
        machine2 = machine2.dfa()

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
            s = find_accepted_string(c2)
        elif empty(machine2):
            s = find_accepted_string(machine1)
        else:
            s = find_accepted_string(intersection(c1, machine2))

        print('Machines differ on "' + s + '".')

    return False



###    UTILITY FUNCTIONS ##########################################################

def clamp(n, minn, maxn):
    return max(minn, min(maxn, n))


def new_name(candidate, nameSet, addend="_"):
    """ Small utility function for finding a name which does not conflict with existing names.
        Since many names are built from atomic concatenations, conflicts are conceivable.
        e.g. a1+a2+a3 == a1a+2a3 """

    cname = candidate

    # Handling the empty set, as empty strings are used for epsilon, etc.
    if cname == "":
        cname = "()"

    while cname in nameSet:
        cname += addend

    return cname


def letter_range(n):
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


def find_accepted_string(machine):
    """ Returns a string accepted by the given machine. """
    if isinstance(machine, NFA):
        machine = machine.dfa()
    machine = machine.minimised()

    if empty(machine):
        return None

    dest = None

    for state in machine.states.values():
        if state.accepting:
            dest = state.name

    return machine.shortest_path(machine.start_name, dest)


def load_fa(filename):
    """ Given a filename, returns the machine described in that file. """
    with open(filename, 'r') as f:
        s = f.read()
        if "{" in s:
            return parse_nfa(s).dfa().minimised()
        else:
            return parse_dfa(s)

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

    def __init__(self, parent, w, h, machine, rename_states=True, annealing=True, springdist=100, gravdist=280, edge_labels=True, state_labels=False):

        Frame.__init__(self, parent, background="white")

        self.width = w
        self.height = h
        self.parent = parent

        self.parent.geometry('%dx%d+%d+%d' % (w, h, 300, 300))

        self.state_labels = state_labels
        self.edge_labels = edge_labels

        self.annealing = annealing

        self.natural_spring = springdist
        self.gravdist = gravdist
        self.spring_const = 0.06
        self.grav_const = 0.02

        self.dragged = None

        if isinstance(machine, NFA):
            self.machine = machine.dfa()
        else:
            self.machine = machine.copy()
        if rename_states:
            self.machine.rename_states()

        self.pack(fill=BOTH, expand=1)
        self.parent.focus_force()

        self.init_ui()
        self.build_machine_graph()
        self.anneal_graph()

    def move_connections(self, item):
        """ Upon moving a node, update the positions of all its connections and labels. """

        dest = self.get_item_centre(item)
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
                    self.canvas.coords(label, *self.proxpoint(coords[:2], self.get_item_centre(self.canvas.find_withtag(distal)[0])))
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
                    self.canvas.coords(label, *self.proxpoint(self.get_item_centre(self.canvas.find_withtag(proximal)[0]), coords[2:]))
                self.canvas.tag_raise(label)

        for loop in loops:
            coords = self.get_box_by_centre([dest[0], dest[1]-20], 10)
            self.canvas.coords(loop, *coords)
            self.canvas.tag_lower(loop)

            labels = self.canvas.find_withtag("l" + str(loop))
            for label in labels:
                #if self.canvas.itemcget(label, "text") == symbol:
                self.canvas.coords(label, *[dest[0], dest[1]-30])
                self.canvas.tag_raise(label)


        state_label = self.canvas.find_withtag("n" + name)
        if state_label != ():
            state_label = state_label[0]
            label_coords = self.canvas.coords(state_label)
            label_coords[0] = dest[0]
            label_coords[1] = dest[1]
            self.canvas.coords(state_label, *label_coords)
            self.canvas.tag_raise(state_label)

        self.canvas.tag_lower(self.delete_text)
        self.canvas.tag_lower(self.delete_rectangle)

    def mouse_click(self, event):
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

    def move_click(self, event):
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
            self.move_connections(self.dragged.item)

    def release_click(self, event):
        if self.dragged is not None:
            if self.canvas.type(self.dragged.item) == "oval":
                del_coords = self.canvas.coords(self.delete_rectangle)
                item_coords = self.canvas.coords(self.dragged.item)

                if (item_coords[0] > del_coords[0] and item_coords[0] < del_coords[2]-40 and
                    item_coords[1] > del_coords[1] and item_coords[1] < del_coords[3]):
                    self.machine.remove_state(self.canvas.gettags(self.dragged.item)[0])
                    self.build_machine_graph()

        self.dragged = None

    def resize_canvas(self, event):
        """ Update the bounds of the canvas when the window is resized. """
        self.width = event.width
        self.height = event.height

        self.gravscale.place(x=120, y=self.height-70)
        self.springscale.place(x=10, y=self.height-70)

        self.graventry.place(x=350, y=self.height-36)
        self.graventry_button.place(x=400, y=self.height-36)

        self.springentry.place(x=235, y=self.height-36)
        self.springentry_button.place(x=285, y=self.height-36)

        self.edgelabel_check.place(x=self.width-200, y=10)
        self.statelabel_check.place(x=self.width-100, y=10)

        self.quitbutton.place(x=self.width-40, y=self.height-95)

        self.file_entry.place(x=self.width-155, y=self.height-65)
        self.file_entry_button.place(x=self.width-220, y=self.height-65)

        self.checkentry.place(x=self.width-155, y=self.height-36)
        self.checkentry_button.place(x=self.width-243, y=self.height-36)

    def get_item_centre(self, item):
        coords = self.canvas.coords(item)
        return [sum(x)/2 for x in zip(coords[:2], coords[2:])]

    def get_box_by_centre(self, p, radius):
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

    def toggle_state_labels(self):
        self.state_labels = not self.state_labels

        labels = self.canvas.find_withtag("tsLabel")

        newstate = "hidden"

        if self.state_labels:
            newstate = "normal"

        for label in labels:
            self.canvas.itemconfig(label, state=newstate)

    def toggle_edge_labels(self):
        self.edge_labels = not self.edge_labels

        labels = self.canvas.find_withtag("teLabel")

        newstate = "hidden"

        if self.edge_labels:
            newstate = "normal"

        for label in labels:
            self.canvas.itemconfig(label, state=newstate)

    def toggle_annealing(self):
        self.annealing = not self.annealing

        if self.annealing:
            self.simbutton.config(relief="sunken")
            self.parent.after(17, self.anneal_graph)
        else:
            self.simbutton.config(relief="groove")

    def update_grav_dist(self, val):
        self.gravdist = int(val)

    def update_spring_dist(self, val):
        self.natural_spring = int(val)

    def update_spring_const(self):
        self.spring_const = float(self.springentry.get())
        self.parent.focus()

    def update_grav_const(self):
        self.grav_const = float(self.graventry.get())
        self.parent.focus()

    def anneal_graph(self):
        """ Settles the graph into a possibly-more-pleasing shape than a random splatter.
            It is a little rubbish at the moment, though. """

        newcoords = []

        numnodes = len(self.nodes)

        # There is no force exerted by a single node or fewer.
        if numnodes < 2:
            return

        # Calculate forces for every node in the graph.
        for i in range(numnodes):
            spring_vectors = []
            grav_vectors = []
            forces = []

            centre = self.get_item_centre(self.nodes[i])
            selfname = self.canvas.gettags(self.nodes[i])[0]

            # Find the vectors to this node from every other node in the graph.
            for p in self.nodes[:i] + self.nodes[i+1:]:
                exocentre = self.get_item_centre(p)
                diff = [exocentre[0]-centre[0], exocentre[1]-centre[1]]

                grav_vectors.append(diff)

                distname = self.canvas.gettags(p)[0]
                if distname not in self.machine.states[selfname].transitions.values():
                    if selfname not in self.machine.states[distname].transitions.values():
                        continue
                spring_vectors.append(diff)

            # Calculate the forces on this node from all nodes connected to it by an edge.
            for v in spring_vectors:
                scale = math.sqrt(v[0]**2 + v[1]**2)/self.natural_spring

                if scale == 0:
                    scale = 0.001

                relaxed = [v[0]/scale, v[1]/scale]

                x = (v[0] - relaxed[0])*self.spring_const
                y = (v[1] - relaxed[1])*self.spring_const

                forces.append([x, y])

            # Every node in the graph exerts a force on every other node, more weakly than springs.
            for v in grav_vectors:
                scale = math.sqrt(v[0]**2 + v[1]**2)/self.gravdist

                if scale == 0:
                    scale = -0.001

                relaxed = [v[0]/scale, v[1]/scale]

                x = (v[0] - relaxed[0])*self.grav_const
                y = (v[1] - relaxed[1])*self.grav_const

                forces.append([x, y])

            force = [sum(component) for component in zip(*forces)]

            centre = [clamp(centre[0]+force[0], 20, self.width - 20), clamp(centre[1]+force[1], 20, self.height - 20)]
            newcoords.append(self.get_box_by_centre(centre, 20))

        # Move the nodes according to the net force on them, but don't move items currently being dragged.
        for node, coord in zip(self.nodes, newcoords):
            if self.dragged is not None:
                if node == self.dragged.item[0]:
                    continue
            self.canvas.coords(node, *coord)
            self.move_connections(node)

        if self.annealing:
            self.parent.after(17, self.anneal_graph)

    def build_machine_graph(self):
        """ Creates and tags all the nodes, labels, interconnections for drawing the given machine. """

        self.canvas.delete("all")

        self.nodes = []

        edgelabel_state = "normal" if self.edge_labels else "hidden"
        statelabel_state = "normal" if self.state_labels else "hidden"

        for state in self.machine.states.values():
            name = state.name
            thickness = 1
            colour = "#ccc"
            activecolour = "#eee"

            if state.accepting:
                thickness = 3

            pattern = []

            if state.name == self.machine.start_name:
                pattern = [15, 8]
                colour = "#fff"
                activecolour = "#fee"

            x = random.randrange(self.width-40)
            y = random.randrange(40, self.height-80)


            self.nodes.append(self.canvas.create_oval(x, y, x+40, y+40, outline="#444", fill=colour, activefill=activecolour, tag=name, width=thickness, dash=pattern))

            self.canvas.create_text(x+20, y+20, fill="#444", font=("Purisa", 14), text=name, tags=("n"+name, "tsLabel"), state=statelabel_state)

            for sym, dest in state.transitions.items():
                labeloffset = random.choice(['n', 'e', 's', 'w'])
                loopoffset = random.choice(['center', 'sw', 'se'])

                if name == dest:
                    l = self.canvas.create_oval(x+10, y-10, x+30, y+10, fill="", tags=("i" + name, "s" + sym))
                    self.canvas.create_text(x+20, y-10, fill="#334", font=("Purisa", 13), text=sym, tags=("l"+str(l), "teLabel"), anchor=loopoffset, state=edgelabel_state)
                    self.canvas.tag_lower(l)
                else:
                    l = self.canvas.create_line(x, y, x+40, y+40, fill="#555", smooth=1, arrow="last", arrowshape=[21, 26, 3], tags=("o" + name, "d" + dest, "s" + sym))
                    self.canvas.create_text(x+20, y+20, anchor=labeloffset, fill="#334", font=("Purisa", 13), text=sym, tags=("l"+str(l), "teLabel"), state=edgelabel_state)
                    self.canvas.tag_lower(l)

        for node in self.nodes:
            self.move_connections(node)


        self.delete_text = self.canvas.create_text([15, 45], anchor='nw', text="Delete\nNode", font=("Helvetica, 10"), width=50, tag="delete")
        self.canvas.tag_lower(self.delete_text)
        self.delete_rectangle = self.canvas.create_rectangle([10, 40, 70, 100], fill="#ddd", tag="delete")
        self.canvas.tag_lower(self.delete_rectangle)


    def describe_active_machine(self):
        self.machine.describe()
        print()

    def check_active_machine(self):
        self.machine.check_string(self.checkentry.get())
        self.checkentry.delete(0, "end")
        print()

    def mod_active_machine(self, transform, sim=True):
        """ Replaces the current machine with a transformed version."""
        if self.annealing:
            self.toggle_annealing()
            self.parent.after(100, self.mod_active_machine, transform)
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
            self.machine.rename_states()
        elif transform == "load":
            self.load_active_machine(self.file_entry.get()) #TODO: Work out why I couldn't pass this as an argument

        self.build_machine_graph()

        self.parent.focus()

        if sim:
            self.toggle_annealing()

    def load_active_machine(self, filename):
        """ Replaces the currently-active machine with one defined in filename, if it is valid. """
        try:
            with open(filename, 'r') as f:
                s = f.read()
                if "{" in s:
                    self.machine = parse_nfa(s).dfa().minimised()
                else:
                    self.machine = parse_dfa(s)
        except:
            self.file_entry.delete(0, "end")

    def init_ui(self):
        """ Build the interface. """

        self.parent.title("DFA Viz")
        self.parent.bind("<Escape>", lambda e: self.parent.destroy())
        self.bind("<Configure>", self.resize_canvas)

        self.canvas = Canvas(self, background="white")
        self.canvas.bind("<Button-1>", self.mouse_click)
        self.canvas.bind("<B1-Motion>", self.move_click)
        self.canvas.bind("<ButtonRelease-1>", self.release_click)

        bfont = ("Helvetica", 10)

        self.simbutton = Button(self, font=bfont, padx=0, pady=0, text="Toggle Sim", relief="sunken", command=self.toggle_annealing)
        self.simbutton.place(x=10, y=10)


        self.gravscale = Scale(self, from_=20, to=500, orient="horizontal", label="grav radius", command=self.update_grav_dist)
        self.gravscale.set(self.gravdist)
        self.gravscale.place(x=120, y=self.height-70)

        self.springscale = Scale(self, from_=20, to=500, orient="horizontal", label="spring radius", command=self.update_spring_dist)
        self.springscale.set(self.natural_spring)
        self.springscale.place(x=10, y=self.height-70)


        self.springentry = Entry(self, font=bfont, width=6, justify="right", bg="#eee")
        self.springentry.place(x=235, y=self.height-36)
        self.springentry.insert(0, str(self.spring_const))
        self.springentry_button = Button(self, font=bfont, padx=0, pady=0, text="spr const", command=self.update_spring_const)
        self.springentry_button.place(x=285, y=self.height-36)
        self.springentry.bind("<Return>", lambda e: self.update_spring_const())

        self.graventry = Entry(self, font=bfont, width=6, justify="right", bg="#eee")
        self.graventry.place(x=350, y=self.height-36)
        self.graventry.insert(0, str(self.grav_const))
        self.graventry_button = Button(self, font=bfont, padx=0, pady=0, text="grav const", command=self.update_grav_const)
        self.graventry_button.place(x=400, y=self.height-36)
        self.graventry.bind("<Return>", lambda e: self.update_grav_const())

        self.statelabel_check = Checkbutton(self, text="State Labels", command=self.toggle_state_labels)
        self.statelabel_check.place(x=self.width-100, y=10)
        if self.state_labels:
            self.statelabel_check.select()

        self.edgelabel_check = Checkbutton(self, text="Edge Labels", command=self.toggle_edge_labels)
        self.edgelabel_check.place(x=self.width-200, y=10)
        if self.edge_labels:
            self.edgelabel_check.select()


        self.minbutton = Button(self, text="Minimise", font=bfont, padx=0, pady=0, command=lambda: self.mod_active_machine("minimise"))
        self.minbutton.place(x=90, y=10)

        self.compbutton = Button(self, text="Complement", font=bfont, padx=0, pady=0, command=lambda: self.mod_active_machine("complement"))
        self.compbutton.place(x=160, y=10)

        self.revbutton = Button(self, text="Reverse", font=bfont, padx=0, pady=0, command=lambda: self.mod_active_machine("reverse"))
        self.revbutton.place(x=250, y=10)

        self.starbutton = Button(self, text="Star", font=bfont, padx=0, pady=0, command=lambda: self.mod_active_machine("star"))
        self.starbutton.place(x=310, y=10)

        self.renamebutton = Button(self, text="Redesignate", font=bfont, padx=0, pady=0, command=lambda: self.mod_active_machine("rename"))
        self.renamebutton.place(x=350, y=10)

        self.describebutton = Button(self, text="Describe", font=bfont, padx=0, pady=0, command=self.describe_active_machine)
        self.describebutton.place(x=435, y=10)

        self.quitbutton = Button(self, text="Quit", font=bfont, padx=0, pady=0, command=self.parent.destroy)
        self.quitbutton.place(x=self.width-45, y=self.height-106)


        self.file_entry = Entry(self, font=bfont, bg="#eee")
        self.file_entry.place(x=self.width-155, y=self.height-70)
        self.file_entry_button = Button(self, text="Load File", font=bfont, padx=0, pady=0, command=lambda: self.mod_active_machine("load"))
        self.file_entry_button.place(x=self.width-220, y=self.height-70)
        self.file_entry.bind("<Return>", lambda e: self.mod_active_machine("load"))


        self.checkentry = Entry(self, font=bfont, bg="#eee")
        self.checkentry.place(x=self.width-155, y=self.height-36)
        self.checkentry_button = Button(self, text="Check String", font=bfont, padx=0, pady=0, command=self.check_active_machine)
        self.checkentry_button.place(x=self.width-243, y=self.height-36)
        self.checkentry.bind("<Return>", lambda e: self.check_active_machine())

        self.delete_rectangle = self.canvas.create_rectangle([10, 40, 70, 100], fill="#ddd", tag="delete")
        self.delete_text = self.canvas.create_text([15, 45], anchor='nw', text="Delete\nNode", font=bfont, width=50, tag="delete")

        self.canvas.pack(fill=BOTH, expand=1)


def draw_dfa(machine, rename=True, grav=280, spring=100, eLabels=True, sLabels=False):
    """ Draws and anneals the given machine. """
    root = Tk()
    win = FAContext(root, 800, 600, machine, rename_states=rename, gravdist=grav, springdist=spring, edge_labels=eLabels, state_labels=sLabels)
    root.mainloop()


###    RUNTIME THINGS    ##########################################################

def default_machine(s):
    """ Checks a string on the machine accepting input of length 3, or which does not contain the substring '101' """

    # We could build the machine from scratch if we wished, in this way:
    # Assuming L1.dfa and L4.dfa exist, with the correct contents.
    # union(load_fa("L1.dfa"), load_fa("L2.dfa")).check_string(s)

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

    parse_dfa(description).check_string(s)


def demo():
    """ A demonstration function, runs most available functions one way or another. """

    print("NFA Parsing\n-----------\n")

    abc_string = (
        "S,A,B,C\n"
        "a,b,c\n"
        "S\n"
        "C\n"
        "{A},{},{},{}\n"
        "{},{B},{},{}\n"
        "{},{},{C},{}\n"
        "{},{},{},{}\n")

    abc = parse_nfa(abc_string)

    print("An NFA accepting 'abc': \n" + abc_string + "\nOn 'abc':")
    abc.dfa().check_string("abc")
    print("\nOn 'cba':")
    abc.dfa().check_string("cba")



    print("\n\n\nExtra-Alphabetic Symbol Handling\n--------------------------------\n")
    print("The previous machine is defined only on [abc], but dynamically transitions to an error state for other input.\n")

    abc.dfa().check_string("abFabc")



    print("\n\n\nNFA <-> DFA Conversion\n----------------------\n")
    print("If we convert the previous NFA to a DFA, we get the following description:\n")
    abc.dfa().describe()
    print("\nWhere '()' has been substituted for the empty set.\n")

    print("If we define a DFA, for example:\n")

    dfa1_string = (
        "A,B,C\n"
        "s,t\n"
        "A\n"
        "B\n"
        "B,A\n"
        "C,A\n"
        "C,B\n")

    dfa1 = parse_dfa(dfa1_string)

    print(dfa1_string + "\nWe can represent this in the NFA format as well:\n")

    dfa1.nfa().describe()


    print("\n\n\nDFA Minimisation\n----------------\n")
    print("Let us define a relatively large NFA. The following represents L1 U L2 from Task 1:\n")

    t1_string = ("S,L11,L12,L13,L21,L22,L23,L24,U\n"
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

    t1 = parse_nfa(t1_string)

    print(t1_string + "\nWe may convert this to a DFA, yielding:\n")

    t2 = t1.dfa()

    t2.describe()

    print("\nWhich itself can be minimised to this 8-state machine:\n")

    t3 = t2.minimised()
    t3.describe()

    print("\nOr, with the states renamed,\n")

    t3.rename_states()
    t3.describe()

    print("\nHence, we can check strings against the NFA by using the equivalent DFA:\n")

    t3.check_string("101")
    print()
    t3.check_string("1010")



    print("\n\n\nLanguage Operations\n-------------------\n")
    print("We can obtain a machine derived from the union of two other machines.")
    print("Further, we are able to do this even when the alphabets of the constituent machines differ.")
    print("For example, here are the descriptions of two DFAs on different alphabets:\n")


    num_string = ("1,2,3,4\n"
                "0,1\n"
                "1\n"
                "1,2,3\n"
                "1,2\n"
                "3,2\n"
                "1,4\n"
                "4,4\n")

    alphanum_string = (
        "A,B,C\n"
        "a,b,0\n"
        "A\n"
        "B\n"
        "B,A,B\n"
        "C,A,C\n"
        "C,B,A\n")

    numerical = parse_dfa(num_string)
    alphanumerical = parse_dfa(alphanum_string)

    print(num_string)
    print(alphanum_string)

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

    oh_one_string = ("S,O,F\n"
                   "0,1\n"
                   "S\n"
                   "F\n"
                   "{O},{},{}\n"
                   "{},{F},{}\n"
                   "{},{},{}\n")

    ccc_string = ("C1,C2,C3,C4\n"
                 "c\n"
                 "C1\n"
                 "C4\n"
                 "{C2},{}\n"
                 "{C3},{}\n"
                 "{C4},{}\n"
                 "{},{}\n")

    print(oh_one_string + "\n")
    print(ccc_string +"\n")

    oh_one = parse_nfa(oh_one_string).dfa().minimised()
    ccc = parse_nfa(ccc_string).dfa().minimised()

    print("The machine for the regex looks like this:\n")

    regex = intersection(concatenation(abc, concatenation(star(union(reversal(abc), oh_one)), ccc)), complement(concatenation(concatenation(abc, oh_one), ccc)))
    regex.describe()

    print("\nOr, renamed:\n")
    regex.rename_states()
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

    a1 = parse_dfa(a1s)
    a2 = parse_dfa(a2s)

    equivalent(a1, a2, True)

    print("\n" + a1s + "\n" + a2s)

    print("In a similar vein, we can find the shortest string that will transition between any two states in a machine.")
    print("In particular, it's useful for finding an example string which is accepted by a machine, if such a string exists.")
    print("For example, the above regex machine accepts the string '", end="")
    print(find_accepted_string(regex) + "'.")



    print("\n\nVisualisation\n-------------\n")
    print("We can display visually the machine for the task 2. Click the Minimise button to get the machine for task 3.")
    print("Drag nodes around with the mouse.")
    print("\nSome other attractive examples are available by uncommenting lines in the source.")
    print("You can also see your own machines, if they have been defined in files, by using the input on the lower right,")
    print("or by invoking the program with the arguments '--draw filename', and filename can be empty.\n")
    print("Be careful with the star and reversal operations on large machines.\nSee the source for more exhaustive notes.\n")
    print("-|-\n/ \\\n")

    draw_dfa(t2, rename=False, sLabels=True)
    draw_dfa(abc)

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
    max_incoming = [n for n in counts if counts[n] == maximum][0]
    regex.remove_state(max_incoming)

    # Other examples
    #draw_dfa(parse_dfa(florette), rename=False, spring=20, grav=220, eLabels=False)
    #draw_dfa(regex, rename=False)
    #draw_dfa(u)


if __name__ == '__main__':
    if len(sys.argv) >= 3:
        if sys.argv[1] == "--draw":
            draw_dfa(load_fa(sys.argv[2]), rename=False)
        elif len(sys.argv) == 4:
            if sys.argv[1] == "--union":
                draw_dfa(union(load_fa(sys.argv[2]), load_fa(sys.argv[3])))
            elif sys.argv[1] == "--concat":
                draw_dfa(concatenation(load_fa(sys.argv[2]), load_fa(sys.argv[3])))
            elif sys.argv[1] == "--intersect":
                draw_dfa(intersection(load_fa(sys.argv[2]), load_fa(sys.argv[3])))
            else:
                load_fa(sys.argv[2]).check_string(sys.argv[1])
        else:
            load_fa(sys.argv[2]).check_string(sys.argv[1])
    elif len(sys.argv) == 2:
        if sys.argv[1] == "--demo":
            demo()
        elif sys.argv[1] == "--draw":
            draw_dfa(parse_dfa(".\n\n.\n\n\n"))
        else:
            default_machine(sys.argv[1])
    else:
        print("rejected")