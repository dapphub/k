// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.kernel;

import com.google.common.collect.SetMultimap;
import org.kframework.parser.concrete2kore.kernel.Grammar.EntryState;
import org.kframework.parser.concrete2kore.kernel.Grammar.ExitState;
import org.kframework.parser.concrete2kore.kernel.Grammar.NextableState;
import org.kframework.parser.concrete2kore.kernel.Grammar.NonTerminal;
import org.kframework.parser.concrete2kore.kernel.Grammar.NonTerminalState;
import org.kframework.parser.concrete2kore.kernel.Grammar.PrimitiveState;
import org.kframework.parser.concrete2kore.kernel.Grammar.RegExState;
import org.kframework.parser.concrete2kore.kernel.Grammar.RuleState;
import org.kframework.parser.concrete2kore.kernel.Grammar.State;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Helper class in the parser that finds all of the entryNullable NonTerminals in a grammar.
 */
public class Nullability {
    /**
     * Accumulated set of "entry nullable" states.
     * A state is entry nullable if we can get to the start of it from the start of its
     * non-terminal without consuming input.
     */
    private Set<State> entryNullable = new HashSet<>();

    /**
     * Accumulated set of "first" states.
     * A state is first for a particular nonterminal if we can reach that state from the
     * start of that non-terminal without consuming any tokens.
     */
    private final List<boolean[]> firstStates;
    private final int[] stateToToken;

    /**
     * Nullability of a state is based on the following two implications:
     * A. EntryState state => entryNullable(state)
     * B. entryNullable(state) && childNullable(state) => entryNullable(state.next)
     * Where childNullable(state) is true when it is possible to get from the
     * start of the state to the end of the state without consuming input.
     *
     * The following algorithm is a least fixed-point algorithm for solving those implications.
     * mark(state) is called when we discover an implication implying entryNullable(state). We can
     * discover this implication one of three ways:
     *
     * 1. A state is an entry state (see rule A)
     * 2. The entryNullable(state) in rule B becomes true (in which case we check childNullable).)
     * 3. The childNullable(state) in rule B becomes true (in which case we check entryNullable(state).)
     * (ChildNullable(state) becomes true when an exit state becomes entryNullable.)
     * @param grammar the grammar object.
     * @return A set with all the NonTerminals that can become entryNullable.
     */
    public Nullability(Grammar grammar, int maxState) {
        assert grammar != null;
        firstStates = Arrays.asList(new boolean[grammar.getAllNonTerminals().size()][]);
        stateToToken = new int[maxState];
        for (int i = 0; i < maxState; i++) {
            stateToToken[i] = -1;
        }
        // 1. get all entryNullable states
        // list NonTerminals reachable from the start symbol.
        // the value of the map keeps a reference to all the states which call NonTerminals
        SetMultimap<NonTerminal, NonTerminalState> nonTerminalCallers = grammar.getNonTerminalCallers();

        // A state is entryNullable iff the *start* of it is reachable from the entry of its nt without consuming input
        // A non-terminal is entryNullable if its exit state is entryNullable
        for (NonTerminal entry : nonTerminalCallers.keySet()) {
            // there are hidden NonTerminals (like List{...} special)
            // the only way to get to them is with the full traversal
            markNullable(entry.entryState, nonTerminalCallers);
        }
        for (NonTerminal entry : grammar.getAllNonTerminals()) {
            boolean[] firstStatesForNt = new boolean[maxState];
            firstStates.set(entry.unique, firstStatesForNt);
            markFirst(firstStatesForNt, entry.entryState);
        }
    }

    /**
     * marks a state as entryNullable if it is not already, and calls mark on any
     * states that should be entryNullable as a result.
     */
    private void markNullable(State state, SetMultimap<NonTerminal, NonTerminalState> nonTerminalCallers) {
        if (!entryNullable.contains(state)) {
            entryNullable.add(state);
            if (state instanceof NextableState) {
                if (isNullable(state))
                    for (State s : ((NextableState) state).next)
                        markNullable(s, nonTerminalCallers);
            } else {
                assert state instanceof ExitState: "Expected element of type ExitState: " + state;
                // previous calls to childNullable would have returned False
                // so now we restart those recursions
                for (State s : nonTerminalCallers.get(state.nt)) {
                    if (entryNullable.contains(s)) {
                        for (State child : ((NextableState)s).next) {
                            markNullable(child, nonTerminalCallers);
                        }
                    }
                }
            }
        }
    }

    private void markFirst(boolean[] firstStatesForNt, State state) {
        if (!firstStatesForNt[state.unique]) {
            firstStatesForNt[state.unique] = true;
            if (state instanceof RegExState) {
                stateToToken[state.unique] = ((RegExState) state).kind;
            }
            if (state instanceof NextableState) {
                if (isNullable(state))
                    for (State s : ((NextableState)state).next)
                        markFirst(firstStatesForNt, s);
                if (state instanceof NonTerminalState) {
                    markFirst(firstStatesForNt, ((NonTerminalState) state).child.entryState);
                }
            }
        }
    }

    /**
     * Checks if a state can parse without consuming characters.
     * @param state The state to check
     * @return true if the state can parse without consuming characters and false otherwise
     */
    public boolean isNullable(State state) {
        return (state instanceof EntryState) ||
                (state instanceof ExitState) ||
                (state instanceof RuleState) ||
               ((state instanceof PrimitiveState) && ((PrimitiveState)state).isNullable()) ||
               ((state instanceof NonTerminalState) && isNullable(((NonTerminalState) state).child));
    }

    public boolean isNullable(NonTerminal nt) { return entryNullable.contains(nt.exitState); }

    public boolean[] getFirstSet(NonTerminal nt, Scanner scanner, List<State> allStates) {
        boolean[] firstStatesForNt = firstStates.get(nt.unique);
        boolean[] firstSet = new boolean[scanner.getMaxToken() + 1];
        for (int i = 0; i < firstStatesForNt.length; i++) {
            if (stateToToken[i] >= 0) {
                firstSet[stateToToken[i]] |= firstStatesForNt[i];
            }
        }
        return firstSet;
    }
}
