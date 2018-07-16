// Copyright (c) 2013-2018 K Team. All Rights Reserved.
package org.kframework.kil;

/**
 *
 */
public class Restrictions extends ModuleItem {
    NonTerminal sort;
    Terminal terminal;
    String pattern;

    public NonTerminal getNonTerminal() {
        return sort;
    }

    public void setNonTerminal(NonTerminal sort) {
        this.sort = sort;
    }

    public Restrictions(NonTerminal sort, Terminal terminal, String pattern) {
        this.sort = sort;
        this.terminal = terminal;
        this.pattern = pattern;
    }

    public Restrictions(Restrictions node) {
        super(node);
        this.sort = node.sort;
        this.terminal = node.terminal;
        this.pattern = node.pattern;
    }

    @Override
    public String toString() {
        return "  syntax " + (sort != null ? sort : terminal) + " -/- " + pattern + "\n";
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (!(obj instanceof Restrictions))
            return false;
        Restrictions syn = (Restrictions) obj;
        if (!pattern.equals(syn.pattern))
            return false;

        if (!(sort != null ? sort.equals(syn.sort) : terminal.equals(syn.terminal)))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        int hash = pattern.hashCode();
        hash += sort != null ? sort.hashCode() : terminal.hashCode();
        return hash;
    }

    @Override
    public Restrictions shallowCopy() {
        return new Restrictions(this);
    }

    public Terminal getTerminal() {
        return terminal;
    }

    public void setTerminal(Terminal terminal) {
        this.terminal = terminal;
    }

    public String getPattern() {
        return pattern;
    }

    public void setPattern(String pattern) {
        this.pattern = pattern;
    }
}
