// Copyright (c) 2012-2018 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.utils.StringUtil;

/** A terminal in a {@link Production}. */
public class Terminal extends ProductionItem {

    private String terminal;

    private boolean caseInsensitive = false;

    public Terminal(String terminal, boolean caseInsensitive) {
        super();
        this.terminal = terminal;
        this.caseInsensitive = caseInsensitive;
    }

    public Terminal(String terminal) {
        super();
        this.terminal = terminal;
    }

    public Terminal(Terminal terminal) {
        super(terminal);
        this.terminal = terminal.terminal;
        this.caseInsensitive = terminal.caseInsensitive;
    }

    public void setTerminal(String terminal) {
        this.terminal = terminal;
    }

    public String getTerminal() {
        return terminal;
    }

    @Override
    public String toString() {
        return StringUtil.enquoteCString(terminal, caseInsensitive ? '\'' : '"');
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (obj == this)
            return true;
        if (!(obj instanceof Terminal))
            return false;

        Terminal trm = (Terminal) obj;

        if (!trm.terminal.equals(this.terminal))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return this.terminal.hashCode();
    }

    @Override
    public Terminal shallowCopy() {
        return new Terminal(this);
    }

    public boolean isCaseInsensitive() {
        return caseInsensitive;
    }

    public void setCaseInsensitive(boolean caseInsensitive) {
        this.caseInsensitive = caseInsensitive;
    }
}
