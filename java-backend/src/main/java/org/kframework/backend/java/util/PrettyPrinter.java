// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.unparser.KPrint;

/**
 * @author Denis Bogdanas
 * Created on 07-Feb-19.
 */
public class PrettyPrinter {
    public final KPrint kprint;
    public final Definition def;
    public final Module module;

    public PrettyPrinter(KPrint kprint, Definition def) {
        this.kprint = kprint;
        this.def = def;
        this.module = def.getModule("LANGUAGE-PARSING").get();
    }

    public void prettyPrint(K target) {
        kprint.prettyPrint(def, module, kprint::outputFile, target);
    }

    public byte[] prettyPrintBytes(K target) {
        return kprint.prettyPrint(def, module, target);
    }
}
