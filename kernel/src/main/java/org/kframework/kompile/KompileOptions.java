// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backends;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.StringListConverter;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

@RequestScoped
public class KompileOptions implements Serializable {


    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public OuterParsingOptions outerParsing = new OuterParsingOptions();

    // Common options
    @Parameter(names="--backend", description="Choose a backend. <backend> is one of [ocaml|coq]. Each creates the kompiled K definition.")
    public String backend = Backends.OCAML;

    @Parameter(names="--doc-style", description="Specify a style option for the package 'k.sty' (when '--backend [pdf|latex]' is used) or path to an alternative .css file (when '--backend html' is used).")
    private String docStyle;

    private static final String DEFAULT_DOC_STYLE = "poster,style=bubble";

    public String docStyle() {
        if (backend.equals(Backends.HTML)) {
            if (docStyle == null) {
                return "k-definition.css";
            }
            return docStyle;
        }
        if (docStyle == null) {
            return DEFAULT_DOC_STYLE;
        }
        if (docStyle.startsWith("+")) {
            return DEFAULT_DOC_STYLE + "," + docStyle.substring(1);
        }
        return docStyle;
    }

    @Parameter(names="--main-module", description="Specify main module in which a program starts to execute. This information is used by 'krun'. The default is the name of the given K definition file without the extension (.k).")
    private String mainModule;

    public String mainModule(FileUtil files) {
        if (mainModule == null) {
            return FilenameUtils.getBaseName(outerParsing.mainDefinitionFile(files).getName()).toUpperCase();
        }
        return mainModule;
    }

    @Parameter(names="--syntax-module", description="Specify main module for syntax. This information is used by 'krun'. (Default: <main-module>-SYNTAX).")
    private String syntaxModule;

    public String syntaxModule(FileUtil files) {
        if (syntaxModule == null) {
            return mainModule(files) + "-SYNTAX";
        }
        return syntaxModule;
    }

    @Parameter(names="--transition", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of tags designating rules to become transitions.")
    public List<String> transition = Collections.singletonList(DEFAULT_TRANSITION);

    public static final String DEFAULT_TRANSITION = "transition";

    @Parameter(names="--non-strict", description="Do not add runtime sort checks for every variable's inferred sort.")
    private boolean nonStrict;

    public boolean strict() { return !nonStrict; }

    @Parameter(names="--coverage", description="Generate coverage data when executing semantics.")
    public boolean coverage;

    @ParametersDelegate
    public Experimental experimental = new Experimental();

    public static final class Experimental implements Serializable {

        // Experimental options
        @Parameter(names="--step", description="Name of the compilation phase after which the compilation process should stop.")
        public String step;

        @Parameter(names="--add-top-cell", description="Add a top cell to configuration and all rules.")
        public boolean addTopCell = false;

        @Parameter(names="--heat-cool-by-strategies", description="Control heating and cooling using strategies.")
        public boolean heatCoolStrategies = false;

        @Parameter(names="--k-cells", description="Cells which contain komputations.")
        public List<String> kCells = Arrays.asList("k");

        @ParametersDelegate
        public SMTOptions smt = new SMTOptions();

        @Parameter(names="--documentation", listConverter=StringListConverter.class, description="<string> is a comma-separated list of tags designating rules to be included in the file generated with --backend=doc")
        public List<String> documentation = Collections.singletonList("documentation");

        @Parameter(names="--legacy-kast", description="Compile with settings based on the old KAST structure")
        public boolean legacyKast = false;

        @Parameter(names="--kore-prove", description="Compile with the KORE pipeline for proving.")
        public boolean koreProve = false;
    }
}
