package org.kframework.kprove;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;
import org.kframework.unparser.PrintOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.SMTOptions;

import java.io.File;
import java.util.List;

@RequestScoped
public class KProveOptions {

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public DefinitionLoadingOptions definitionLoading = new DefinitionLoadingOptions();

    @Parameter(description="<file>")
    private List<String> parameters;

    private File specFile;

    public synchronized File specFile(FileUtil files) {
        if (specFile == null) {
            if (parameters == null || parameters.size() == 0) {
                throw KEMException.criticalError("You have to provide exactly one main file in order to do outer parsing.");
            }
            specFile = files.resolveWorkingDirectory(parameters.get(0));
        }
        return specFile;
    }

    @ParametersDelegate
    public SMTOptions smt = new SMTOptions();

    @ParametersDelegate
    public PrintOptions print = new PrintOptions();

    // TODO: Should eventually allow this option in non-proof mode
    @Parameter(names={"--debugg"}, description="Output proof debugging information")
    public boolean debugg = false;

    @Parameter(names={"--debugg-path"}, description="Path where the debugg output should be stored")
    public String debuggPath;

    @Parameter(names={"--spec-module", "-sm"}, description="Name of module containing specification to prove")
    public String specModule;

    @Parameter(names={"--def-module", "-m"}, description="Name of module containing definition to prove under")
    public String defModule;
}
