// Copyright (c) 2013-2018 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.compile.Backend;
import org.kframework.main.FrontEnd;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import java.util.ArrayList;
import java.util.List;

public class KompileFrontEnd extends FrontEnd {

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KompileModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }


    private final KompileOptions options;
    private final Provider<Backend> koreBackend;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final BinaryLoader loader;
    private final FileUtil files;

    @Inject
    KompileFrontEnd(
            KompileOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Provider<Backend> koreBackend,
            Stopwatch sw,
            KExceptionManager kem,
            BinaryLoader loader,
            JarInfo jarInfo,
            FileUtil files) {
        super(kem, options.global, usage, experimentalUsage, jarInfo, files);
        this.options = options;
        this.koreBackend = koreBackend;
        this.sw = sw;
        this.kem = kem;
        this.loader = loader;
        this.files = files;
    }

    @Override
    public int run() {
        if (!options.outerParsing.mainDefinitionFile(files).exists()) {
            throw KEMException.criticalError("Definition file doesn't exist: " +
                    options.outerParsing.mainDefinitionFile(files).getAbsolutePath());
        }

        Kompile kompile = new Kompile(options, files, kem, sw);
        Backend backend = koreBackend.get();
        CompiledDefinition def = kompile.run(options.outerParsing.mainDefinitionFile(files), options.mainModule(files), options.syntaxModule(files), backend.steps());
        loader.saveOrDie(files.resolveKompiled("compiled.bin"), def);
        backend.accept(def);
        loader.saveOrDie(files.resolveKompiled("timestamp"), "");
        sw.printIntermediate("Save to disk");
        sw.printTotal("Total");
        return 0;
    }
}

