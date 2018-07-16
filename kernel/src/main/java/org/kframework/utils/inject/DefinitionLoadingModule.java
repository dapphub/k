// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.google.inject.AbstractModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.DefinitionDir;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.file.WorkingDir;
import org.kframework.utils.options.DefinitionLoadingOptions;

import java.io.File;
import java.io.FilenameFilter;
import java.util.Map;

public class DefinitionLoadingModule extends AbstractModule {

    @Override
    protected void configure() {
    }

    @Provides @DefinitionScoped
    CompiledDefinition koreDefinition(BinaryLoader loader, FileUtil files) {
        return loader.loadOrDie(CompiledDefinition.class, files.resolveKompiled("compiled.bin"));
    }


    @Provides
    KompileOptions kompileOptions(Provider<CompiledDefinition> compiledDef) {
        // a hack, but it's good enough for what we need from it, which is a temporary solution
        KompileOptions res = compiledDef.get().kompileOptions;
        return res;
    }

    @Provides @KompiledDir
    File definition(@DefinitionDir File defDir, KExceptionManager kem) {
        File directory = null;
        File[] dirs = defDir.listFiles(new FilenameFilter() {
            @Override
            public boolean accept(File current, String name) {
                return new File(current, name).isDirectory();
            }
        });

        for (int i = 0; i < dirs.length; i++) {
            if (dirs[i].getAbsolutePath().endsWith("-kompiled")) {
                if (directory != null) {
                    throw KEMException.criticalError("Multiple compiled definitions found in the "
                            + "current working directory: " + directory.getAbsolutePath() + " and " +
                            dirs[i].getAbsolutePath());
                } else {
                    directory = dirs[i];
                }
            }
        }

        if (directory == null) {
            throw KEMException.criticalError("Could not find a compiled definition. " +
                    "Use --directory to specify one.");
        }
        if (!directory.isDirectory()) {
            throw KEMException.criticalError("Does not exist or not a directory: " + directory.getAbsolutePath());
        }
        return directory;
    }

    @Provides @DefinitionDir
    File directory(DefinitionLoadingOptions options, @WorkingDir File workingDir, KExceptionManager kem, @Environment Map<String, String> env) {
        File directory;
        if (options.directory == null) {
            if (env.get("KRUN_COMPILED_DEF") != null) {
                File f = new File(env.get("KRUN_COMPILED_DEF"));
                if (f.isAbsolute()) {
                    directory = f;
                } else {
                    directory = new File(workingDir, env.get("KRUN_COMPILED_DEF"));
                }
            } else {
                directory = workingDir;
            }
        } else {
            File f = new File(options.directory);
            if (f.isAbsolute()) {
                directory = f;
            } else {
                directory = new File(workingDir, options.directory);
            }
        }
        if (!directory.isDirectory()) {
            throw KEMException.criticalError("Does not exist or not a directory: " + directory.getAbsolutePath());
        }
        return directory;
    }
}
