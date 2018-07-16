// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.kast;

import org.kframework.kil.loader.Context;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.options.DefinitionLoadingOptions;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;

public class KastModule extends AbstractModule {

    @Override
    public void configure() {
        bind(FrontEnd.class).to(KastFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KAST);

        install(new DefinitionLoadingModule());

        bind(Context.class).annotatedWith(Main.class).to(Context.class);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KastOptions.class);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(KastOptions.Experimental.class);
    }

    @Provides
    GlobalOptions globalOptions(KastOptions options) {
        return options.global;
    }

    @Provides
    DefinitionLoadingOptions defLoadingOptions(KastOptions options) {
        return options.definitionLoading;
    }
}
