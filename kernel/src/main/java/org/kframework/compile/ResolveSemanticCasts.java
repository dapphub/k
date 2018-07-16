// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.parser.outer.Outer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 4/17/15.
 */
public class ResolveSemanticCasts {

    private final boolean skipSortPredicates;
    private Set<KApply> casts = new HashSet<>();
    private Map<KVariable, KVariable> varToTypedVar = new HashMap<>();

    public ResolveSemanticCasts(boolean skipSortPredicates) {

        this.skipSortPredicates = skipSortPredicates;
    }

    void resetCasts() {
        casts.clear();
        varToTypedVar.clear();
    }

    public K resolve(K k) {
        resetCasts();
        gatherCasts(k);
        return transform(k);
    }

    private Rule resolve(Rule rule) {
        resetCasts();
        gatherCasts(rule.body());
        gatherCasts(rule.requires());
        gatherCasts(rule.ensures());
        return new Rule(
                transform(rule.body()),
                addSideCondition(transform(rule.requires()), rule.att().contains("macro")),
                transform(rule.ensures()),
                rule.att());
    }

    private Context resolve(Context context) {
        resetCasts();
        gatherCasts(context.body());
        gatherCasts(context.requires());
        return new Context(
                transform(context.body()),
                addSideCondition(transform(context.requires()), false),
                context.att());
    }

    K addSideCondition(K requires, boolean macro) {
        if (skipSortPredicates || macro)
            return requires;
        else {
            Optional<KApply> sideCondition = casts.stream().map(k -> {
                return new TransformK() {
                    @Override
                    public K apply(KVariable k) {
                        if (varToTypedVar.containsKey(k)) {
                            return varToTypedVar.get(k);
                        }
                        return k;
                    }
                }.apply(k);
            }).map(k -> KApply(KLabel("is" + getSortNameOfCast((KApply) k)), transform(k))).reduce(BooleanUtils::and);
            if (!sideCondition.isPresent()) {
                return requires;
            } else if (requires.equals(BooleanUtils.TRUE) && sideCondition.isPresent()) {
                return sideCondition.get();
            } else {
                return BooleanUtils.and(sideCondition.get(), requires);
            }
        }
    }

    public static String getSortNameOfCast(KApply kapp) {
        return kapp.klabel().name().substring("#SemanticCastTo".length());
    }

    void gatherCasts(K term) {
        new VisitK() {
            @Override
            public void apply(KApply v) {
                if (v.klabel().name().startsWith("#SemanticCastTo")) {
                    casts.add(v);
                    K child = v.klist().items().get(0);
                    if (child instanceof KVariable) {
                        KVariable var = (KVariable) child;
                        varToTypedVar.put(var, KVariable(var.name(), var.att().contains(Sort.class) ? var.att() : var.att().add(Sort.class, Outer.parseSort(getSortNameOfCast(v)))));
                    }
                }
                super.apply(v);
            }
        }.apply(term);
    }

    K transform(K term) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                if (casts.contains(k)) {
                    return super.apply(k.klist().items().get(0));
                }
                return super.apply(k);
            }

            @Override
            public K apply(KVariable k) {
                if (varToTypedVar.containsKey(k)) {
                    return varToTypedVar.get(k);
                }
                return super.apply(k);
            }
        }.apply(term);
    }


    public synchronized Sentence resolve(Sentence s) {
        if (s instanceof Rule) {
            return resolve((Rule) s);
        } else if (s instanceof Context) {
            return resolve((Context) s);
        } else {
            return s;
        }
    }
}
