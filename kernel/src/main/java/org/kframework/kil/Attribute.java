// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.kil;

import com.google.common.reflect.TypeToken;
import com.google.inject.name.Named;
import com.google.inject.name.Names;
import org.kframework.kil.loader.Constants;

import java.io.Serializable;
import java.lang.annotation.Annotation;

/**
 * Represents either an explicit attribute on a {@link Rule} or {@link Production},
 * or node metadata like location.
 * The inherited member attributes is used for location information
 * if this represents an explicitly written attribute.
 */
public class Attribute<T> extends ASTNode {

    public static final String BUILTIN_KEY = "builtin";
    public static final String FUNCTION_KEY = "function";
    public static final String ASSOCIATIVE_KEY = "assoc";
    public static final String COMMUTATIVE_KEY = "comm";
    public static final String IDEMPOTENT_KEY = "idem";
    public static final String UNIT_KEY = "unit";
    public static final String PREDICATE_KEY = "predicate";
    public static final String STREAM_KEY = "stream";
    public static final String ANYWHERE_KEY = Constants.ANYWHERE;
    public static final String PATTERN_KEY = "pattern";
    public static final String PATTERN_FOLDING_KEY = "pattern-folding";
    public static final String HOOK_KEY = "hook";
    public static final String MACRO_KEY = "macro";
    public static final String LEMMA_KEY = "lemma";
    public static final String TRUSTED_KEY = "trusted";
    public static final String SIMPLIFICATION_KEY = "simplification";

    public static final String FRESH_GENERATOR = "freshGenerator";
    public static final String BITWIDTH_KEY = "bitwidth";
    public static final String EXPONENT_KEY = "exponent";
    public static final String SIGNIFICAND_KEY = "significand";
    public static final String SMTLIB_KEY = "smtlib";
    public static final String SMT_LEMMA_KEY = "smt-lemma";
    public static final String SMT_SORT_FLATTEN = "smt-sort-flatten";
    // Used to direct configuration abstraction,
    // generated when translating configuration declaration to productions.
    public static final String CELL_KEY = "cell";
    public static final String CELL_FRAGMENT_KEY = "cellFragment";
    public static final String CELL_OPT_ABSENT_KEY = "cellOptAbsent";

    public static final String EQUALITY_KEY = "equality";
    public static final String ARITY_KEY = "arity";
    public static final String IMPURE_KEY = "impure";
    public static final String STRICT_KEY = "strict";
    public static final String SEQSTRICT_KEY = "seqstrict";
    public static final String CONCRETE_FUNCTION_KEY = "concrete";

    public static final Attribute<String> BRACKET = Attribute.of("bracket", "");
    public static final Attribute<String> FUNCTION = Attribute.of(FUNCTION_KEY, "");
    public static final Attribute<String> PREDICATE = Attribute.of(PREDICATE_KEY, "");
    public static final Attribute<String> PATTERN = Attribute.of(PATTERN_KEY, "");
    public static final Attribute<String> PATTERN_FOLDING = Attribute.of(PATTERN_FOLDING_KEY, "");
    public static final Attribute<String> TRUSTED = Attribute.of(TRUSTED_KEY, "");
    public static final Attribute<String> MACRO = Attribute.of(MACRO_KEY, "");
    public static final Attribute<String> ANYWHERE = Attribute.of("anywhere", "");
    public static final Attribute<String> TRANSITION = Attribute.of("transition", "");
    public static final Attribute<String> NOT_IN_RULES = Attribute.of("notInRules", "");
    public static final Attribute<String> VARIABLE = Attribute.of("variable", "");
    public static final Attribute<String> HYBRID = Attribute.of("hybrid", "");

    private Key<T> key;
    private T value;

    public static class Key<T> implements Serializable {
        private final TypeToken<T> typeToken;
        private final Annotation annotation;

        protected Key(TypeToken<T> typeToken, Annotation annotation) {
            this.typeToken = typeToken;
            this.annotation = annotation;
        }

        public TypeToken<T> getTypeToken() {
            return typeToken;
        }

        public Annotation getAnnotation() {
            return annotation;
        }

        public static <T> Key<T> get(Class<T> cls, Annotation annotation) {
            return new Key<T>(TypeToken.of(cls), annotation);
        }

        public static <T> Key<T> get(Class<T> cls) {
            return new Key<T>(TypeToken.of(cls), null);
        }

        public static <T> Key<T> get(TypeToken<T> type) {
            return new Key<T>(type, null);
        }

        public static <T> Key<T> get(TypeToken<T> type, Annotation annotation) {
            return new Key<T>(type, annotation);
        }

        @Override
        public String toString() {
            if (getTypeToken().equals(TypeToken.of(String.class))) {
                return toString(getAnnotation());
            }
            String annotation = toString(getAnnotation());
            if (annotation != null) {
                return "@" + getTypeToken().toString() + "." + annotation;
            } else {
                return "@" + getTypeToken().toString();
            }
        }

        public static String toString(Annotation annotation) {
            if (annotation == null) return null;
            if (annotation instanceof Named) {
                return ((Named)annotation).value();
            }
            return annotation.toString();
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result
                    + ((annotation == null) ? 0 : annotation.hashCode());
            result = prime * result
                    + ((typeToken == null) ? 0 : typeToken.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Key<?> other = (Key<?>) obj;
            if (annotation == null) {
                if (other.annotation != null)
                    return false;
            } else if (!annotation.equals(other.annotation))
                return false;
            if (typeToken == null) {
                if (other.typeToken != null)
                    return false;
            } else if (!typeToken.equals(other.typeToken))
                return false;
            return true;
        }
    }

    public static Attribute<String> of(String key, String value) {
        return new Attribute<String>(keyOf(key), value);
    }

    public static Key<String> keyOf(String key) {
        return Key.get(String.class, Names.named(key));
    }

    public Attribute(Key<T> key, T value) {
        super();
        this.key = key;
        this.value = value;
    }

    public Attribute(Attribute<T> attribute) {
        super(attribute);
        key = attribute.key;
        value = attribute.value;
    }

    @Override
    public String toString() {
        return " " + this.getKey() + "(" + this.getValue() + ")";
    }

    public void setValue(T value) {
        this.value = value;
    }

    public T getValue() {
        return value;
    }

    public Key<T> getKey() {
        return key;
    }

    public void setKey(Key<T> key) {
        this.key = key;
    }

    @Override
    public Attribute<T> shallowCopy() {
        return new Attribute<T>(this);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((key == null) ? 0 : key.hashCode());
        result = prime * result + ((value == null) ? 0 : value.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Attribute<?> other = (Attribute<?>) obj;
        if (key == null) {
            if (other.key != null)
                return false;
        } else if (!key.equals(other.key))
            return false;
        if (value == null) {
            if (other.value != null)
                return false;
        } else if (!value.equals(other.value))
            return false;
        return true;
    }
}
