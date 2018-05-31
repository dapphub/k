// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.kil;

import com.google.inject.name.Names;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.Attribute.Key;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * class for AST Attributes.
 * This is used to represent a collection of attributes on a node,
 * which may contain both attributes in the K source
 * written by a user, and metadata like location added by kompile.
 * Only {@link Rule} and {@link Production} may have user-written
 * attributes.
 *
 * @see ASTNode
 */
public class Attributes extends ASTNode implements Map<Key<?>, Attribute<?>> {

    protected transient LinkedHashMap<Key<?>, Attribute<?>> contents;

    public Attributes(Attributes c) {
        super(c);
        this.contents = c.contents;
    }

    public Attributes(Location location, Source source) {
        super(location, source);
        contents = new LinkedHashMap<>();
    }

    public Attributes() {
        contents = new LinkedHashMap<>();
    }

    @Override
    public String toString() {
        if (isEmpty())
            return "";
        String content = "[";
        for (Attribute<?> t : contents.values())
            content += t + ", ";
        return content.substring(0, content.length() - 2) + "]";
    }

    @Override
    public Attributes shallowCopy() {
        Attributes result = new Attributes();
        result.contents.putAll(contents);
        return result;
    }


    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((contents == null) ? 0 : contents.hashCode());
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
        Attributes other = (Attributes) obj;
        if (contents == null) {
            if (other.contents != null)
                return false;
        } else if (!contents.equals(other.contents))
            return false;
        return true;
    }

    public void add(Attribute<?> e) {
        contents.put(e.getKey(), e);
    }

    public <T> void add(Class<T> cls, T value) {
        add(new Attribute<T>(Key.get(cls), value));
    }

    public <T> void add(Class<T> cls, String string, T value) {
        add(new Attribute<T>(Key.get(cls, Names.named(string)), value));
    }

    public <T> T typeSafeGet(Key<T> key) {
        Attribute<?> attr = get(key);
        if (attr == null) return null;
        return (T) attr.getValue();
    }

    public <T> T typeSafeGet(Class<T> cls) {
        return typeSafeGet(Key.get(cls));
    }

    public <T> T typeSafeGet(Class<T> cls, String string) {
        return typeSafeGet(Key.get(cls, Names.named(string)));
    }

    /**
     * Retrieves the attribute by key from the list of attributes
     */
    public <T> T getAttr(Key<T> key) {
        final Attribute<T> value = (Attribute<T>) get(key);
        if (value == null)
            return null;
        return value.getValue();
    }

    public String getAttr(String key) {
        return getAttr(Attribute.keyOf(key));
    }

    @Override
    public void clear() {
        contents.clear();
    }

    @Override
    public boolean containsKey(Object key) {
        return contents.containsKey(key);
    }

    @Override
    public boolean containsValue(Object value) {
        return contents.containsValue(value);
    }

    @Override
    public Set<java.util.Map.Entry<Key<?>, Attribute<?>>> entrySet() {
        return contents.entrySet();
    }

    @Override
    public Attribute<?> get(Object key) {
        return contents.get(key);
    }

    @Override
    public boolean isEmpty() {
        return contents.isEmpty();
    }

    @Override
    public Set<Key<?>> keySet() {
        return contents.keySet();
    }

    @Override
    public Attribute<?> put(Key<?> key, Attribute<?> value) {
        return contents.put(key, value);
    }

    @Override
    public void putAll(Map<? extends Key<?>, ? extends Attribute<?>> m) {
        contents.putAll(m);
    }

    @Override
    public Attribute<?> remove(Object key) {
        return contents.remove(key);
    }

    @Override
    public int size() {
        return contents.size();
    }

    @Override
    public Collection<Attribute<?>> values() {
        return contents.values();
    }

    private void writeObject(ObjectOutputStream stream) throws IOException {
        stream.defaultWriteObject();
        Set<Attribute<?>> attributes = new HashSet<>(contents.values());
        stream.writeObject(attributes);
    }

    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        contents = new LinkedHashMap<>();
        Set<Attribute<?>> attributes = (Set<Attribute<?>>) stream.readObject();
        for (Attribute<?> attr : attributes) {
            contents.put(attr.getKey(), attr);
        }
    }
}
