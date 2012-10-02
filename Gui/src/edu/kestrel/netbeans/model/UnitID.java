package edu.kestrel.netbeans.model;

import java.util.Map;
import java.util.HashMap;

public final class UnitID {

    private static Map nameMap = new HashMap();
    
    private String name;

    public UnitID(String name) {
	this.name = name;
    }

    public static void addInstance(String name) {
	UnitID instance = new UnitID(name);
	nameMap.put(name, instance);
    }

    public static UnitID get(String name) {
	return (UnitID) nameMap.get(name);
    }

    public static Object[] getInstances() {
	return nameMap.values().toArray();
    }

    public String toString() {
	return name;
    }

}
