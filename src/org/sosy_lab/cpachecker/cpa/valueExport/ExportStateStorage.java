// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.valueExport;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Multimap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.sosy_lab.cpachecker.cfa.types.Type;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisInformation;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState.ValueAndType;
import org.sosy_lab.cpachecker.cpa.value.type.NumericValue;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;
/** A data container to store all states collected during value analysis */
public class ExportStateStorage {

  public static final String CPACHECKER_TEMP = "__CPAchecker_TMP";

  private static final String ID_HEADER = "ID";

  String methodName;
  Set<Pair<MemoryLocation, Type>> locationsUsedInMethod;
  Multimap<Integer, Map<MemoryLocation, Number>> lineNumberToState;
  List<Pair<MemoryLocation, Type>> locationsUsedInMethodOrdered;

  private String default_for_unknown;

  private boolean handleUndefiendVars;

  public ExportStateStorage(
      String pMethodName, String default_for_unknown, boolean handleUndefiendVars) {
    this.methodName = pMethodName;
    this.lineNumberToState = ArrayListMultimap.create();
    this.locationsUsedInMethod = new HashSet<>();
    this.locationsUsedInMethodOrdered = new ArrayList<>();
    this.default_for_unknown = default_for_unknown;
    this.handleUndefiendVars = handleUndefiendVars;
  }

  public boolean isEmpty() {
    return this.lineNumberToState.isEmpty() && this.locationsUsedInMethodOrdered.isEmpty();
  }

  public void addNewState(ValueAnalysisInformation pInfo, int pLineNumber) {
    Map<MemoryLocation, Number> state = new HashMap<>();
    for (Entry<MemoryLocation, ValueAndType> ass : pInfo.getAssignments().entrySet()) {
      MemoryLocation memLoc = ass.getKey();
      //      boolean isNotArrayVar = true;
      boolean varIsVisible = true;
      try {
        String functionName = memLoc.getFunctionName();
        if (functionName != null && !functionName.equals(this.methodName)) {
          varIsVisible = false;
        }
      } catch (NullPointerException e) {
        // as the getFunctionName may throw a Nullpointert ( implying to set isNotArrayVar
        //       =false)
        //              isNotArrayVar = false;
      }

      if (ass.getValue() != null
          && ass.getValue().getValue() != null
          && !memLoc.getIdentifier().startsWith(CPACHECKER_TEMP)
          // && isNotArrayVar
          // TODO: We just remove this line, as it causes many problems and prefer to remove array
          // programs for the dataset
          && varIsVisible
      //          && !memLoc.getIdentifier().equals(memLoc.getAsSimpleString())
      ) {

        if (ass.getValue().getValue() instanceof NumericValue) {
          Number num = ((NumericValue) ass.getValue().getValue()).getNumber();
          state.put(memLoc, num);
          Pair<MemoryLocation, Type> pair = Pair.of(memLoc, ass.getValue().getType());
          if (this.locationsUsedInMethod.add(pair)) {
            // To maintain a consistent variable ordering, add them to a list
            this.locationsUsedInMethodOrdered.add(pair);
          }
        } else if (handleUndefiendVars) {
          state.put(memLoc, null);
          Pair<MemoryLocation, Type> pair = Pair.of(memLoc, ass.getValue().getType());
          if (this.locationsUsedInMethod.add(pair)) {
            // To maintain a consistent variable ordering, add them to a list
            this.locationsUsedInMethodOrdered.add(pair);
        }
      }
      }
    }
    this.lineNumberToState.put(pLineNumber, state);
  }

  public String printFirst() {
    StringBuilder builder;
    builder = new StringBuilder();

    builder = builder.append("##");
    builder = builder.append(ID_HEADER + ",");

    for (Pair<MemoryLocation, Type> var : this.locationsUsedInMethodOrdered) {

      builder = builder.append("|" + var.getFirst().getAsSimpleString() + "|").append(",");
    }
    // Remove last ","
    if (builder.lastIndexOf(",") > 0) {
      builder = builder.deleteCharAt(builder.length() - 1);
    }
    return builder.toString();
  }

  public List<String> printAllStates(
      AtomicInteger id_counter, Map<Integer, Set<String>> pVarsAssignedInLoop) {
    List<String> states = new ArrayList<>();

    for (Entry<Integer, Map<MemoryLocation, Number>> state : this.lineNumberToState.entries()) {
      List<String> varsPrinted = new ArrayList<>();
      StringBuilder builder = new StringBuilder();
      builder = builder.append(state.getKey() + "-" + id_counter.getAndIncrement() + ",");

      for (Pair<MemoryLocation, Type> loc : this.locationsUsedInMethodOrdered) {
        Number value = state.getValue().get(loc.getFirst());
        if (value != null) {
          builder = builder.append(value.intValue()).append(",");
        } else {
          builder = builder.append(this.default_for_unknown).append(",");
        }
        varsPrinted.add(loc.getFirst().getAsSimpleString());
      }
      if (builder.lastIndexOf(",") > 0) {
        // Now, print the encoding, which variables are modified within the loop
        if (pVarsAssignedInLoop.containsKey(state.getKey())) {
          Set<String> modified = pVarsAssignedInLoop.get(state.getKey());
          builder = builder.append("[");
          for (String var : varsPrinted) {
            builder = builder.append(modified.contains(var) ? "1" : "0").append(";");
          }
          if (builder.lastIndexOf(";") > 0) {
            builder = builder.deleteCharAt(builder.length() - 1);
          }
          builder = builder.append("]");
        } else {
          builder = builder.deleteCharAt(builder.length() - 1);
        }
      }

      states.add(builder.toString());
    }

    return states;
  }

  public List<String> printBody(
      AtomicInteger id_counter, Map<Integer, Set<String>> pVarsAssignedInLoop) {
    List<String> body = new ArrayList<>();

    body.add(printFirst());
    body.addAll(printAllStates(id_counter, pVarsAssignedInLoop));
    return body;
  }

  public String getMethodName() {
    return methodName;
  }

  public List<Pair<MemoryLocation, Type>> getLocationsUsedInMethod() {
    return locationsUsedInMethodOrdered;
  }

  public Multimap<Integer, Map<MemoryLocation, Number>> getLineNumberToState() {
    return lineNumberToState;
  }
}
