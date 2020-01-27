/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.collect.PathCopyingPersistentTreeMap;
import org.sosy_lab.common.collect.PersistentSortedMap;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.AnalysisDirection;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.alwaystop.AlwaysTopCPA;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManagerImpl;
import org.sosy_lab.cpachecker.util.predicates.regions.SymbolicRegionManager;
import org.sosy_lab.cpachecker.util.predicates.smt.BooleanFormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;

public class CFA2ReachedSetTransformer {

  public List<Pair<AbstractState, Precision>> transformCFAToReachedSet(
      CFA pCfa,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      Configuration pConfig,
      int offset)
      throws InvalidConfigurationException {
    ConfigurationBuilder builder = Configuration.builder();

    builder.setOption("reachedSet", "NORMAL");
    List<Pair<AbstractState, Precision>> returnSet = new ArrayList<>();

    @SuppressWarnings("resource")
    Solver solver = Solver.create(pConfig, pLogger, pShutdownNotifier);
    FormulaManagerView view = solver.getFormulaManager();

    PathFormulaManager pathFormulaManager =
        new PathFormulaManagerImpl(
            view,
            pConfig,
            pLogger,
            pShutdownNotifier,
            pCfa,
            AnalysisDirection.FORWARD);
    BooleanFormulaManagerView bfmgr = view.getBooleanFormulaManager();

    SymbolicRegionManager regionmngr = new SymbolicRegionManager(solver);
    Set<Integer> noAbstractionReuse = new HashSet<>();
    PredicateAbstractState initale =
        PredicateAbstractState.mkAbstractionState(
            pathFormulaManager.makeEmptyPathFormula(),
            new AbstractionFormula(
                view,
                regionmngr.makeTrue(),
                bfmgr.makeTrue(),
                bfmgr.makeTrue(),
                pathFormulaManager.makeEmptyPathFormula(),
                noAbstractionReuse),
            PathCopyingPersistentTreeMap.of());

    // Since there is no public constructor for the AlwaysTopPrecision, use this ugly workaround
    Precision precision = AlwaysTopCPA.INSTANCE.getInitialPrecision(null, null);
    returnSet.add(Pair.of(initale, precision));

    // Firstly, read the file and parse it, such that we have a map of the form: location ->
    // invarinat
    Map<Pair<Integer, String>, String> invariants = parseInvFile();
    Map<String, String> nodeToInv = new HashMap<>();

    // Now, iterate over the cfa nodes and check for each leaving edge, if the assosiated source
    // code is present in the invariant file.
    // If yes, the invarinat is associated with the node!
    Pair<Integer, String> posInvLoc;
    for (CFANode node : pCfa.getAllNodes()) {
      boolean invFound = false;

      for (int i = 0; i < node.getNumLeavingEdges(); i++) {
        CFAEdge edge = node.getLeavingEdge(i);
        if (node.getNodeNumber() == 15) {
          System.out.println(
              edge.getLineNumber() + "  " + edge.getCode() + "(in node " + node.getNodeNumber());
        }
        System.out.println(
            edge.getLineNumber() + "  " + edge.getCode() + "(in node " + node.getNodeNumber());
        posInvLoc = Pair.of(edge.getLineNumber() + offset, "");

        if (invariants.containsKey(posInvLoc)) {

          returnSet.add(
              Pair.of(
                  getAbstrStateForInv(node, view, pathFormulaManager, regionmngr, bfmgr),
                  precision));
          nodeToInv.put("N" + node.getNodeNumber(), invariants.get(posInvLoc));
          break;

        }
        if (!invFound) {
          // No invariant is found, hence the node is added with true;
          returnSet.add(
              Pair.of(
                  getAbstrStateForInv(node, view, pathFormulaManager, regionmngr, bfmgr),
                  precision));
        }

      }
    }

    pLogger.log(Level.FINER, nodeToInv.toString());
    solver.close();
    return returnSet;
  }

  private AbstractState getAbstrStateForInv(
      CFANode pNode,
      FormulaManagerView view,
      PathFormulaManager pathFormulaManager,
      SymbolicRegionManager pRegionmngr,
      BooleanFormulaManagerView pBfmgr) {
    AbstractState state;

    HashMap<CFANode, Integer> tempMap = new HashMap<>();
    tempMap.put(pNode, 0);
    PersistentSortedMap<CFANode, Integer> mapOfNode = PathCopyingPersistentTreeMap.copyOf(tempMap);

    AbstractionFormula pA =
        new AbstractionFormula(
            view,
            pRegionmngr.makeTrue(),
            pBfmgr.makeTrue(),
            pBfmgr.makeTrue(),
            pathFormulaManager.makeEmptyPathFormula(),
            new HashSet<>());
    state =
        PredicateAbstractState
            .mkAbstractionState(pathFormulaManager.makeEmptyPathFormula(), pA, mapOfNode);
    // mkNonAbstractionStateWithNewPathFormula(
    // pathFormulaManager.makeEmptyPathFormula(),
    // pInitale);

    assert AbstractStates.extractLocation(state) != null;
    return state;

  }

  @SuppressWarnings("resource")
  private Map<Pair<Integer, String>, String> parseInvFile() {
    BufferedReader reader = null;
    Map<Pair<Integer, String>, String> invs = new HashMap<>();
    try {
      reader =
          Files.newBufferedReader(
              Paths.get("/home/cppp/Documents/seahorn/invars_in_c.txt"),
              Charset.defaultCharset());
      String line = reader.readLine();
      // Skip the first line

      while ((line = reader.readLine()) != null) {
        if (line.indexOf(",") == -1) {
          throw new IllegalArgumentException(
              "The ile was not parsed as expected, the line "
                  + line
                  + "does nto have the format 'Linenumber , sourcecode");
        }
        int lineNumber = Integer.parseInt(line.substring(0, line.indexOf(",")));
        // +1 to ignore the ','
        String code = line.substring(line.indexOf(",") + 1);
        String inv = reader.readLine();
        invs.put(Pair.of(lineNumber, code), inv);
      }
      reader.close();
    } catch (IOException e) {
      // TODO: Enhance logging
      throw new IllegalArgumentException(e);
    }

    return invs;
  }

}
