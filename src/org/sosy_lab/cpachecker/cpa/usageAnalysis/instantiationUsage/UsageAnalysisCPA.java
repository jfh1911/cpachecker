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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.core.defaults.AbstractCPA;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.defaults.DelegateAbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.FinalSegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.araySegmentationDomain.transfer.CSegmentationTransferRelation;

@Options(prefix = "cpa.usageCPA")
public class UsageAnalysisCPA extends AbstractCPA {

  @Option(
    secure = true,
    name = "merge",
    toUppercase = true,
    values = {"SEP", "JOIN"},
    description = "which merge operator to use for UsageOfArrayElemensCPA")
  private String mergeType = "JOIN";

  @Option(
    secure = true,
    name = "stop",
    toUppercase = true,
    values = {"SEP", "JOIN"},
    description = "which stop operator to use for UsageOfArrayElemensCPA")
  private String stopType = "SEP";

  private final LogManager logger;
  public static final String VARMANE_FOR_ARRAY_LENGTH = "SIZE";
  private static final String VARNAME_ARRAY = "a";
  private static final String[] temp = {"i"};
  private static final List<String> ARRAY_ACCESS_VARS = Arrays.asList(temp);
  private final CFA cfa;

  /**
   * This method acts as the constructor of the interval analysis CPA.
   *
   * @param config the configuration of the CPAinterval analysis CPA.
   */
  public UsageAnalysisCPA(Configuration config, LogManager pLogger, CFA cfa)
      throws InvalidConfigurationException {
    super(
        "join",
        "sep",
        DelegateAbstractDomain.<ArraySegmentationState<VariableUsageState>>getInstance(),
        null);
    config.inject(this, UsageAnalysisCPA.class);
    this.logger = pLogger;
    this.cfa = cfa;
  }

  @Override
  public MergeOperator getMergeOperator() {
    return buildMergeOperator(mergeType);
  }

  @Override
  public StopOperator getStopOperator() {
    return buildStopOperator(stopType);
  }

  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(UsageAnalysisCPA.class);
  }

  @Override
  public TransferRelation getTransferRelation() {
    return new CSegmentationTransferRelation<VariableUsageState>(
        new UsageAnalysisTransferRelation(
            new LogManagerWithoutDuplicates(logger),
            this.cfa.getMachineModel()),
        new LogManagerWithoutDuplicates(logger),
        cfa.getMachineModel(),
        "SimpleUsage");
  }

  @Override
  public ArraySegmentationState<VariableUsageState>
      getInitialState(CFANode pNode, StateSpacePartition pPartition) throws InterruptedException {

    // The initial state consists of two segments: {0} N? {SIZE}, where SIZE is a variable used to
    // denote the length of the array used in the program

    // Iterate through the cfa to get the assignments of the variable that are predefined (SIZE; the
    // array, the variables used to access the array)

    CVariableDeclaration sizeVar = null;
    List<CVariableDeclaration> arrayAccessVars = new ArrayList<>();
    CVariableDeclaration arrayVar = null;

    for (CFANode node : cfa.getAllNodes()) {
      if (!(node instanceof FunctionEntryNode)) {
        for (int i = 0; i < node.getNumLeavingEdges(); i++) {
          CFAEdge e = node.getLeavingEdge(i);
          if (e instanceof CDeclarationEdge
              && ((CDeclarationEdge) e).getDeclaration() instanceof CVariableDeclaration) {
            CVariableDeclaration decl =
                (CVariableDeclaration) ((CDeclarationEdge) e).getDeclaration();
            if (decl.getName().equalsIgnoreCase(UsageAnalysisCPA.VARMANE_FOR_ARRAY_LENGTH)) {
              sizeVar = decl;
            } else if (ARRAY_ACCESS_VARS.contains(decl.getName())) {
              arrayAccessVars.add(decl);
            } else if (decl.getName().equalsIgnoreCase(UsageAnalysisCPA.VARNAME_ARRAY)) {
              arrayVar = decl;
            }
          }
        }
      }
    }

    if (sizeVar == null) {
      throw new InterruptedException(
          "The program cannot be analyed, since the assumption, that the main function defines a variable named '"
              + UsageAnalysisCPA.VARMANE_FOR_ARRAY_LENGTH
              + "' is not met!");
    }
    if (arrayVar == null) {
      throw new InterruptedException(
          "The program cannot be analyed, since the array that needs to be ananlyzed in the main function named'"
              + UsageAnalysisCPA.VARMANE_FOR_ARRAY_LENGTH
              + "' is not defined!");
    }

    List<AExpression> pSBSecond = new ArrayList<>();
    // TODO: add handling for Java programs
    // Assume that the Size-var is defined in main method
    pSBSecond.add(new CIdExpression(sizeVar.getFileLocation(), sizeVar));
    List<AExpression> pSBFirst = new ArrayList<>();
    pSBFirst.add(CIntegerLiteralExpression.ZERO);

    ArraySegment<VariableUsageState> second =
        new ArraySegment<>(
            pSBSecond,
            new EmptyVariableUsageElement(),
            false,
            new FinalSegment<>(VariableUsageState.getEmptyElement()),
            cfa.getLanguage());

    ArraySegment<VariableUsageState> first =
        new ArraySegment<>(
            pSBFirst,
            new VariableUsageState(VariableUsageType.NOT_USED),
            true,
            second,
            cfa.getLanguage());

    List<ArraySegment<VariableUsageState>> segments = new ArrayList<>();
    segments.add(first);
    segments.add(second);

    ArrayList<AIdExpression> listOfIDElements = new ArrayList<>();
    arrayAccessVars.parallelStream()
        .forEach(v -> listOfIDElements.add(new CIdExpression(v.getFileLocation(), v)));
    return new ArraySegmentationState<VariableUsageState>(
        segments,
        VariableUsageState.getEmptyElement(),
        listOfIDElements,
        new CIdExpression(arrayVar.getFileLocation(), arrayVar),
        new CIdExpression(sizeVar.getFileLocation(), sizeVar),
        cfa.getLanguage(),
        false,
        logger);
  }
}
