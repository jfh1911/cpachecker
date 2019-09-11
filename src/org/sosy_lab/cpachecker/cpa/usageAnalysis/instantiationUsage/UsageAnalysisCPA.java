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

import com.google.common.collect.Lists;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpressionBuilder;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CArrayType;
import org.sosy_lab.cpachecker.core.defaults.AbstractCPA;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.defaults.DelegateAbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.CGenericInterval;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.CPropertySpec;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.FinalSegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.UnreachableSegmentation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.transfer.CSegmentationTransferRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.util.EnhancedCExpressionSimplificationVisitor;
import org.sosy_lab.cpachecker.exceptions.CPAException;

@Options(prefix = UsageAnalysisCPA.NAME_OF_ANALYSIS)
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


  @Option(
    name = "arrayName",
    toUppercase = false,
    description = "The array that needs to be analyzed")
  private String VARNAME_ARRAY = "";

  @Option(
    name = "arrayAccessVar",
    toUppercase = false,
    description = "The variables used to access array elements")
  private String arrayAccessVar = "";

  private List<String> ARRAY_ACCESS_VARS = Lists.newArrayList(arrayAccessVar);
  private final CFA cfa;
  public static final String NAME_OF_ANALYSIS = "cpa.usageCPA";
  private final LogManager logger;

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

    @Nullable
    CExpression sizeVar = null;
    List<CVariableDeclaration> arrayAccessVars = new ArrayList<>();
    CVariableDeclaration arrayVar = null;


    for (CFANode node : cfa.getAllNodes()) {
      if (!(node instanceof FunctionEntryNode)) {
        for (int i = 0; i < node.getNumLeavingEdges(); i++) {
          CFAEdge e = node.getLeavingEdge(i);
          if (e instanceof CDeclarationEdge) {
            if (((CDeclarationEdge) e).getDeclaration() instanceof CVariableDeclaration) {
              CVariableDeclaration decl =
                  (CVariableDeclaration) ((CDeclarationEdge) e).getDeclaration();
              // if (decl.getName().equalsIgnoreCase(this.VARMANE_FOR_ARRAY_LENGTH)) {
              // sizeVar = decl;
              // } else
              if (ARRAY_ACCESS_VARS.contains(decl.getName())) {
                arrayAccessVars.add(decl);
              } else if (decl.getName().equalsIgnoreCase(this.VARNAME_ARRAY)) {
                arrayVar = decl;
                if (decl.getType() instanceof CArrayType) {
                  CArrayType t = (CArrayType) decl.getType();
                  sizeVar = t.getLength();
                } else {
                  // TODO Log error
                }
              }
            }
            // else if (((CDeclarationEdge) e).getDeclaration()) {
            // }
          }
        }
      }
    }

    // Check if the sizeVar is a constant:


    if (arrayVar == null) {
      throw new InterruptedException(
          "The program cannot be analyed, since the array that needs to be ananlyzed in the main function named'"
              + this.VARNAME_ARRAY
              + "' is not defined!");
    }


    List<AExpression> pSBSecond = new ArrayList<>();
    // TODO: add handling for Java programs
    // Assume that the Size-var is defined in main method
    pSBSecond.add(sizeVar);
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
    Predicate<ArraySegmentationState<VariableUsageState>> predicate = null;
    EnhancedCExpressionSimplificationVisitor visitor =
        new EnhancedCExpressionSimplificationVisitor(
            cfa.getMachineModel(),
            new LogManagerWithoutDuplicates(logger));
    CBinaryExpressionBuilder builder = new CBinaryExpressionBuilder(cfa.getMachineModel(), logger);

    predicate = new Predicate<ArraySegmentationState<VariableUsageState>>() {
      @Override
      public boolean test(ArraySegmentationState<VariableUsageState> pT) {
        if (pT instanceof UnreachableSegmentation) {
          return false;
        }

        CPropertySpec<VariableUsageState> properties = null;
        try {
          properties =
              pT.getSegmentsForProperty(
                  new VariableUsageState(VariableUsageType.USED),
                  visitor,
                  builder);
        } catch (CPAException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        }
        List<CGenericInterval> overApproxP = properties.getOverApproxIntervals();
        boolean isCorrect =
            pT.isEmptyArray()
                || (overApproxP.size() == 1
            && overApproxP.get(0).getLow().equals(CIntegerLiteralExpression.ZERO)
                    && overApproxP.get(0).getHigh().equals(pT.getSizeVar()));
        return !isCorrect;
      }
    };

    return new ArraySegmentationState<>(
        segments,
        VariableUsageState.getEmptyElement(),
        listOfIDElements,
        new CIdExpression(arrayVar.getFileLocation(), arrayVar),
        sizeVar,
        cfa.getLanguage(),
        false,
        "UsageAnalysisCPA",
        predicate,
        logger);

  }
}
