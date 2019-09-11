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
import java.util.Collection;
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
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpressionBuilder;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
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
    List<AExpression> arrayAccessVars = new ArrayList<>();
    CVariableDeclaration arrayVar = null;

    for (CFANode node : cfa.getAllNodes()) {
      if (!(node instanceof FunctionEntryNode)) {
        for (int i = 0; i < node.getNumLeavingEdges(); i++) {
          CFAEdge e = node.getLeavingEdge(i);
          if (e instanceof CDeclarationEdge) {
            if (((CDeclarationEdge) e).getDeclaration() instanceof CVariableDeclaration) {
              CVariableDeclaration decl =
                  (CVariableDeclaration) ((CDeclarationEdge) e).getDeclaration();
              if (decl.getName().equalsIgnoreCase(this.VARNAME_ARRAY)) {
                arrayVar = decl;
                if (decl.getType() instanceof CArrayType) {
                  CArrayType t = (CArrayType) decl.getType();
                  sizeVar = t.getLength();
                } else {
                  throw new InterruptedException(
                      "The program cannot be analyed, since the array that needs to be ananlyzed in the main function named'"
                          + this.VARNAME_ARRAY
                          + "' is not definedas a array variable!");
                }
              }
            }

          }
          // Next, determine the variables / expressions used to access any array
          else if (e instanceof CStatementEdge) {
            CStatementEdge s = (CStatementEdge) e;
            if (s.getStatement() instanceof CAssignment) {
              // Only consider the RHS, since LHS is not an usage (only an assignment)
              arrayAccessVars
                  .addAll(computeVars(((CAssignment) s.getStatement()).getRightHandSide()));
            } else if (s.getStatement() instanceof CFunctionCall) {
              arrayAccessVars.addAll(
                  computeVars(((CFunctionCall) s.getStatement()).getFunctionCallExpression()));
            }
          } else if (e instanceof CFunctionCallEdge) {
            ((CFunctionCallEdge) e).getArguments()
                .forEach(a -> arrayAccessVars.addAll(computeVars(a)));
          } else if (e instanceof CAssumeEdge) {
            arrayAccessVars.addAll(computeVars(((CAssumeEdge) e).getExpression()));
          } else if (e instanceof CFunctionReturnEdge) {
            // TODO: Considere this
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
        arrayAccessVars,
        new CIdExpression(arrayVar.getFileLocation(), arrayVar),
        sizeVar,
        cfa.getLanguage(),
        false,
        "UsageAnalysisCPA",
        predicate,
        logger);

  }

  private Collection<CExpression> computeVars(CRightHandSide pExpr) {
    List<CExpression> res = new ArrayList<CExpression>();

    if (pExpr instanceof CFunctionCallExpression) {
      ((CFunctionCallExpression) pExpr).getParameterExpressions()
          .forEach(e -> res.addAll(computeVars(e)));
    } else if (pExpr instanceof CBinaryExpression) {
      CBinaryExpression bin = (CBinaryExpression) pExpr;
      res.addAll(computeVars(bin.getOperand1()));
      res.addAll(computeVars(bin.getOperand2()));
    } else if (pExpr instanceof CUnaryExpression) {
      res.addAll(computeVars(((CUnaryExpression) pExpr).getOperand()));
    } else if (pExpr instanceof CArraySubscriptExpression) {
      res.add(((CArraySubscriptExpression) pExpr).getSubscriptExpression());
    }

    return res;
  }
}
