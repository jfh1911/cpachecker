// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.hardloopbound;

import com.google.common.base.Optional;
import com.google.common.collect.Lists;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.ADeclaration;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.AParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.AStatement;
import org.sosy_lab.cpachecker.cfa.model.ADeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.AReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.AStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.AssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.defaults.SingletonPrecision;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.AbstractStates;

public class HardLoopboundTransferFunction
    extends ForwardingTransferRelation<
        HardLoopbonudState, HardLoopbonudState, SingletonPrecision> {



  private final LogManagerWithoutDuplicates logger;

  private int maxLoopIterations;

  private Map<CFANode, Integer> numberVisits;

  public HardLoopboundTransferFunction(LogManager pLogger, int pMaxLoopIteration) {

    logger = new LogManagerWithoutDuplicates(pLogger);


    this.maxLoopIterations = pMaxLoopIteration;
    this.numberVisits = new HashMap<>();
  }



  @Override
  protected HardLoopbonudState handleFunctionCallEdge(
      FunctionCallEdge callEdge,
      List<? extends AExpression> arguments,
      List<? extends AParameterDeclaration> parameters,
      String calledFunctionName)
      throws UnrecognizedCodeException {
    return state;
  }

  @Override
  protected HardLoopbonudState handleBlankEdge(BlankEdge cfaEdge) {
    return state;
  }

  @Override
  protected HardLoopbonudState handleReturnStatementEdge(AReturnStatementEdge returnEdge)
      throws UnrecognizedCodeException {

    return state;
  }

  /**
   * Handles return from one function to another function.
   *
   * @param functionReturnEdge return edge from a function to its call site
   * @return new abstract state
   */
  @Override
  protected HardLoopbonudState handleFunctionReturnEdge(
      FunctionReturnEdge functionReturnEdge,
      FunctionSummaryEdge summaryEdge,
      AFunctionCall exprOnSummary,
      String callerFunctionName)
      throws UnrecognizedCodeException {

    return state;
  }

  @Override
  protected HardLoopbonudState handleFunctionSummaryEdge(CFunctionSummaryEdge cfaEdge)
      throws CPATransferException {
    return state;
  }

  @Override
  protected HardLoopbonudState handleAssumption(
      AssumeEdge cfaEdge, AExpression expression, boolean truthValue)
      throws UnrecognizedCodeException {
    return state;
  }

  @Override
  protected HardLoopbonudState handleDeclarationEdge(
      ADeclarationEdge declarationEdge, ADeclaration declaration) throws UnrecognizedCodeException {

    return state;
  }

  @Override
  protected HardLoopbonudState handleStatementEdge(
      AStatementEdge cfaEdge, AStatement expression) throws UnrecognizedCodeException {

    return state;
  }

  @Override
  public Collection<? extends AbstractState> strengthen(
      AbstractState pElement,
      Iterable<AbstractState> pElements,
      CFAEdge pCfaEdge,
      Precision pPrecision)
      throws CPATransferException {
    assert pElement instanceof HardLoopbonudState;

    // Do post processing
    final Collection<AbstractState> postProcessedResult = new ArrayList<>(1);
    postProcessedResult.add(pElement);

    @Nullable Optional<CFANode> locState = AbstractStates.extractLocations(pElements).first();
    if (locState.isPresent() && locState.get().isLoopStart()) {
      if (numberVisits.containsKey(locState.get())) {

        int visits = numberVisits.get(locState.get()) + 1;
        numberVisits.replace(locState.get(), visits);
        if (visits > this.maxLoopIterations) {
          // Return an empty state, which leads to not following this path anymore!
          logger.log(
              Level.INFO,
              String.format(
                  "Reached the limit for node %s, hence stoping the exploration at this point!",
                  locState.get().toString()));
          return Lists.newArrayList();
        }

      } else {
        numberVisits.put(locState.get(), 1);
      }
    }

    return postProcessedResult;
  }



}
