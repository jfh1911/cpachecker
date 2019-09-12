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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Predicate;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
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
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegment;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ArraySegmentationState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.ExtendedCompletLatticeAbstractState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.FinalSegment;
import org.sosy_lab.cpachecker.util.Triple;

public class ArraySegmentationCPAHelper<T extends ExtendedCompletLatticeAbstractState<T>> {



  public ArraySegmentationCPAHelper(CFA pCfa, LogManager pLogger, String pVarname_array) {
    super();
    cfa = pCfa;
    logger = pLogger;
    varnameArray = pVarname_array;
  }

  private CFA cfa;
  private LogManager logger;
  private String varnameArray;

  public ArraySegmentationState<T>
      computeInitaleState(
          T pInnerInitaleState,
          Predicate<ArraySegmentationState<T>> pPredicate,
          T pEmptyElement,
          String pName)
          throws InterruptedException {

    Triple<AExpression, CVariableDeclaration, List<AExpression>> initalValuesForArraySegmentationDomain =
        computeInitalForArraySegmentation();

    List<ArraySegment<T>> segments =
        buildInitaleSegmentation(
            initalValuesForArraySegmentationDomain,
            pEmptyElement,
            pInnerInitaleState);

    return new ArraySegmentationState<>(
        segments,
        pInnerInitaleState,
        initalValuesForArraySegmentationDomain.getThird(),
        new CIdExpression(
            initalValuesForArraySegmentationDomain.getSecond().getFileLocation(),
            initalValuesForArraySegmentationDomain.getSecond()),
        initalValuesForArraySegmentationDomain.getFirst(),
        cfa.getLanguage(),
        false,
        pName,
        pPredicate,
        logger);

  }

  private List<ArraySegment<T>> buildInitaleSegmentation(
      Triple<AExpression, CVariableDeclaration, List<AExpression>> initalValuesForArraySegmentationDomain,
      T pEmptyElement,
      T pInitaleAnalysisInformaiton) {
    List<AExpression> pSBSecond = new ArrayList<>();
    // TODO: add handling for Java programs
    // Assume that the Size-var is defined in main method
    pSBSecond.add(initalValuesForArraySegmentationDomain.getFirst());
    List<AExpression> pSBFirst = new ArrayList<>();
    pSBFirst.add(CIntegerLiteralExpression.ZERO);

    ArraySegment<T> second =
        new ArraySegment<>(
            pSBSecond,
            pEmptyElement,
            false,
            new FinalSegment<>(pEmptyElement),
            cfa.getLanguage());

    ArraySegment<T> first =
        new ArraySegment<>(pSBFirst, pInitaleAnalysisInformaiton, true, second, cfa.getLanguage());

    List<ArraySegment<T>> segments = new ArrayList<>();
    segments.add(first);
    segments.add(second);
    return segments;
  }

  protected Triple<AExpression, CVariableDeclaration, List<AExpression>>
      computeInitalForArraySegmentation() throws InterruptedException {
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
              if (decl.getName().equalsIgnoreCase(varnameArray)) {
                arrayVar = decl;
                if (decl.getType() instanceof CArrayType) {
                  CArrayType t = (CArrayType) decl.getType();
                  sizeVar = t.getLength();
                } else {
                  throw new InterruptedException(
                      "The program cannot be analyed, since the array that needs to be ananlyzed in the main function named'"
                          + this.varnameArray
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
              + this.varnameArray
              + "' is not defined!");
    }

    return Triple.of(sizeVar, arrayVar, arrayAccessVars);
  }

  protected Collection<CExpression> computeVars(CRightHandSide pExpr) {
    List<CExpression> res = new ArrayList<>();

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
