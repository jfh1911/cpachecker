/*
 * CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2017  Dirk Beyer
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
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cfa.parser.eclipse.js;

import org.eclipse.wst.jsdt.core.dom.BooleanLiteral;
import org.eclipse.wst.jsdt.core.dom.ConditionalExpression;
import org.eclipse.wst.jsdt.core.dom.Expression;
import org.eclipse.wst.jsdt.core.dom.FunctionExpression;
import org.eclipse.wst.jsdt.core.dom.FunctionInvocation;
import org.eclipse.wst.jsdt.core.dom.InfixExpression;
import org.eclipse.wst.jsdt.core.dom.NullLiteral;
import org.eclipse.wst.jsdt.core.dom.NumberLiteral;
import org.eclipse.wst.jsdt.core.dom.PostfixExpression;
import org.eclipse.wst.jsdt.core.dom.PrefixExpression;
import org.eclipse.wst.jsdt.core.dom.SimpleName;
import org.eclipse.wst.jsdt.core.dom.StringLiteral;
import org.eclipse.wst.jsdt.core.dom.UndefinedLiteral;
import org.sosy_lab.cpachecker.cfa.ast.js.JSExpression;

class ExpressionCFABuilder implements ExpressionAppendable {

  private ConditionalExpressionAppendable conditionalExpressionAppendable;
  private FunctionExpressionAppendable functionExpressionAppendable;
  private FunctionInvocationAppendable functionInvocationAppendable;
  private InfixExpressionAppendable infixExpressionAppendable;
  private PrefixExpressionAppendable prefixExpressionAppendable;
  private PostfixExpressionAppendable postfixExpressionAppendable;

  void setConditionalExpressionAppendable(
      final ConditionalExpressionAppendable pConditionalExpressionAppendable) {
    conditionalExpressionAppendable = pConditionalExpressionAppendable;
  }

  void setFunctionExpressionAppendable(
      final FunctionExpressionAppendable pFunctionExpressionAppendable) {
    functionExpressionAppendable = pFunctionExpressionAppendable;
  }

  void setFunctionInvocationAppendable(
      final FunctionInvocationAppendable pFunctionInvocationAppendable) {
    functionInvocationAppendable = pFunctionInvocationAppendable;
  }
  void setInfixExpressionAppendable(
      final InfixExpressionAppendable pInfixExpressionAppendable) {
    infixExpressionAppendable = pInfixExpressionAppendable;
  }

  void setPrefixExpressionAppendable(
      final PrefixExpressionAppendable pPrefixExpressionAppendable) {
    prefixExpressionAppendable = pPrefixExpressionAppendable;
  }

  void setPostfixExpressionAppendable(
      final PostfixExpressionAppendable pPostfixExpressionAppendable) {
    postfixExpressionAppendable = pPostfixExpressionAppendable;
  }

  @Override
  public JSExpression append(final JavaScriptCFABuilder pBuilder, final Expression pExpression) {
    if (pExpression instanceof ConditionalExpression) {
      return conditionalExpressionAppendable.append(pBuilder, (ConditionalExpression) pExpression);
    } else if (pExpression instanceof FunctionExpression) {
      return functionExpressionAppendable.append(pBuilder, (FunctionExpression) pExpression);
    } else if (pExpression instanceof FunctionInvocation) {
      return functionInvocationAppendable.append(pBuilder, (FunctionInvocation) pExpression);
    }
    // TODO do without ASTConverter
    if (pExpression instanceof SimpleName) {
      return pBuilder.getAstConverter().convert((SimpleName) pExpression);
    } else if (pExpression instanceof InfixExpression) {
      return infixExpressionAppendable.append(pBuilder, (InfixExpression) pExpression);
    } else if (pExpression instanceof PrefixExpression) {
      return prefixExpressionAppendable.append(pBuilder, (PrefixExpression) pExpression);
    } else if (pExpression instanceof PostfixExpression) {
      return postfixExpressionAppendable.append(pBuilder, (PostfixExpression) pExpression);
    } else if (pExpression instanceof StringLiteral) {
      return pBuilder.getAstConverter().convert((StringLiteral) pExpression);
    } else if (pExpression instanceof NumberLiteral) {
      return pBuilder.getAstConverter().convert((NumberLiteral) pExpression);
    } else if (pExpression instanceof BooleanLiteral) {
      return pBuilder.getAstConverter().convert((BooleanLiteral) pExpression);
    } else if (pExpression instanceof NullLiteral) {
      return pBuilder.getAstConverter().convert((NullLiteral) pExpression);
    } else if (pExpression instanceof UndefinedLiteral) {
      return pBuilder.getAstConverter().convert((UndefinedLiteral) pExpression);
    } else if (pExpression == null) {
      // This might be caused by a bug in the eclipse parser,
      // for example: https://bugs.eclipse.org/bugs/show_bug.cgi?id=518324
      throw new CFAGenerationRuntimeException(
          "The expression to convert is null. This might be "
              + "caused by explicitly assigning undefined in a variable declaration.");
    }
    throw new CFAGenerationRuntimeException(
        "Unknown kind of expression (not handled yet): " + pExpression.getClass().getSimpleName(),
        pExpression);
  }
}