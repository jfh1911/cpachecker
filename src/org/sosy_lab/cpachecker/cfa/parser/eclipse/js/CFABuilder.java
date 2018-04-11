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

import com.google.common.collect.Lists;
import com.google.common.collect.TreeMultimap;
import java.util.TreeMap;
import java.util.function.BiFunction;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFACreationUtils;
import org.sosy_lab.cpachecker.cfa.Language;
import org.sosy_lab.cpachecker.cfa.ParseResult;
import org.sosy_lab.cpachecker.cfa.model.AbstractCFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cfa.model.js.JSFunctionEntryNode;

class CFABuilder {
  private final Scope scope;
  private final LogManager logger;
  private final ASTConverter astConverter;

  private final ParseResult parseResult;

  private final String functionName;

  private CFANode exitNode;

  CFABuilder(
      final Scope pScope,
      final LogManager pLogger,
      final ASTConverter pAstConverter,
      final JSFunctionEntryNode pEntryNode) {
    this(pScope, pLogger, pAstConverter, pEntryNode.getFunctionName(), pEntryNode);
    parseResult.getFunctions().put(functionName, pEntryNode);
    parseResult.getCFANodes().put(functionName, pEntryNode);
    parseResult.getCFANodes().put(functionName, pEntryNode.getExitNode());
  }

  CFABuilder(
      final Scope pScope,
      final LogManager pLogger,
      final ASTConverter pAstConverter,
      final String pFunctionName,
      final CFANode pEntryNode) {
    scope = pScope;
    logger = pLogger;
    astConverter = pAstConverter;
    functionName = pFunctionName;
    exitNode = pEntryNode;
    parseResult =
        new ParseResult(
            new TreeMap<>(), TreeMultimap.create(), Lists.newArrayList(), Lists.newArrayList());
    parseResult.getCFANodes().put(functionName, pEntryNode);
  }

  public CFABuilder addParseResult(final ParseResult pParseResult) {
    // TODO move to ParseResult?
    parseResult.getFunctions().putAll(pParseResult.getFunctions());
    parseResult.getCFANodes().putAll(pParseResult.getCFANodes());
    parseResult.getGlobalDeclarations().addAll(pParseResult.getGlobalDeclarations());
    return this;
  }

  public CFABuilder append(final CFABuilder builder) {
    addParseResult(builder.getParseResult());

    if (!(builder.exitNode instanceof FunctionExitNode)) {
      exitNode = builder.exitNode;
    }
    return this;
  }

  public CFABuilder appendEdge(final BiFunction<CFANode, CFANode, AbstractCFAEdge> createEdge) {
    return appendEdge(new CFANode(functionName), createEdge);
  }

  public CFABuilder appendEdge(
      final CFANode nextNode, final BiFunction<CFANode, CFANode, AbstractCFAEdge> createEdge) {
    parseResult.getCFANodes().put(functionName, exitNode);
    final AbstractCFAEdge edge = createEdge.apply(exitNode, nextNode);
    exitNode = nextNode;
    CFACreationUtils.addEdgeToCFA(edge, logger);
    return this;
  }

  public CFANode createNode() {
    final CFANode node = new CFANode(functionName);
    parseResult.getCFANodes().put(functionName, node);
    return node;
  }

  public ParseResult getParseResult() {
    return parseResult;
  }

  public ASTConverter getAstConverter() {
    return astConverter;
  }

  public CFANode getExitNode() {
    return exitNode;
  }

  public LogManager getLogger() {
    return logger;
  }

  public String getFunctionName() {
    return functionName;
  }

  public Scope getScope() {
    return scope;
  }

  public String getFilename() {
    return getScope().getFileName();
  }

}