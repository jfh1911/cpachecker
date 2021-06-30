// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.valueExport;

import com.google.common.collect.Sets;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.ADeclaration;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.AParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.AStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
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
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CSimpleType;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.defaults.SingletonPrecision;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisInformation;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState.ValueAndType;
import org.sosy_lab.cpachecker.cpa.value.type.NumericValue;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

public class ValueAnalysisExportTransferRelation
    extends ForwardingTransferRelation<
        ValueAnalysisExportState, ValueAnalysisExportState, SingletonPrecision> {

  private static final String VERIFIER_NONDET = "__VERIFIER_nondet_";

  private static final String CPACHECKER_TEMP = "__CPAchecker_TMP";

  private static final String ID_HEADER = "ID";
  private Path variableValuesCsvFile = null;
  private AtomicInteger id_counter;
  private boolean storeVariableValues = false;

  private final LogManagerWithoutDuplicates logger;

  private boolean isFirstState = true;
  private CFA cfa;

  public ValueAnalysisExportTransferRelation(
      LogManager pLogger,
      Path variableValuesCsvFile,
      boolean storeVariableValues,
      CFA pCfa,
      int pFirstID) {

    logger = new LogManagerWithoutDuplicates(pLogger);
    this.variableValuesCsvFile = variableValuesCsvFile;
    this.storeVariableValues = storeVariableValues;
    this.cfa = pCfa;
    this.id_counter = new AtomicInteger(pFirstID);
    try {
      FileChannel.open(variableValuesCsvFile, StandardOpenOption.WRITE).truncate(0).close();
    } catch (IOException e) {
      logger.log(Level.WARNING, "Could not create csv file, as the file doe snot exists");
    }
  }

  @Override
  protected ValueAnalysisExportState handleFunctionCallEdge(
      FunctionCallEdge callEdge,
      List<? extends AExpression> arguments,
      List<? extends AParameterDeclaration> parameters,
      String calledFunctionName)
      throws UnrecognizedCodeException {
    return state;
  }

  @Override
  protected ValueAnalysisExportState handleBlankEdge(BlankEdge cfaEdge) {
    return state;
  }

  @Override
  protected ValueAnalysisExportState handleReturnStatementEdge(AReturnStatementEdge returnEdge)
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
  protected ValueAnalysisExportState handleFunctionReturnEdge(
      FunctionReturnEdge functionReturnEdge,
      FunctionSummaryEdge summaryEdge,
      AFunctionCall exprOnSummary,
      String callerFunctionName)
      throws UnrecognizedCodeException {

    return state;
  }

  @Override
  protected ValueAnalysisExportState handleFunctionSummaryEdge(CFunctionSummaryEdge cfaEdge)
      throws CPATransferException {
    return state;
  }

  @Override
  protected ValueAnalysisExportState handleAssumption(
      AssumeEdge cfaEdge, AExpression expression, boolean truthValue)
      throws UnrecognizedCodeException {
    return state;
  }

  @Override
  protected ValueAnalysisExportState handleDeclarationEdge(
      ADeclarationEdge declarationEdge, ADeclaration declaration) throws UnrecognizedCodeException {

    return state;
  }

  @Override
  protected ValueAnalysisExportState handleStatementEdge(
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
    assert pElement instanceof ValueAnalysisExportState;

    // Do post processing
    final Collection<AbstractState> postProcessedResult = new ArrayList<>(1);
    postProcessedResult.add(pElement);

    if (storeVariableValues) {
      List<String> lines = new ArrayList<>();
      StringBuilder builder = new StringBuilder();
      for (AbstractState other : pElements) {
        if (other instanceof ValueAnalysisState
            && pCfaEdge != null
            && pCfaEdge.getPredecessor() != null
            && pCfaEdge.getPredecessor().isLoopStart()
            && !postProcessedResult.isEmpty()) {

          // We are at a loop head

          ValueAnalysisState s = (ValueAnalysisState) other;
          ValueAnalysisInformation info = s.getInformation();
          if (isFirstState) {
            lines.addAll(printVariableInformations(info));
            lines.add(builder.toString());
            builder = new StringBuilder();

            builder = builder.append("##");
            builder = builder.append(ID_HEADER + ",");
            for (Entry<MemoryLocation, ValueAndType> ass : info.getAssignments().entrySet()) {
              if (!ass.getKey().getIdentifier().startsWith(CPACHECKER_TEMP)) {
                builder = builder.append(ass.getKey().getIdentifier()).append(",");
              }
            }
            // Remove last ","

              // Remove last ","
              if (builder.lastIndexOf(",") > 0) {
                builder = builder.deleteCharAt(builder.length() - 1);
              }
            lines.add(builder.toString());

            try {
              Files.write(variableValuesCsvFile, lines, StandardCharsets.UTF_8);
              lines.clear();
              // ,StandardOpenOption.TRUNCATE_EXISiTING);
              isFirstState = false;

            } catch (IOException e) {
              logger.log(Level.WARNING, "Could not create csv file, as the file does not exists");
            }
          }
          builder = new StringBuilder();

          // Firstly, append the id
          builder =
              builder.append(pCfaEdge.getLineNumber() + "-" + id_counter.getAndIncrement() + ",");

          for (Entry<MemoryLocation, ValueAndType> ass : info.getAssignments().entrySet()) {
            if (ass.getValue() != null
                && ass.getValue().getValue() != null
                && ass.getValue().getValue() instanceof NumericValue
                && !ass.getKey().getIdentifier().startsWith(CPACHECKER_TEMP)) {
              Number num = ((NumericValue) ass.getValue().getValue()).getNumber();
              builder = builder.append(num.intValue()).append(",");
            }
          }

          // Remove last ","
          if (builder.lastIndexOf(",") > 0) {
            builder = builder.deleteCharAt(builder.length() - 1);
          }

          lines.add(builder.toString());
          builder = new StringBuilder();

          try {
            Files.write(
                variableValuesCsvFile, lines, StandardCharsets.UTF_8, StandardOpenOption.APPEND);

          } catch (IOException e) {
            logger.log(Level.WARNING, "Could not create csv file, as the file does not exists");
          }
        }
      }
    }

    return postProcessedResult;
  }

  private List<String> printVariableInformations(ValueAnalysisInformation pInfo) {
    List<String> lines = new ArrayList<>();
    StringBuilder information = new StringBuilder();
    information = information.append("## Varname, type, isUnsinged, isConstant, isRandomValue");
    lines.add(information.toString());
    information = new StringBuilder();
    Set<CFAEdge> edges = new HashSet<>();
    for (CFANode n : cfa.getAllNodes()) {
      for (int i = 0; i < n.getNumEnteringEdges(); i++) {
        edges.add(n.getEnteringEdge(i));
      }
    }

    Set<String> varsWithRandomValueAssignedTo = new HashSet<>();
    Set<String> varsWithUnchangedValue = computeUnchagnedVars(edges);
    for (CFAEdge e : edges) {
      if (e instanceof CStatementEdge) {
        CStatement statement = ((CStatementEdge) e).getStatement();
        if (statement instanceof CFunctionCallAssignmentStatement) {
          CFunctionCallAssignmentStatement statement2 =
              (CFunctionCallAssignmentStatement) statement;
          if (statement2.getRightHandSide().toString().startsWith(VERIFIER_NONDET)) {
            varsWithRandomValueAssignedTo.add(statement2.getLeftHandSide().toASTString());
          }
        }
      }
    }

    for (Entry<MemoryLocation, ValueAndType> entry : pInfo.getAssignments().entrySet()) {
      if (entry.getValue() != null
          && entry.getValue().getValue() != null
          && entry.getValue().getValue() instanceof NumericValue) {

        information =
            information.append(
                entry.getKey().getIdentifier() + "," + entry.getValue().getType() + ",");
        if (entry.getValue().getType() instanceof CSimpleType) {
          CSimpleType t = (CSimpleType) entry.getValue().getType();
          boolean isConst =
              t.isConst() || varsWithUnchangedValue.contains(entry.getKey().getIdentifier());
          information = information.append(t.isUnsigned() + "," + isConst + ",");
        } else {
          information = information.append("?,?,");
        }

        information =
            information.append(
                varsWithRandomValueAssignedTo.contains(entry.getKey().getIdentifier()));
        lines.add(information.toString());
        information = new StringBuilder();
      }
    }
    return lines;
  }

  private Set<String> computeUnchagnedVars(Set<CFAEdge> pEdges) {
    Set<String> nonConstVars = new HashSet<>();
    Set<String> allVars = new HashSet<>();
    for (CFAEdge e : pEdges) {
      if (e instanceof CDeclarationEdge) {
        CDeclarationEdge ce = (CDeclarationEdge) e;
        if (ce.getDeclaration() instanceof CVariableDeclaration) {
          allVars.add(((CVariableDeclaration) ce.getDeclaration()).getName());
        }
      } else if (e instanceof CStatementEdge) {
        CStatementEdge stmt = (CStatementEdge) e;
        if (stmt.getStatement() instanceof CAssignment) {
          CAssignment assign = (CAssignment) stmt.getStatement();
          if (assign.getLeftHandSide() instanceof CIdExpression) {
            nonConstVars.add(((CIdExpression) assign.getLeftHandSide()).getName());
          }
        }
      }
    }
    // Constant = allVars - nonConstantVars
    return Sets.difference(allVars, nonConstVars);
  }
}
