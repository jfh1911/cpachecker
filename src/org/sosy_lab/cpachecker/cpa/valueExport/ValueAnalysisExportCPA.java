// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.valueExport;

import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.defaults.AbstractCPA;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.defaults.DelegateAbstractDomain;
import org.sosy_lab.cpachecker.core.defaults.MergeSepOperator;
import org.sosy_lab.cpachecker.core.defaults.StopAlwaysOperator;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;

@Options(prefix = "cpa.valueExport")
public class ValueAnalysisExportCPA extends AbstractCPA implements ConfigurableProgramAnalysis {

  @Option(
      secure = true,
      description =
          "Create a csv file that contains the values for all program variables. The ordering is saved within the "
              + "first row. Moreover, the information, if the variable is initally assigned by a random function is stored. "
              + "The type ending '.csv' is added auztomatically.")
  private String variableValuesCsvFile = "output/variables";

  @Option(secure = true, description = "Enable storing the variable values.")
  private boolean storeVariableValues = false;

  @Option(secure = true, description = "ID to start with at data-generation.")
  private int firstID = 1;

  @Option(
      secure = true,
      description =
          "Default Value for unknown values (variable values that are undefined) at exported file. By default '?'.")
  private String defaultForUndefined = "?";

  @Option(
      secure = true,
      description = "Export currently computed data after each X-th loop iterations.")
  private int exportAfterXIterations = 50;

  @Option(
      secure = true,
      description =
          "Trie to abort theexecution after the loop is visited x times. -1 for no aborting")
  private int maxLoopIteration = -1;

  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(ValueAnalysisExportCPA.class);
  }

  private final LogManager logger;
  private final CFA cfa;

  private ValueAnalysisExportCPA(Configuration config, LogManager logger, CFA cfa)
      throws InvalidConfigurationException {
    super(DelegateAbstractDomain.<ValueAnalysisExportState>getInstance(), null);
    this.logger = logger;
    this.cfa = cfa;

    config.inject(this, ValueAnalysisExportCPA.class);
  }

  @Override
  public MergeOperator getMergeOperator() {
    return new MergeSepOperator();
  }

  @Override
  public StopOperator getStopOperator() {
    return new StopAlwaysOperator();
  }

  @Override
  public ValueAnalysisExportTransferRelation getTransferRelation() {
    return new ValueAnalysisExportTransferRelation(
        logger,
        variableValuesCsvFile,
        storeVariableValues,
        cfa,
        firstID,
        defaultForUndefined,
        exportAfterXIterations,
        maxLoopIteration);
  }

  @Override
  public AbstractState getInitialState(CFANode pNode, StateSpacePartition pPartition) {
    return new ValueAnalysisExportState();
  }
}
