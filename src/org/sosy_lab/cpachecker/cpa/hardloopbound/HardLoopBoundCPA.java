// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.hardloopbound;

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

@Options(prefix = "cpa.hardloopbound")
public class HardLoopBoundCPA extends AbstractCPA implements ConfigurableProgramAnalysis {

  @Option(
      secure = true,
      description = "Abort the execution after the loop is visited x times. -1 for no aborting")
  private int hardLoopbound = -1;

  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(HardLoopBoundCPA.class);
  }

  private final LogManager logger;
  private final CFA cfa;


  private HardLoopBoundCPA(Configuration config, LogManager logger, CFA cfa)
      throws InvalidConfigurationException {
    super(DelegateAbstractDomain.<HardLoopbonudState>getInstance(), null);
    this.logger = logger;
    this.cfa = cfa;

    config.inject(this, HardLoopBoundCPA.class);
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
  public HardLoopboundTransferFunctino getTransferRelation() {
    return new HardLoopboundTransferFunctino(logger, hardLoopbound);
  }

  @Override
  public AbstractState getInitialState(CFANode pNode, StateSpacePartition pPartition) {
    return new HardLoopbonudState();
  }
}
