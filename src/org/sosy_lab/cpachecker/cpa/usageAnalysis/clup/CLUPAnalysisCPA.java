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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.clup;

import java.util.Map;
import java.util.NavigableSet;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.AnalysisDirection;
import org.sosy_lab.cpachecker.core.defaults.AbstractCPA;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.defaults.DelegateAbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.cpa.ifcsecurity.ControlDependenceComputer;
import org.sosy_lab.cpachecker.cpa.ifcsecurity.DominanceFrontier;
import org.sosy_lab.cpachecker.cpa.ifcsecurity.Dominators;
import org.sosy_lab.cpachecker.cpa.location.LocationCPA;
import org.sosy_lab.cpachecker.cpa.location.LocationStateFactory;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.arraySegmentationDomain.formula.FormulaRelation;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.clu.CLUAnalysisState;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.UsageAnalysisCPA;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.VariableUsageState;

@Options(prefix = "cpa.CLUCPA")
public class CLUPAnalysisCPA extends AbstractCPA {

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
  private final CFA cfa;
  private final Configuration config;

  private UsageAnalysisCPA usageCPA;
  LocationCPA locationCPA;

  private LocationStateFactory factory;

  private FormulaRelation formulaRelation;

  private Map<CFANode, NavigableSet<CFANode>> rcd;

  /**
   * This method acts as the constructor of the interval analysis CPA.
   *
   * @param config the configuration of the CPAinterval analysis CPA.
   */
  private CLUPAnalysisCPA(
      Configuration config,
      LogManager pLogger,
      ShutdownNotifier shutdownNotifier,
      CFA pCfa)
      throws InvalidConfigurationException {
    super(
        "join",
        "sep",
        DelegateAbstractDomain.<CLUAnalysisState<VariableUsageState>>getInstance(),
        null);
    config.inject(this, CLUPAnalysisCPA.class);
    // writer = new StateToFormulaWriter(config, pLogger, shutdownNotifier, cfa);

    this.logger = pLogger;
    this.cfa = pCfa;
    this.config = config;
    usageCPA = new UsageAnalysisCPA(config, logger, shutdownNotifier, pCfa);
    locationCPA = LocationCPA.create(this.cfa, this.config);
    this.factory = new LocationStateFactory(pCfa, AnalysisDirection.FORWARD, config);

    Dominators postdom = new Dominators(pCfa, 1);
    postdom.execute();
    Map<CFANode, CFANode> postdominators = postdom.getDom();
    pLogger.log(Level.FINE, "Postdominators");
    pLogger.log(Level.FINE, postdominators);

    DominanceFrontier domfron = new DominanceFrontier(pCfa, postdominators);
    domfron.execute();
    Map<CFANode, NavigableSet<CFANode>> df = domfron.getDominanceFrontier();
    pLogger.log(Level.FINE, "Dominance Frontier");
    pLogger.log(Level.FINE, df);

    ControlDependenceComputer cdcom = new ControlDependenceComputer(pCfa, df);
    cdcom.execute();
    Map<CFANode, NavigableSet<CFANode>> cd = cdcom.getControlDependency();
    pLogger.log(Level.FINE, "Control Dependency");
    pLogger.log(Level.FINE, cd);

    Map<CFANode, NavigableSet<CFANode>> recd = cdcom.getReversedControlDependency();
    pLogger.log(Level.FINE, "Reversed Control Dependency");
    pLogger.log(Level.FINE, recd);
    this.rcd = recd;

    this.formulaRelation = new FormulaRelation(config, pLogger, shutdownNotifier, pCfa, rcd);
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
    return AutomaticCPAFactory.forType(CLUPAnalysisCPA.class);
  }

  @Override
  public TransferRelation getTransferRelation() {

    return new CLUPAnanylsisTransferRelation(
        new LogManagerWithoutDuplicates(logger),
        cfa.getMachineModel(),
        factory,
        formulaRelation);

  }

  @Override
  public AbstractState getInitialState(CFANode pNode, StateSpacePartition pPartition)
      throws InterruptedException {

    return new CLUPAnalysisState<VariableUsageState>(
        locationCPA.getInitialState(pNode, pPartition),
        usageCPA.getInitialState(pNode, pPartition),
        formulaRelation.makeInitial(),
        this.logger);

  }
}
