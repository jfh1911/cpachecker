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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.clu;

import java.util.Arrays;
import java.util.List;
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
import org.sosy_lab.cpachecker.cpa.location.LocationCPA;
import org.sosy_lab.cpachecker.cpa.location.LocationStateFactory;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiation.VariableUsageDomain;
import org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis.UsageAnalysisCPA;

@Options(prefix = "cpa.CLUCPA")
public class CLUAnalysisCPA extends AbstractCPA {

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
  private static final String VARNAME_ARRAY = "a";
  private static final String[] temp = {"i"};
  private static final List<String> ARRAY_ACCESS_VARS = Arrays.asList(temp);
  private final CFA cfa;
  private final Configuration config;

  private ShutdownNotifier shutdownNotifier;
  private UsageAnalysisCPA usageCPA;
  LocationCPA locationCPA;

  private LocationStateFactory factory;

  /**
   * This method acts as the constructor of the interval analysis CPA.
   *
   * @param config the configuration of the CPAinterval analysis CPA.
   */
  private CLUAnalysisCPA(
      Configuration config,
      LogManager pLogger,
      ShutdownNotifier shutdownNotifier,
      CFA cfa)
      throws InvalidConfigurationException {
    super(
        "join",
        "sep",
        DelegateAbstractDomain.<CLUAnalysisState<VariableUsageDomain>>getInstance(),
        null);
    config.inject(this, CLUAnalysisCPA.class);
    // writer = new StateToFormulaWriter(config, pLogger, shutdownNotifier, cfa);

    this.logger = pLogger;
    this.cfa = cfa;
    this.config = config;
    this.shutdownNotifier = shutdownNotifier;
    usageCPA = new UsageAnalysisCPA(config, logger, shutdownNotifier, cfa);
    locationCPA = LocationCPA.create(this.cfa, this.config);
    this.factory = new LocationStateFactory(cfa, AnalysisDirection.FORWARD, config);
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
    return AutomaticCPAFactory.forType(CLUAnalysisCPA.class);
  }

  @Override
  public TransferRelation getTransferRelation() {
    return new CLUAnanylsisTransferRelation(
        new LogManagerWithoutDuplicates(logger),
        cfa.getMachineModel(),
        this.factory);
  }

  @Override
  public AbstractState getInitialState(CFANode pNode, StateSpacePartition pPartition)
      throws InterruptedException {

    return new CLUAnalysisState<VariableUsageDomain>(
        locationCPA.getInitialState(pNode, pPartition),
        usageCPA.getInitialState(pNode, pPartition),
        this.logger);


  }
}
