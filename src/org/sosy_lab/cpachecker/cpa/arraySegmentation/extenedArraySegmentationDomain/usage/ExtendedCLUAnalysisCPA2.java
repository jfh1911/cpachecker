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
package org.sosy_lab.cpachecker.cpa.arraySegmentation.extenedArraySegmentationDomain.usage;

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
import org.sosy_lab.cpachecker.cpa.usageAnalysis.instantiationUsage.VariableUsageState;

@Options(prefix = "cpa.CLUCPA")
public class ExtendedCLUAnalysisCPA2 extends AbstractCPA {

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
  private String varnameArray = "";

  private final LogManager logger;
  private final CFA cfa;
  private final Configuration config;

  private ExtendedUsageAnalysisCPA usageCPA;
  LocationCPA locationCPA;

  private LocationStateFactory factory;

  /**
   * This method acts as the constructor of the interval analysis CPA.
   *
   * @param config the configuration of the CPAinterval analysis CPA.
   */
  private ExtendedCLUAnalysisCPA2(
      Configuration config,
      LogManager pLogger,
      ShutdownNotifier shutdownNotifier,
      CFA cfa)
      throws InvalidConfigurationException {
    super(
        "join",
        "sep",
        DelegateAbstractDomain.<ExtendedCLUAnalysisState<VariableUsageState>>getInstance(),
        null);
    config.inject(this, ExtendedCLUAnalysisCPA2.class);
    // writer = new StateToFormulaWriter(config, pLogger, shutdownNotifier, cfa);

    this.logger = pLogger;
    this.cfa = cfa;
    this.config = config;
    usageCPA = new ExtendedUsageAnalysisCPA(config, logger, cfa, varnameArray, shutdownNotifier);
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
    return AutomaticCPAFactory.forType(ExtendedCLUAnalysisCPA2.class);
  }

  @Override
  public TransferRelation getTransferRelation() {
    return new ExtendedCLUAnanylsisTransferRelation(
        new LogManagerWithoutDuplicates(logger),
        cfa.getMachineModel(),
        this.factory);
  }

  @Override
  public AbstractState getInitialState(CFANode pNode, StateSpacePartition pPartition)
      throws InterruptedException {

    return new ExtendedCLUAnalysisState<VariableUsageState>(
        locationCPA.getInitialState(pNode, pPartition),
        usageCPA.getInitialState(pNode, pPartition),
        this.logger);

  }
}
