/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ExternalInvariantsManager {

  private List<Path> generatedInvariants;
  private List<String> producers;
  boolean mayProduceInvariants = false;

  public ExternalInvariantsManager(boolean pMayProduceInvariants) {
    generatedInvariants = Collections.synchronizedList(new ArrayList<>());
    mayProduceInvariants = pMayProduceInvariants;
    producers = new ArrayList<>();
  }

  public int getNumberOfGeneratedWitnesses() {
    return generatedInvariants.size();
  }

  public void addNewInvariant(Path pathToInv, String producer) {
    System.out.println("new invariant added from tool " + producer);
    this.generatedInvariants.add(pathToInv);
    this.producers.add(producer);
  }

  public void addNewInvariant(List<Path> pathToInv, List<String> pProducers) {
    System.out.println("new invariant added from tool " + pProducers);
    this.generatedInvariants.addAll(pathToInv);
    this.producers.addAll(pProducers);
  }

  public List<Path> getGeneratedInvariants() {
    System.out.println("returning generated invariants at path " + generatedInvariants.toString());
    return Collections.unmodifiableList(generatedInvariants);
  }

  public boolean mayProduceInvariants() {
    return this.mayProduceInvariants;
  }

  /**
   * If the invariant generation will not produce a result, notify the manager using this method
   * (may be useful, if the master analysis waits for the invariant generation to complete)
   */
  public void setInvGenCancled() {
    this.mayProduceInvariants = false;
  }

  public String getProducerOfWitness(int pNumInjectedWitnesses) {
    if (producers.size() > pNumInjectedWitnesses) {
      return producers.get(pNumInjectedWitnesses);
    } else {
      return "No Information available";
    }
  }


}
