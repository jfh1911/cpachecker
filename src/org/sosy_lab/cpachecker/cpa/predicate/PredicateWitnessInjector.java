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
package org.sosy_lab.cpachecker.cpa.predicate;

import com.google.common.collect.ImmutableList;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport.WitnessInjector;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.composite.CompositePrecision;

public class PredicateWitnessInjector extends WitnessInjector {

  private PredicatePrecisionBootstrapper bootstrapper;


  public PredicateWitnessInjector(PredicatePrecisionBootstrapper pBootstrapper) {
    super();
    bootstrapper = pBootstrapper;
  }

  @Override
  public void inject(ReachedSet pReached, Path pPathToInvariant) {

    PredicatePrecision allPredicatePrecisions=
        bootstrapper.parseInvariantsFromCorrectnessWitnessAsPredicates(pPathToInvariant);
    for(AbstractState s : pReached.asCollection()) {
      if (s instanceof ARGState) {
      ARGState state = ((ARGState)s);
      @Nullable


        Precision p = pReached.getPrecision(state);
        if (p instanceof CompositePrecision) {
          ImmutableList<Precision> prec = ((CompositePrecision) p).getWrappedPrecisions();
          List<Precision> updatedPrec = new ArrayList<>();
          for (int i = 0; i < prec.size(); i++) {
            if (prec.get(i) instanceof PredicatePrecision) {
              updatedPrec.add(((PredicatePrecision) prec.get(i)).mergeWith(allPredicatePrecisions));
            } else {
              updatedPrec.add(prec.get(i));
            }
          }
          Precision newPrecision = new CompositePrecision(updatedPrec);
          pReached.updatePrecision(s, newPrecision);
        }

      }
    }

  }

}
