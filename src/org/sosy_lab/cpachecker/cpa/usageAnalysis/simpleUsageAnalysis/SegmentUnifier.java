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
package org.sosy_lab.cpachecker.cpa.usageAnalysis.simpleUsageAnalysis;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiPredicate;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.Pair;

public class SegmentUnifier<T extends LatticeAbstractState<T>> {
  private BiPredicate<Boolean, Boolean> curleyVee = new BiPredicate<Boolean, Boolean>() {
    @Override
    public boolean test(Boolean pArg0, Boolean pArg1) {
      return pArg0 || pArg1;
    }
  };

  BiPredicate<Boolean, Boolean> curleyWedge = new BiPredicate<Boolean, Boolean>() {
    @Override
    public boolean test(Boolean pArg0, Boolean pArg1) {
      return pArg0 && pArg1;
    }
  };

  BinaryOperator<T> sqcup = new BinaryOperator<T>() {

    @Override
    public T apply(T pArg0, T pArg1) {
      try {
        return pArg0.join(pArg1);
      } catch (CPAException | InterruptedException e) {
        // FIXME: Extend error handling!
        e.printStackTrace();
        throw new IllegalArgumentException(e);
      }
    }
  };

  public Pair<ArraySegmentationState<T>, ArraySegmentationState<T>>
      unifyMerge(ArraySegmentationState<T> d1, ArraySegmentationState<T> d2, T il, T ir)
          throws CPAException {
    return this.unifyGeneric(d1, d2, il, ir, sqcup, sqcup, curleyVee, curleyVee);
  }

  public Pair<ArraySegmentationState<T>, ArraySegmentationState<T>> unifyCompare(
      ArraySegmentationState<T> d1,
      ArraySegmentationState<T> d2,
      T il,
      T ir,
      BinaryOperator<T> sqcap)
      throws CPAException {

    // _|_, _|_, sqcup, sqcap, v , ^
    return this.unifyGeneric(d1, d2, il, ir, sqcup, sqcap, curleyVee, curleyWedge);
  }

  public Pair<ArraySegmentationState<T>, ArraySegmentationState<T>> unifyGeneric(
      ArraySegmentationState<T> pD1,
      ArraySegmentationState<T> pD2,
      T il,
      T ir,
      BinaryOperator<T> ol,
      BinaryOperator<T> or,
      BiPredicate<Boolean, Boolean> hatl,
      BiPredicate<Boolean, Boolean> hatr)
      throws CPAException {

    ArraySegmentationState<T> d1 = pD1.clone();
    ArraySegmentationState<T> copyForLoggingOfD1 = pD1.clone();
    ArraySegmentationState<T> copyForLoggingOfD2 = pD2.clone();

    ArraySegmentationState<T> d2 = pD2.clone();

    // Case 1:
    if (d1 instanceof ErrorSegmentation
        || d1 instanceof UnreachableArraySegmentation
        || d2 instanceof ErrorSegmentation
        || d2 instanceof UnreachableArraySegmentation) {
      return Pair.of(d1, d2);
    }

    if (d1.getSegments().isEmpty() || d2.getSegments().isEmpty()) {
      throw new IllegalArgumentException("Cannot unify empty segments");
    }

    // Setup some vars and pointer needed:
    List<ArraySegment<T>> segs1 = d1.getSegments();
    List<ArraySegment<T>> segs2 = d2.getSegments();
    ArraySegment<T> b1 = segs1.get(0);
    ArraySegment<T> b2 = segs2.get(0);

    // Create resultLists, the concatination will be done in the end
    List<ArraySegment<T>> res1 = new ArrayList<>();
    List<ArraySegment<T>> res2 = new ArrayList<>();

    // The algorithm terminates, if the left and the rigth segment bound are reached with the
    // pointer

    while ((!(b1 instanceof FinalSegSymbol)) && (!(b2 instanceof FinalSegSymbol))) {
      // Case 2: Both segment bounds are equal
      if (b1.getSegmentBound().containsAll(b2.getSegmentBound())
          && b2.getSegmentBound().containsAll(b1.getSegmentBound())) {
        res1.add(b1);
        res2.add(b2);
        b1 = b1.getNextSegment();
        b2 = b2.getNextSegment();
        continue;
      }
      // Needed in all other cases:
      List<AExpression> b1SegBounds = b1.getSegmentBound();
      List<AExpression> b2SegBounds = b2.getSegmentBound();
      List<AExpression> b1Bar =
          d2.getSegmentBounds(b2.getNextSegment())
              .parallelStream()
              .filter(b -> b1SegBounds.contains(b))
              .collect(Collectors.toList());
      List<AExpression> b2Bar =
          d1.getSegmentBounds(b1.getNextSegment())
              .parallelStream()
              .filter(b -> b2SegBounds.contains(b))
              .collect(Collectors.toList());
      // Compute the expressions, that are present in both segment bounds
      List<AExpression> subsetOfB1_B2 = new ArrayList<>();
      b1SegBounds.parallelStream()
          .filter(e -> b2SegBounds.contains(e))
          .forEach(e -> subsetOfB1_B2.add(e));

      // Case 3:
      if (b1SegBounds.containsAll(b2SegBounds)) {
        // Case 3.1
        // replace the segment bounds from b1 with them of B2, since the SB of B1 are a superset of
        // B2
        if (b1Bar.isEmpty()) {
          b1.setSegmentBound(b2SegBounds);
          continue;
        }
        // Case 3.2
        // To avoid confusen, crate two new elements, where the first is temp1 = B1\B1Bar I_l ?
        // and the second temp2 = B1Bar p1 ?1
        ArraySegment<T> temp2 =
            new ArraySegment<>(
                b1Bar,
                b1.getAnalysisInformation(),
                b1.isPotentiallyEmpty(),
                b1.getNextSegment());
        ArraySegment<T> temp1 = new ArraySegment<>(subsetOfB1_B2, il, true, temp2);
        b1 = temp1;
        continue;
      }

      // Case 4:
      if (b2.getSegmentBound().containsAll(b1.getSegmentBound())) {
        // Case 4.1
        // replace the segment bounds from b1 with them of B2, since the SB of B1 are a superset of
        // B2
        if (b2Bar.isEmpty()) {
          b2.setSegmentBound(b1SegBounds);
          continue;
        }
        // Case 4.2
        // To avoid confusen, crate two new elements, where the first is temp1 = B2\B2Bar I_r ?
        // and the second temp2 = B2Bar p2 ?2
        ArraySegment<T> temp2 =
            new ArraySegment<>(
                b2Bar,
                b2.getAnalysisInformation(),
                b2.isPotentiallyEmpty(),
                b2.getNextSegment());
        ArraySegment<T> temp1 = new ArraySegment<>(subsetOfB1_B2, ir, true, temp2);
        b2 = temp1;
        continue;
      }

      // Case 5:
      // Firstly, check if there is an expression in B1 presnt in B2 and vice versa

      if (b1SegBounds.parallelStream().anyMatch(b -> b2SegBounds.contains(b))
          && b2SegBounds.parallelStream().anyMatch(b -> b1SegBounds.contains(b))) {

        // Case 5.1 B1Bar = B2Bar = emptyset
        if (b1Bar.isEmpty() && b2Bar.isEmpty()) {
          // Reassign b1 and b2
          b1.setSegmentBound(subsetOfB1_B2);
          b2.setSegmentBound(subsetOfB1_B2);
          continue;
        } else if (b1Bar.isEmpty()) {
          // Case 5.2
          b1.setSegmentBound(subsetOfB1_B2);
          // To avoid confusen, crate two new elements, where the first is temp1 = B2\B2Bar I_r ?
          // and the second temp2 = B2Bar p2 ?2
          ArraySegment<T> temp2 =
              new ArraySegment<>(
                  b2Bar,
                  b2.getAnalysisInformation(),
                  b2.isPotentiallyEmpty(),
                  b2.getNextSegment());
          ArraySegment<T> temp1 = new ArraySegment<>(subsetOfB1_B2, ir, true, temp2);
          b2 = temp1;
          continue;
        } else if (b2Bar.isEmpty()) {
          // Case 5.3
          // To avoid confusen, crate two new elements, where the first is temp1 = B1\B1Bar I_l ?
          // and the second temp2 = B1Bar p1 ?1
          ArraySegment<T> temp2 =
              new ArraySegment<>(
                  b1Bar,
                  b1.getAnalysisInformation(),
                  b1.isPotentiallyEmpty(),
                  b1.getNextSegment());
          ArraySegment<T> temp1 = new ArraySegment<>(subsetOfB1_B2, il, true, temp2);
          b1 = temp1;
          b2.setSegmentBound(subsetOfB1_B2);
          continue;
        } else {
          // Firstly, remove b1Bar from B1 for the second argument named b1Temp, than use this
          // element and create a new one pointing to this
          ArraySegment<T> b1Temp = b1.removeExprFromBound(b1Bar);
          // Create B1Bar Il ? B1\B1Bar
          b1 = new ArraySegment<>(b1Bar, il, true, b1Temp);
          // Firstly, remove b2Bar from B2 for the second argument named b2Temp, than use this
          // element
          // and create a new one pointing to this
          ArraySegment<T> b2Temp = b2.removeExprFromBound(b2Bar);
          // Create B2Bar Ir ? B2\B2Bar
          b2 = new ArraySegment<>(b2Bar, ir, true, b2Temp);
          continue;
        }
      }

      // Load the last unified element (needed for cases 6-8):
      if (res1.isEmpty() || res2.isEmpty()) {
        throw new CPAException(
            "The unififcation failed for the elements "
                + copyForLoggingOfD1.toDOTLabel()
                + " and  "
                + copyForLoggingOfD2.toDOTLabel());
      }
      ArraySegment<T> b0 = res1.get(res1.size() - 1);
      ArraySegment<T> b0Prime = res2.get(res2.size() - 1);
      // Since they will be readded later on, remove tb0 and b0' from res1 and res2
      res1.remove(b0);
      res2.remove(b0Prime);

      // Case 6: Ensure that there is no intersection of B1 and B2
      if (!(b1.getSegmentBound().parallelStream().anyMatch(b -> b2SegBounds.contains(b))
          || b2.getSegmentBound().parallelStream().anyMatch(b -> b1SegBounds.contains(b)))) {

        if ((!b1Bar.isEmpty()) && b2Bar.isEmpty()) {
          // Case 6.1
          b0.setNextSegment(
              new ArraySegment<>(
                  b1Bar,
                  b1.getAnalysisInformation(),
                  b1.isPotentiallyEmpty(),
                  b1.getNextSegment()));
          b1 = b0;
          // Merge the analysis informaiton from B2 into B0' and remove the segment B2
          b0Prime.setAnalysisInformation(
              or.apply(b0Prime.getAnalysisInformation(), b2.getAnalysisInformation()));
          b0Prime.setPotentiallyEmpty(
              hatr.test(b0Prime.isPotentiallyEmpty(), b2.isPotentiallyEmpty()));
          b0Prime.setNextSegment(b2.getNextSegment());
          b2 = b0Prime;
          continue;
        } else if (b1Bar.isEmpty() && (!b2Bar.isEmpty())) {
          // Case 6.2
          // Merge the analysis informaiton from B1 into B0 and remove the segment B1
          b0.setAnalysisInformation(
              ol.apply(b0.getAnalysisInformation(), b1.getAnalysisInformation()));
          b0.setPotentiallyEmpty(hatl.test(b0.isPotentiallyEmpty(), b1.isPotentiallyEmpty()));
          b0.setNextSegment(b1.getNextSegment());
          b1 = b0;
          b0Prime.setNextSegment(
              new ArraySegment<>(
                  b2Bar,
                  b2.getAnalysisInformation(),
                  b2.isPotentiallyEmpty(),
                  b2.getNextSegment()));
          b2 = b0Prime;

          continue;
        } else {
          // Case 6.3
          // Merge the analysis informaiton from B1 into B0 and remove the segment B1
          b0.setAnalysisInformation(
              ol.apply(b0.getAnalysisInformation(), b1.getAnalysisInformation()));
          b0.setPotentiallyEmpty(hatl.test(b0.isPotentiallyEmpty(), b1.isPotentiallyEmpty()));
          b0.setNextSegment(b1.getNextSegment());
          b1 = b0;
          // Merge the analysis informaiton from B2 into B0' and remove the segment B2
          b0Prime.setAnalysisInformation(
              or.apply(b0Prime.getAnalysisInformation(), b2.getAnalysisInformation()));
          b0Prime.setPotentiallyEmpty(
              hatr.test(b0Prime.isPotentiallyEmpty(), b2.isPotentiallyEmpty()));
          b0Prime.setNextSegment(b2.getNextSegment());
          b2 = b0Prime;
          continue;
        }
      }

      // Case 7: Right limit reached
      if (!(b1.getNextSegment() instanceof FinalSegSymbol)
          && b2.getNextSegment() instanceof FinalSegSymbol) {
        // Merge the analysis informaiton from B1 into B0 and remove the segment B1
        b0.setAnalysisInformation(
            ol.apply(b0.getAnalysisInformation(), b1.getAnalysisInformation()));
        b0.setPotentiallyEmpty(hatl.test(b0.isPotentiallyEmpty(), b1.isPotentiallyEmpty()));
        b0.setNextSegment(b1.getNextSegment());
        b1 = b0;
        continue;

      }
      // Case 8: Left limit reached
      if (b1.getNextSegment() instanceof FinalSegSymbol
          && !(b2.getNextSegment() instanceof FinalSegSymbol)) {
        // Merge the analysis informaiton from B2 into B0' and remove the segment B2
        b0Prime.setAnalysisInformation(
            or.apply(b0Prime.getAnalysisInformation(), b2.getAnalysisInformation()));
        b0Prime
            .setPotentiallyEmpty(hatr.test(b0Prime.isPotentiallyEmpty(), b2.isPotentiallyEmpty()));
        b0Prime.setNextSegment(b2.getNextSegment());
        b2 = b0Prime;
        continue;

      }
      // Case 9:
      if (b1.getNextSegment() instanceof FinalSegSymbol
          && b2.getNextSegment() instanceof FinalSegSymbol) {
        // Termination, hence break loop (should happen anyway
        break;
      }

    }
    return Pair.of(
        new ArraySegmentationState<>(
            conc(res1, d1.gettEmptyElement()),
            d1.gettBottom(),
            d1.gettTop(),
            d1.gettEmptyElement(),
            d1.gettMeet(),
            d1.gettLisOfArrayVariables(),
            d1.gettArray(),
            d1.getLogger()),
        new ArraySegmentationState<>(
            conc(res2, d2.gettEmptyElement()),
            d2.gettBottom(),
            d2.gettTop(),
            d2.gettEmptyElement(),
            d2.gettMeet(),
            d1.gettLisOfArrayVariables(),
            d1.gettArray(),
            d2.getLogger()));

  }

  public List<ArraySegment<T>> conc(List<ArraySegment<T>> pCopiedElements, T pEmptyElement) {
    if (pCopiedElements.isEmpty()) {
      throw new IllegalArgumentException("Cannot concatinate an empty list of elements");
    }
    for (int i = 0; i < pCopiedElements.size() - 1; i++) {
      pCopiedElements.get(i).setNextSegment(pCopiedElements.get(i + 1));
    }
    pCopiedElements.get(pCopiedElements.size() - 1)
        .setNextSegment(new FinalSegSymbol<>(pEmptyElement));
    return pCopiedElements;
  }

}
