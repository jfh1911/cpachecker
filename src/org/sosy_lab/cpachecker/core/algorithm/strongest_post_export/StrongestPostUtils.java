// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.strongest_post_export;

import com.google.common.collect.Lists;
import java.util.Optional;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.CFAUtils;

public class StrongestPostUtils {

  public static Optional<CFANode> getLoopBranchForLoopHead(CFANode pLoopHead, LogManager logger) {
    if (!pLoopHead.isLoopStart()) {
      logger.log(Level.INFO, String.format("The given node %s is not a loopStart!", pLoopHead));
      return Optional.empty();
    }
    if (pLoopHead.getNumLeavingEdges() == 2) {
      return Optional.of(pLoopHead);
    } else if (pLoopHead.getNumLeavingEdges() != 1) {
      logger.log(
          Level.INFO,
          String.format(
              "Dont know how to handle node %s with %d successors! Only 1 or 2 is supported",
              pLoopHead, pLoopHead.getNumLeavingEdges()));
      return Optional.empty();
    }

    // Continue to iterate through the successors of pLoopHead until we reach the first node with
    // two successors having a assume edge.
    // this is the node we are searching for.
    CFANode current = pLoopHead;
    while(current.getNumLeavingEdges() == 1) {
      current = current.getLeavingEdge(0).getSuccessor();
    }
    if (current.getNumLeavingEdges() == 2
        && CFAUtils.allLeavingEdges(current).allMatch(e -> e instanceof CAssumeEdge)) {
      return Optional.of(current);
    }
    return Optional.empty();
  }

  public static Optional<AbstractState> getAbstractStateForLoopHead(
      ARGState pState, CFANode pNode, LogManager logger) {
    if (!AbstractStates.extractLocation(pState).isLoopStart()) {
      logger.log(Level.INFO, String.format("The given node %s is not a loopStart!", pState));
      return Optional.empty();
    }
    if (AbstractStates.extractLocation(pState).equals(pNode)) {
      return Optional.of(pState);
    } else if (pState.getChildren().size() != 1) {
      logger.log(
          Level.INFO,
          String.format(
              "Dont know how to handle node %s with %d successors! Only 1 is supported",
              pNode, pNode.getNumLeavingEdges()));
      return Optional.empty();
    }

    // Continue to iterate through the successors of pState until we reach a node that corresponds
    // to pLoopHead
    ARGState current = pState;
    while (!AbstractStates.extractLocation(current).equals(pNode)) {
      if (pState.getChildren().size() != 1) {
        logger.log(
            Level.INFO,
            String.format(
                "Dont know how to handle node %s with %d successors! Only 1 is supported",
                pNode, pNode.getNumLeavingEdges()));
        return Optional.empty();
      }
      current = Lists.newArrayList(current.getChildren()).get(0);
    }
    return Optional.of(current);
  }
}
