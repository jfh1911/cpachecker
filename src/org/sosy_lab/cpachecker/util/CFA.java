/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2010  Dirk Beyer
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
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.util;

import static com.google.common.base.Preconditions.checkState;
import static com.google.common.collect.Iterables.filter;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.objectmodel.CFAEdge;
import org.sosy_lab.cpachecker.cfa.objectmodel.CFAFunctionDefinitionNode;
import org.sosy_lab.cpachecker.cfa.objectmodel.CFANode;
import org.sosy_lab.cpachecker.cfa.objectmodel.c.FunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.objectmodel.c.FunctionReturnEdge;

import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedSet;
import com.google.common.collect.Sets;

public class CFA {

  /**
   * Find all nodes of the CFA that are reachable from the given entry point.
   * 
   * Same as {@link #transitiveSuccessors(CFANode, boolean)}.
   * 
   * @param rootNode  The start node of the search.
   * @param interprocedural Whether interprocedural edges (function call/return) should be followed. 
   * @return A set of nodes.
   */
  public static Set<CFANode> allNodes(CFAFunctionDefinitionNode rootNode, boolean interprocedural) {
    return transitiveSuccessors(rootNode, interprocedural);
  }

  /**
   * Find all nodes of the CFA that are reachable from the given entry point.
   * @param node  The start node of the search.
   * @param interprocedural Whether interprocedural edges (function call/return) should be followed. 
   * @return A set of nodes.
   */
  public static Set<CFANode> transitiveSuccessors(CFANode node, boolean interprocedural) {
    Set<CFANode> allNodes = new HashSet<CFANode>();
    dfs(node, allNodes, false, interprocedural);
    return allNodes;
  }
  
  /**
   * Find all nodes of the CFA from which a given node is reachable.
   * @param node  The start node of the backwards search.
   * @param interprocedural Whether interprocedural edges (function call/return) should be followed. 
   * @return A set of nodes.
   */
  public static Set<CFANode> transitivePredecessors(CFANode node, boolean interprocedural) {
    Set<CFANode> allNodes = new HashSet<CFANode>();
    dfs(node, allNodes, true, interprocedural);
    return allNodes;
  }
  
  /**
   * Perform a DFS search on the CFA. All visited nodes are added to a given set.
   * If this set is non-empty at the beginning, the search does not traverse
   * beyond the nodes of this set (the part of the CFA reachable from these nodes
   * is considered to be know already).
   * 
   * @param start The start node of the search.
   * @param seen A set of nodes that have already been visited.
   * @param reverse Whether to go backwards or forward.
   * @param interprocedural Whether interprocedural edges (function call/return) should be followed. 
   * @return The highest node id encountered.
   */
  public static int dfs(CFANode start, Set<CFANode> seen, boolean reverse, boolean interprocedural) {
    int maxNodeId = -1; 

    Deque<CFANode> toProcess = new ArrayDeque<CFANode>();
    toProcess.push(start);
    while (!toProcess.isEmpty()) {
      CFANode n = toProcess.pop();
      maxNodeId = Math.max(maxNodeId, n.getNodeNumber());
      seen.add(n);
      if (reverse) {
        for (int i = 0; i < n.getNumEnteringEdges(); ++i) {
          CFAEdge e = n.getEnteringEdge(i);
          if (!interprocedural && (e instanceof FunctionCallEdge || e instanceof FunctionReturnEdge)) {
            continue;
          }
          
          CFANode s = e.getPredecessor();
          if (!seen.contains(s)) {
            toProcess.push(s);
          }
        }
        if (n.getEnteringSummaryEdge() != null) {
          CFANode s = n.getEnteringSummaryEdge().getPredecessor();
          if (!seen.contains(s)) {
            toProcess.push(s);
          }
        }
      } else {
        for (int i = 0; i < n.getNumLeavingEdges(); ++i) {
          CFAEdge e = n.getLeavingEdge(i);
          if (!interprocedural && (e instanceof FunctionCallEdge || e instanceof FunctionReturnEdge)) {
            continue;
          }

          CFANode s = e.getSuccessor();
          if (!seen.contains(s)) {
            toProcess.push(s);
          }
        }
        if (n.getLeavingSummaryEdge() != null) {
          CFANode s = n.getLeavingSummaryEdge().getSuccessor();
          if (!seen.contains(s)) {
            toProcess.push(s);
          }
        }
      }
    }
    return maxNodeId;
  }
 
  /**
   * A predicate that can be used to filter out nodes that are marked as loop start nodes.
   */
  public static Predicate<CFANode> FILTER_LOOP_HEADS = new Predicate<CFANode>() {
    @Override
    public boolean apply(CFANode pNode) {
      return pNode.isLoopStart();
    }
  };


  /**
   * Computes the transitive closure of the reachability relation on a set of
   * nodes.
   * 
   * The result is given as a two-dimensional array, where
   * (result[i][j] == true) iff that the node with id j is reachable from the node with id i.
   * 
   * This analysis does not know about the special meaning of function calls/exits,
   * so if there exist such edges, the analysis may be imprecise because it does
   * not keep track of the callstack.
   * 
   * @param allNodes The set of all nodes to consider.
   * @param max The highest node id of all nodes in allNodes.
   * @return A two-dimensional array with the transitive closure.
   */
  public static boolean[][] transitiveClosure(Set<CFANode> allNodes, int max) {
    boolean[][] transitiveClosure = new boolean[max+1][max+1];
    // all fields are initialized to 'false' by Java

    // transitiveClosure[i][j] means that j is reachable from i (j is a successor of i)
    
    // initialize for all direct edges
    for (CFANode currentNode : allNodes) {
      final int i = currentNode.getNodeNumber();
      final boolean[] transitiveClosureI = transitiveClosure[i];

      for (int j = 0; j < currentNode.getNumLeavingEdges(); ++j) {
        CFAEdge e = currentNode.getLeavingEdge(j);
        transitiveClosureI[e.getSuccessor().getNodeNumber()] = true;
      }
      
      CFAEdge e = currentNode.getLeavingSummaryEdge();
      if (e != null) {
        transitiveClosureI[e.getSuccessor().getNodeNumber()] = true;
      }
    }
    
    // (Floyd-)Warshall algorithm for transitive closure
    for (int k = 0; k <= max; k++) {
      for (int i = 0; i <= max; i++) {
        final boolean[] transitiveClosureI =  transitiveClosure[i];
        
        for (int j = 0; j <= max; j++) {
//        transitiveClosure[i][j] = transitiveClosure[i][j] || (transitiveClosure[i][k] && transitiveClosure[k][j]); 

          // optimization:
          transitiveClosureI[j]   = transitiveClosureI[j]   || (transitiveClosureI[k]   && transitiveClosure[k][j]); 
        }
      }
    }
    return transitiveClosure;
  }
  
  /**
   * Find all nodes that belong to the same loop as a given node.
   * @param node A node of a loop.
   * @return All nodes of the same loop
   */
  public static Sets.SetView<CFANode> findLoopNodes(CFANode node) {
    return Sets.intersection(transitiveSuccessors(node, false), transitivePredecessors(node, false));
  }
  
  /**
   * Creates two mappings from all loop-entry and loop-exit edges respectively
   * to the head of the loop.
   * 
   * The analysis is purely intraprocedural, so function call/return edges
   * that leave or re-enter loops will always be considered as loop entry or exit edges.
   * 
   * Does not work with nested loops!
   * 
   * @param allNodes The set of all nodes of the CFA.
   * @return Two mappings from loop-entry edges to the head of the loop and from loop-exit edges to the head of the loop.
   */
  public static Pair<Map<CFAEdge, CFANode>, Map<CFAEdge, CFANode>> allLoopEntryExitEdges(Set<CFANode> allNodes) {
    Map<CFAEdge, CFANode> loopEntryEdges = new HashMap<CFAEdge, CFANode>();
    Map<CFAEdge, CFANode> loopExitEdges = new HashMap<CFAEdge, CFANode>();

    for (CFANode loopHeadNode : filter(allNodes, FILTER_LOOP_HEADS)) {
      Collection<CFANode> loopNodes = findLoopNodes(loopHeadNode);
      for (CFANode loopNode : loopNodes) {
        
        { // entry edges
          for (int i = 0; i < loopNode.getNumEnteringEdges(); i++) {
            CFAEdge e = loopNode.getEnteringEdge(i);
            
            if (!loopNodes.contains(e.getPredecessor())) {
              CFANode old = loopEntryEdges.put(e, loopHeadNode);
              
              checkState(old == null, "Edge enters two loops!");
            }
          }
          
          CFAEdge e = loopNode.getEnteringSummaryEdge();
          if (e != null && !loopNodes.contains(e.getPredecessor())) {
            CFANode old = loopEntryEdges.put(e, loopHeadNode);
            
            checkState(old == null, "Edge enters two loops!");
          }
        }
        
        { // exit edges
          for (int i = 0; i < loopNode.getNumLeavingEdges(); i++) {
            CFAEdge e = loopNode.getLeavingEdge(i);
            
            if (!loopNodes.contains(e.getSuccessor())) {
              CFANode old = loopExitEdges.put(e, loopHeadNode);
              
              checkState(old == null, "Edge exits two loops!");
            }
          }
          
          CFAEdge e = loopNode.getLeavingSummaryEdge();
          if (e != null && !loopNodes.contains(e.getSuccessor())) {
            CFANode old = loopExitEdges.put(e, loopHeadNode);
            
            checkState(old == null, "Edge exits two loops!");
          }
        }
      }
    }
    return Pair.of(loopEntryEdges, loopExitEdges);
  }
  
  // wrapper class for Set<CFANode> because Java arrays don't like generics
  private static class Edge {
    private final Set<CFANode> nodes = new HashSet<CFANode>(1);
    
    private void add(Edge n) {
      nodes.addAll(n.nodes);
    }
    
    private void add(CFANode n) {
      nodes.add(n);
    }
    
    private Set<CFANode> asNodeSet() {
      return nodes;
    }
  }
  
  private static class Loop {
    
    // loopHeads is a sub-set of nodes such that all infinite paths through
    // the set nodes will pass through at least one node in loopHeads infinitively often
    // i.e. you will have to pass through at least one loop head in every iteration
    private ImmutableSet<CFANode> loopHeads;
    
    private ImmutableSortedSet<CFANode> nodes;
    
    // the following sets are computed lazily by calling {@link #computeSets()}
    private ImmutableSet<CFAEdge> innerLoopEdges;
    private ImmutableSet<CFAEdge> incomingEdges;
    private ImmutableSet<CFAEdge> outgoingEdges;
    
    public Loop(CFANode loopHead, Set<CFANode> pNodes) {
      loopHeads = ImmutableSet.of(loopHead);
      nodes = ImmutableSortedSet.<CFANode>naturalOrder()
                                .addAll(pNodes)
                                .add(loopHead)
                                .build();
    }
    
    private void computeSets() {
      if (innerLoopEdges != null) {
        assert incomingEdges != null;
        assert outgoingEdges != null;
      }
      
      Set<CFAEdge> incomingEdges = new HashSet<CFAEdge>();
      Set<CFAEdge> outgoingEdges = new HashSet<CFAEdge>();
      
      for (CFANode n : nodes) {
        for (int i = 0; i < n.getNumEnteringEdges(); i++) {
          incomingEdges.add(n.getEnteringEdge(i));
        }
        for (int i = 0; i < n.getNumLeavingEdges(); i++) {
          outgoingEdges.add(n.getLeavingEdge(i));
        }
      }
      
      innerLoopEdges = Sets.intersection(incomingEdges, outgoingEdges).immutableCopy();
      incomingEdges.removeAll(innerLoopEdges);
      outgoingEdges.removeAll(innerLoopEdges);
      
      assert !incomingEdges.isEmpty() : "Unreachable loop?";
      
      this.incomingEdges = ImmutableSet.copyOf(incomingEdges);
      this.outgoingEdges = ImmutableSet.copyOf(outgoingEdges);
    }
    
    void addNodes(Loop l) {
      nodes = ImmutableSortedSet.<CFANode>naturalOrder()
                                .addAll(nodes)
                                .addAll(l.nodes)
                                .build();
      
      innerLoopEdges = null;
      incomingEdges = null;
      outgoingEdges = null;
    }
    
    void mergeWith(Loop l) {
      loopHeads = Sets.union(loopHeads, l.loopHeads).immutableCopy();
      addNodes(l);
    }
   
    public boolean intersectsWith(Loop l) {
      return !Sets.intersection(nodes, l.nodes).isEmpty();
    }
    
    /**
     * Check if this loop is an outer loop of another, given one.
     */
    public boolean isOuterLoopOf(Loop other) {
      this.computeSets();
      other.computeSets();
      
      return this.innerLoopEdges.containsAll(other.incomingEdges)
          && this.innerLoopEdges.containsAll(other.outgoingEdges);
    }
    
    @Override
    public String toString() {
      computeSets();
      return "Loop with heads " + loopHeads + "\n"
           + "  incoming: " + incomingEdges + "\n"
           + "  outgoing: " + outgoingEdges + "\n"
           + "  nodes:    " + nodes;
    }
  }
  
  public static Collection<Loop> findLoops(CFAFunctionDefinitionNode startNode) {
    SortedSet<CFANode> nodes = new TreeSet<CFANode>();
    dfs(startNode, nodes, false, false);
    
    final int min = nodes.first().getNodeNumber();
    final int max = nodes.last().getNodeNumber();
    final int size = max + 1 - min;
    
    // all nodes of the graph
    // Fields may be null, iff there is no node with this number.
    // forall i : nodes[i].getNodeNumber() == i + min
    final CFANode[] nodesArray = new CFANode[size];
    
    // all edges of the graph
    // Iff there is an edge from nodes[i] to nodes[j], edges[i][j] is not null.
    // The set edges[i][j].nodes contains all nodes that were eliminated and merged into this edge. 
    final Edge[][] edges =  new Edge[size][size];
    
    // FIRST step: initialize arrays
    for (CFANode n : nodes) {
      int i = n.getNodeNumber() - min;
      assert nodesArray[i] == null;
      nodesArray[i] = n;

      for (int e = 0; e < n.getNumLeavingEdges(); e++) {
        CFAEdge edge = n.getLeavingEdge(e);
        CFANode succ = edge.getSuccessor();
        int j = succ.getNodeNumber() - min;
        edges[i][j] = new Edge();
      }
    }

    // SECOND step: simplify graph and identify loops
    List<Loop> loops = new ArrayList<Loop>();
    boolean changed;
    do {
      // first try without the "reverse merge" strategy
      // this strategy may eliminate real loop heads too early so that the
      // algorithm would propose another node of the loop has loop head
      // (which is counter-intuitive to the user)
      changed = identifyLoops(false, nodes, min, nodesArray, edges, loops);
      
      if (!changed && !nodes.isEmpty()) {
        // but if we have to, try and use this strategy
        changed = identifyLoops(true, nodes, min, nodesArray, edges, loops);
      }
      
    } while (changed && !nodes.isEmpty()); // stop if nothing has changed or nodes is empty

    
    // check that the complete graph has collapsed
    if (!nodes.isEmpty()) {
      throw new RuntimeException("Code structure is too complex, could not detect all loops!");
    }
   
    // THIRD step:
    // check all pairs of loops if one is an inner loop of the other
    // the check is symmetric, so we need to check only (i1, i2) with i1 < i2
    
    NavigableSet<Integer> toRemove = new TreeSet<Integer>();
    for (int i1 = 0; i1 < loops.size(); i1++) {
      Loop l1 = loops.get(i1);
      
      for (int i2 = i1+1; i2 < loops.size(); i2++) {
        Loop l2 = loops.get(i2);
        
        if (!l1.intersectsWith(l2)) {
          // loops have nothing in common
          continue;
        }
        
        if (l1.isOuterLoopOf(l2)) {
          
          // l2 is an inner loop
          // add it's nodes to l1
          l1.addNodes(l2);
          
        } else if (l2.isOuterLoopOf(l1)) {

          // l1 is an inner loop
          // add it's nodes to l2
          l2.addNodes(l1);
          
        } else {
          // strange goto loop, merge the two together

          l1.mergeWith(l2);
          toRemove.add(i2);
        }
      }
    }

    for (int i : toRemove.descendingSet()) { // need to iterate in reverse order!
      loops.remove(i);
    }
 
    return loops;
  }

  private static boolean identifyLoops(boolean reverseMerge, SortedSet<CFANode> nodes, final int offset,
      final CFANode[] nodesArray, final Edge[][] edges, List<Loop> loops) {
    
    final int size = edges.length;

    boolean changed = false;
      
      // merge nodes with their neighbors, if possible
      Iterator<CFANode> it = nodes.iterator();
      while (it.hasNext()) {
        final CFANode currentNode = it.next();
        final int current = currentNode.getNodeNumber() - offset;

        // find edges of current
        final int predecessor = findSingleIncomingEdgeOfNode(current, edges);
        final int successor   = findSingleOutgoingEdgeOfNode(current, edges);
        
        if ((predecessor == -1) && (successor == -1)) {
          // no edges, eliminate node
          it.remove(); // delete currentNode
        
        } else if ((predecessor == -1) && (successor > -1)) {
          // no incoming edges, one outgoing edge
          final int successor2 = findSingleOutgoingEdgeOfNode(successor, edges);
          if (successor2 == -1) {
            // the current node is a source that is only connected with a sink
            // we can remove it
            edges[current][successor] = null;
            it.remove(); // delete currentNode
          }

        } else if ((successor == -1) && (predecessor > -1)) {
          // one incoming edge, no outgoing edges
          final int predecessor2 = findSingleIncomingEdgeOfNode(predecessor, edges);
          if (predecessor2 == -1) {
            // the current node is a sink that is only connected with a source
            // we can remove it
            edges[predecessor][current] =  null;
            it.remove(); // delete currentNode
          }
          
        } else if ((predecessor > -1) && (successor != -1)) {
          // current has a single incoming edge from predecessor and is no sink, eliminate current
          changed = true;
          
          // copy all outgoing edges (current,j) to (predecessor,j)
          for (int j = 0; j < size; j++) {
            if (edges[current][j] != null) {
              // combine three edges (predecessor,current) (current,j) and (predecessor,j)
              // into a single edge (predecessor,j)
              Edge targetEdge = getEdge(predecessor, j, edges);
              targetEdge.add(edges[predecessor][current]);
              targetEdge.add(edges[current][j]);
              targetEdge.add(currentNode);
              edges[current][j] = null;
            }
          }
          
          // delete from graph
          edges[predecessor][current] = null;
          it.remove(); // delete currentNode

          // now predecessor node might have gained a self-edge
          if (edges[predecessor][predecessor] != null) {
            CFANode pred = nodesArray[predecessor];
            handleLoop(pred, predecessor, edges, loops);
          }
        
          
        } else if (reverseMerge && (successor > -1) && (predecessor != -1)) {
          // current has a single outgoing edge to successor and is no source, eliminate current
          changed = true;
          
          // copy all incoming edges (j,current) to (j,successor)
          for (int j = 0; j < size; j++) {
            if (edges[j][current] != null) {
              // combine three edges (j,current) (current,successor) and (j,successor)
              // into a single edge (j,successor)
              Edge targetEdge = getEdge(j, successor, edges);
              targetEdge.add(edges[j][current]);
              targetEdge.add(edges[current][successor]);
              targetEdge.add(currentNode);
              edges[j][current] = null;
            }
          }
                    
          // delete from graph
          edges[current][successor] = null;
          it.remove(); // delete currentNode

          // now successor node might have gained a self-edge
          if (edges[successor][successor] != null) {
            CFANode succ = nodesArray[successor];
            handleLoop(succ, successor, edges, loops);
          }
        }
      }
      
      return changed;
  }

  // get edge from edges array, ensuring that it is added if it does not exist yet
  private static Edge getEdge(int i, int j, Edge[][] edges) {
    Edge result = edges[i][j];
    if (edges[i][j] == null) {
      result = new Edge();
      edges[i][j] = result;
    }
    return result;
  }
  
  // create a loop from a node with a self-edge
  private static void handleLoop(final CFANode loopHead, int loopHeadIndex,
      final Edge[][] edges, Collection<Loop> loops) {
    assert loopHead != null;
    
    // store loop
    Loop loop = new Loop(loopHead, edges[loopHeadIndex][loopHeadIndex].asNodeSet());
    loops.add(loop);
    
    // remove this loop from the graph
    edges[loopHeadIndex][loopHeadIndex] = null;
  }

  // find index of single predecessor of node i
  // if there is no successor, -1 is returned
  // if there are several successor, -2 is returned
  private static int findSingleIncomingEdgeOfNode(int i, Edge[][] edges) {
    final int size = edges.length;
    
    int predecessor = -1;
    for (int j = 0; j < size; j++) {
      if (edges[j][i] != null) {
        // i has incoming edge from j
        
        if (predecessor > -1) {
          // not the only incoming edge
          return -2;
        } else {
          predecessor = j;
        }
      }
    }
    return predecessor;
  }
  
  // find index of single successor of node i
  // if there is no successor, -1 is returned
  // if there are several successors, -2 is returned
  private static int findSingleOutgoingEdgeOfNode(int i, Edge[][] edges) {
    final int size = edges.length;
    
    int successor = -1;
    for (int j = 0; j < size; j++) {
      if (edges[i][j] != null) {
        // i has outgoing edge to j
        
        if (successor > -1) {
          // not the only outgoing edge
          return -2;
        } else {
          successor = j;
        }
      }
    }
    return successor;
  }
}
