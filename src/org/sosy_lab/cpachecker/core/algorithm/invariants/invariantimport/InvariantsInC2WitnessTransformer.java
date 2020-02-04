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

import com.google.common.collect.Multimap;
import java.io.File;
import java.io.IOException;
import java.time.ZoneId;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.time.temporal.ChronoUnit;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.cfa.model.AssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.automaton.AutomatonGraphmlCommon;
import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import scala.NotImplementedError;

public class InvariantsInC2WitnessTransformer {

  private static final String KEY_STRING = "key";
  private static final String DATA_STRING = "data";
  private static final String NAME_OF_TOOL = "CoInVerify";

  private static final String TRUE = "true";
  private static final String FALSE = "false";
  public static final String MAIN_FUNCTION = "main";
  private int nodeNameCounter;

  public InvariantsInC2WitnessTransformer() {
    super();
    nodeNameCounter = 0;
  }

  /**
   *
   * @param mapping a multimap, where the first parameter is the line number, the second one a
   *        string of the source code and the third a string with the c invariant
   * @param fileToStoreInvTo the file, where the witness should be stored to
   * @param pCfa TODO log
   * @param pSpecification TODO log
   * @param sourceFile TODO log
   * @param pLogger TODO log
   * @throws ParserConfigurationException TODO log
   * @throws IOException TODO log
   * @throws CPAException TODO log
   * @throws TransformerException TODO log
   *
   *
   */
  public void transform(
      Multimap<Integer, Pair<String, String>> mapping,
      File fileToStoreInvTo,
      CFA pCfa,
      Specification pSpecification,
      File sourceFile,
      LogManager pLogger)
      throws ParserConfigurationException, IOException, CPAException, TransformerException {
    // Next, create an xml file and put the header to it

    DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
    DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
    Document doc = docBuilder.newDocument();
    Element graphml = getDocWithHeader(doc);

    // append child elements to root element
    // Extract the information about the source code file the invariants belong to:
    Element graph = addPredefinedGraphElements(pCfa, pSpecification, sourceFile, doc, graphml);

    // Than, find the necessary nodes (start node and node to enter the main function to get to
    // the invariant
    Element globalEntryElement =
        createNodeWithDataNode(graph, doc, getNewNameForNode(), "entry", "true");

    int lineNumberOfMain = -1;

    Map<Integer, Set<CFAEdge>> lineToEdgesOfMain = new HashMap<>();
    lineNumberOfMain =
        getMappingLinesToEdgesOfFunction(pCfa, lineNumberOfMain, lineToEdgesOfMain, MAIN_FUNCTION);

    CFANode mainEntryNode = pCfa.getAllFunctions().get(MAIN_FUNCTION);
    if (mainEntryNode == null || lineNumberOfMain == -1) {
      throw new CPAException(
          "Could not find main function, hence aborted computation of invariants");
    }

    Element mainEntryElement = createBlankNode(graph, doc, getNewNameForNode());
    Element toEntry =
        getEnterFunctionEdge(doc, globalEntryElement, mainEntryElement, "main", lineNumberOfMain);
    graph.appendChild(toEntry);
    // afterwards, find the node where the invariants belong to. If more than one, abort
    // Otherwise, add a path from entering node f main to that node

    // Get the edge containing the line number of the invariant, the starting node of the edge is
    // the desired one

    // FIXME: Since we only want to evaluate the cases where the invariant is in fact helpfull,
    // meaning that at least one invariant is non-trivial and hence unequal to "true/false", we can
    // save computation time (for the first evaluation and abort, if only non-trivial invariants are
    // generated:
    boolean nonTrivialInvariantGenerated = false;
    for (Entry<Integer, Pair<String, String>> inv : mapping.entries()) {

      if (inv.getValue().getSecond().strip().equalsIgnoreCase(TRUE)
          || inv.getValue().getSecond().strip().equalsIgnoreCase(FALSE)) {
        // No need to add true or false
        continue;
      }

      int lineNumber = inv.getKey();
      if (!lineToEdgesOfMain.containsKey(lineNumber)) {
        pLogger.log(
            Level.FINE,
            "Cannot parse the invariant, because no matching line number was found: "
                + inv.toString());
        continue;
      }
      nonTrivialInvariantGenerated = true;
      // Determine the minimal Start and maximal end offset for a given line (if there are more
      // statements present

      computeAllEdgesForLineNumber(
          pCfa,
          doc,
          graph,
          lineToEdgesOfMain,
          mainEntryElement,
          inv,
          lineNumber);

    }

    // write the content into xml file
    TransformerFactory transformerFactory = TransformerFactory.newInstance();

    Transformer transformer = transformerFactory.newTransformer();
    transformer.setOutputProperty(OutputKeys.INDENT, "yes");
    transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");
    DOMSource source = new DOMSource(doc);

    StreamResult result = new StreamResult(fileToStoreInvTo);
    transformer.transform(source, result);
    if (!nonTrivialInvariantGenerated) {
      throw new IllegalStateException(
          "The invariant generation via [SEAHORN] does only generate trivial invariants, hence abort the computation!");
    }

  }

  private void computeAllEdgesForLineNumber(
      CFA pCfa,
      Document doc,
      Element graph,
      Map<Integer, Set<CFAEdge>> lineToEdgesOfMain,
      Element mainEntryElement,
      Entry<Integer, Pair<String, String>> inv,
      int lineNumber) {
    for (CFAEdge e : lineToEdgesOfMain.get(lineNumber)) {
      int minStartOffset = Integer.MAX_VALUE;
      int maxEndOffset = Integer.MIN_VALUE;

      Set<FileLocation> fileLocs =
          AutomatonGraphmlCommon.getFileLocationsFromCfaEdge(e, pCfa.getMainFunction());
      if (fileLocs.isEmpty()) {
        if (e.getFileLocation() != null && e instanceof BlankEdge) {
          // Determine the predrecesor location (only if unique and add an edge in the witness for
          // that location
          // (Since the location is a blank one and hence associated to the previous spot
          if (e.getPredecessor().getNumEnteringEdges() == 1) {
            int prevLine = e.getPredecessor().getEnteringEdge(0).getLineNumber();
            computeOneEdgeForLineNumber(
                pCfa,
                doc,
                graph,
                lineToEdgesOfMain,
                mainEntryElement,
                inv,
                prevLine,
                e.getSuccessor().isLoopStart());
          }
        }
      } else {

        for (FileLocation loc : fileLocs) {
          // TODO: Add handling for edges with different starting and finishing line
          minStartOffset = Math.min(minStartOffset, loc.getNodeOffset());
          maxEndOffset = Math.max(maxEndOffset, loc.getNodeOffset() + loc.getNodeLength());
        }

        Pair<String, String> sourceAndInv = inv.getValue();

        Element invElement =
            createNodeWithInvariant(doc, sourceAndInv.getSecond(), getNewNameForNode());
        graph.appendChild(invElement);
        Optional<Boolean> isControlEdge = Optional.empty();

        // Check if a controledge (assume edge) is present
        if (e instanceof AssumeEdge) {
          isControlEdge = Optional.of(((AssumeEdge) e).getTruthAssumption());
        }

        // Check if the flag "enterLoopHead" is true, meaning that the edge is one into a loop
        // head
        // Create a edge in the witness from mainEntryElement to the invElement node
        Element edge =
            getEdge(
                doc,
                mainEntryElement,
                invElement,
                e.getSuccessor().isLoopStart(),
                lineNumber,
                lineNumber,
                minStartOffset,
                maxEndOffset,
                isControlEdge);
        graph.appendChild(edge);
      }
    }
  }

  private void computeOneEdgeForLineNumber(
      CFA pCfa,
      Document doc,
      Element graph,
      Map<Integer, Set<CFAEdge>> lineToEdgesOfMain,
      Element mainEntryElement,
      Entry<Integer, Pair<String, String>> inv,
      int lineNumber,
      boolean isLoopStart) {

    int minStartOffset = Integer.MAX_VALUE;
    int maxEndOffset = Integer.MIN_VALUE;
    for (CFAEdge e : lineToEdgesOfMain.get(lineNumber)) {

      Set<FileLocation> fileLocs =
          AutomatonGraphmlCommon.getFileLocationsFromCfaEdge(e, pCfa.getMainFunction());
      if (!fileLocs.isEmpty()) {
        for (FileLocation loc : fileLocs) {
          // TODO: Add handling for edges with different starting and finishing line
          minStartOffset = Math.min(minStartOffset, loc.getNodeOffset());
          maxEndOffset = Math.max(maxEndOffset, loc.getNodeOffset() + loc.getNodeLength());
        }
      }

    }
    Pair<String, String> sourceAndInv = inv.getValue();
    Element invElement =
        createNodeWithInvariant(doc, sourceAndInv.getSecond(), getNewNameForNode());
    graph.appendChild(invElement);

    // Check if the flag "enterLoopHead" is true, meaning that the edge is one into a loop
    // head
    // Create a edge in the witness from mainEntryElement to the invElement node
    Element edge =
        getEdge(
            doc,
            mainEntryElement,
            invElement,
            isLoopStart,
            lineNumber,
            lineNumber,
            minStartOffset,
            maxEndOffset,
            Optional.empty());
    graph.appendChild(edge);

  }

  private Element addPredefinedGraphElements(
      CFA pCfa,
      Specification pSpecification,
      File sourceFile,
      Document doc,
      Element graphml)
      throws IOException {
    Element graph = doc.createElement("graph");
    graphml.appendChild(graph);
    graph.setAttributeNode(createAttrForDoc(doc, "edgedefault", "directed"));

    graph = createAndAppandDataNode(graph, doc, "witness-type", "correctness_witness");
    graph = createAndAppandDataNode(graph, doc, "sourcecodelang", "C");
    graph = createAndAppandDataNode(graph, doc, "producer", NAME_OF_TOOL);
    graph = createAndAppandDataNode(graph, doc, "specification", getSpecification(pSpecification));
    graph = createAndAppandDataNode(graph, doc, "programfile", sourceFile.getAbsolutePath());
    graph = createAndAppandDataNode(graph, doc, "programhash", getHash(sourceFile));
    graph =
        createAndAppandDataNode(
            graph,
            doc,
            "architecture",
            pCfa.getMachineModel().name().contains("32") ? "32bit" : "64bit");
    graph =
        createAndAppandDataNode(
            graph,
            doc,
            "creationtime",
            ZonedDateTime.now(ZoneId.of("Europe/Paris"))
                .truncatedTo(ChronoUnit.MINUTES)
                .format(DateTimeFormatter.ISO_OFFSET_DATE_TIME));
    return graph;
  }

  private String getSpecification(Specification pSpecification) {
    StringBuilder builder = new StringBuilder();
    pSpecification.getPathToSpecificationAutomata()
        .values()
        .forEach(a -> builder.append(a.toString()));
    return builder.toString();
  }

  private Element getEdge(
      Document pDoc,
      Element pSource,
      Element pTarget,
      boolean pIsLoopStart,
      int pLineNumberStart,
      int pLineNumberEnd,
      int pStartOffset,
      int pEndOffset,
      Optional<Boolean> cfgAssumeEdge) {
    Element edge = pDoc.createElement("edge");
    edge.setAttributeNode(createAttrForDoc(pDoc, "source", pSource.getAttribute("id")));
    edge.setAttributeNode(createAttrForDoc(pDoc, "target", pTarget.getAttribute("id")));

    if (pIsLoopStart) {
      edge = createAndAppandDataNode(edge, pDoc, "enterLoopHead", "true");
    }
    if (cfgAssumeEdge.isPresent()) {
      if (cfgAssumeEdge.get()) {
        // Create <data key="control">condition-true</data>
        edge = createAndAppandDataNode(edge, pDoc, "control", "condition-true");
      } else {
        // Create <data key="control">condition-false</data>
        edge = createAndAppandDataNode(edge, pDoc, "control", "condition-false");
      }
    }
    edge = createAndAppandDataNode(edge, pDoc, "startline", String.valueOf(pLineNumberStart));
    edge = createAndAppandDataNode(edge, pDoc, "endline", String.valueOf(pLineNumberEnd));
    edge = createAndAppandDataNode(edge, pDoc, "startoffset", String.valueOf(pStartOffset));
    edge = createAndAppandDataNode(edge, pDoc, "endoffset", String.valueOf(pEndOffset));
    return edge;
  }

  private Element getEnterFunctionEdge(
      Document pDoc,
      Element pSource,
      Element pTarget,
      String nameOfEnterFunction,
      int pLineNumberOfMain) {

    Element edge = pDoc.createElement("edge");
    edge.setAttributeNode(createAttrForDoc(pDoc, "source", pSource.getAttribute("id")));
    edge.setAttributeNode(createAttrForDoc(pDoc, "target", pTarget.getAttribute("id")));

    edge = createAndAppandDataNode(edge, pDoc, "startline", String.valueOf(pLineNumberOfMain));
    edge = createAndAppandDataNode(edge, pDoc, "endline", String.valueOf(pLineNumberOfMain));

    edge = createAndAppandDataNode(edge, pDoc, "enterFunction", nameOfEnterFunction);
    return edge;
  }

  private Element createNodeWithInvariant(Document pDoc, String pInv, String nameOfNode) {
    Element invNode = pDoc.createElement("node");
    invNode.setAttributeNode(createAttrForDoc(pDoc, "id", nameOfNode));

    Element scope = pDoc.createElement(DATA_STRING);
    scope.setAttributeNode(createAttrForDoc(pDoc, KEY_STRING, "invariant.scope"));
    scope.appendChild(pDoc.createTextNode("main"));
    invNode.appendChild(scope);
    Element iinvDataNode = pDoc.createElement(DATA_STRING);
    iinvDataNode.setAttributeNode(createAttrForDoc(pDoc, KEY_STRING, "invariant"));
    iinvDataNode.setTextContent(pInv);
    invNode.appendChild(iinvDataNode);
    return invNode;
  }

  private Element createBlankNode(Element pGraph, Document pDoc, String nameOfNode) {
    Element node = pDoc.createElement("node");
    node.setAttributeNode(createAttrForDoc(pDoc, "id", nameOfNode));
    pGraph.appendChild(node);
    return node;
  }

  private Element createNodeWithDataNode(
      Element pGraph,
      Document pDoc,
      String nameOfNode,
      String key,
      String value) {
    Element node = pDoc.createElement("node");
    node.setAttributeNode(createAttrForDoc(pDoc, "id", nameOfNode));
    node = createAndAppandDataNode(node, pDoc, key, value);
    pGraph.appendChild(node);
    return node;
  }

  private Element createAndAppandDataNode(
      Element pGraph,
      Document pDoc,
      String pStringpKeyValue,
      String textValue) {

    Element data = pDoc.createElement(DATA_STRING);
    data.setAttributeNode(createAttrForDoc(pDoc, KEY_STRING, pStringpKeyValue));
    data.appendChild(pDoc.createTextNode(textValue));
    pGraph.appendChild(data);
    return pGraph;
  }

  private Element getDocWithHeader(Document doc) {

    Element graphml = doc.createElement("graphml");
    doc.appendChild(graphml);

    graphml.setAttributeNode(
        createAttrForDoc(doc, "xmlns", "\"http://graphml.graphdrawing.org/xmlns\""));
    graphml.setAttributeNode(
        createAttrForDoc(doc, "xmlns:xsi", "\"http://www.w3.org/2001/XMLSchema-instance\""));

    graphml.appendChild(
        getDefaultNode(doc, "\"invariant\"", "\"string\"", "\"node\"", "\"invariant\""));
    graphml.appendChild(
        getDefaultNode(
            doc,
            "\"invariant.scope\"",
            "\"string\"",
            "\"node\"",
            "\"invariant.scope\""));

    graphml.appendChild(
        getDefaultNode(
            doc,
            "\"sourcecodeLanguage\"",
            "\"string\" ",
            "\"graph\" ",
            "\"sourcecodelang\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"programFile\"", "\"string\" ", "\"graph\" ", "\"programfile\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"programHash\"", "\"string\" ", "\"graph\" ", "\"programhash\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"specification\"", "\"string\" ", "\"graph\" ", "\"specification\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"architecture\"", "\"string\" ", "\"graph\" ", "\"architecture\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"producer\"", "\"string\" ", "\"graph\" ", "\"producer\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"creationTime\"", "\"string\" ", "\"graph\" ", "\"creationtime\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"startline\"", "\"int\" ", "\"edge\" ", "\"startline\""));
    graphml.appendChild(getDefaultNode(doc, "\"endline\"", "\"int\" ", "\"edge\" ", "\"endline\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"startoffset\"", "\"int\" ", "\"edge\" ", "\"startoffset\""));
    graphml
        .appendChild(getDefaultNode(doc, "\"endoffset\"", "\"int\"", "\"edge\"", "\"endoffset\""));
    graphml
        .appendChild(getDefaultNode(doc, "\"control\"", "\"string\" ", "\"edge\" ", "\"control\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"enterFunction\"", "\"string\" ", "\"edge\" ", "\"enterFunction\""));
    graphml.appendChild(
        getDefaultNode(
            doc,
            "\"returnFromFunction\"",
            "\"string\" ",
            "\"edge\" ",
            "\"returnFrom\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"witness-type\"", "\"string\" ", "\"graph\" ", "\"witness-type\""));
    graphml.appendChild(
        getDefaultNode(
            doc,
            "\"inputWitnessHash\"",
            "\"string\" ",
            "\"graph\" ",
            "\"inputwitnesshash\""));
    graphml.appendChild(
        getDefaultNode(doc, "\"originFileName\"", "\"string\"", "\"edge\"", "\"originfile\""));

    graphml.appendChild(
        getDefaultNode(doc, "\"isEntryNode\"", "\"boolean\"", "\"node\"", "\"entry\"", "false"));
    graphml.appendChild(
        getDefaultNode(
            doc,
            "\"enterLoopHead\"",
            "\"boolean\"",
            "\"edge\"",
            "\"enterLoopHead\"",
            "false"));
    Element scope = doc.createElement(DATA_STRING);
    scope.setAttributeNode(createAttrForDoc(doc, KEY_STRING, "invariant.scope"));
    scope.appendChild(doc.createTextNode("main"));

    return graphml;
  }

  private Attr createAttrForDoc(Document pDoc, String attrName, String value) {
    Attr newAttr = pDoc.createAttribute(attrName);
    newAttr.setNodeValue(value);
    return newAttr;
  }

  private Node
      getDefaultNode(Document doc, String attrName, String attrType, String forStr, String id) {
    Element node = doc.createElement(KEY_STRING);
    node.setAttributeNode(createAttrForDoc(doc, "attr.name", attrName));
    node.setAttributeNode(createAttrForDoc(doc, "attr.type", attrType));
    node.setAttributeNode(createAttrForDoc(doc, "for", forStr));
    node.setAttributeNode(createAttrForDoc(doc, "id", id));
    return node;
  }

  private Node getDefaultNode(
      Document doc,
      String attrName,
      String attrType,
      String forStr,
      String id,
      String defaultVal) {
    Element node = doc.createElement(KEY_STRING);
    node.setAttributeNode(createAttrForDoc(doc, "attr.name", attrName));
    node.setAttributeNode(createAttrForDoc(doc, "attr.type", attrType));
    node.setAttributeNode(createAttrForDoc(doc, "for", forStr));
    node.setAttributeNode(createAttrForDoc(doc, "id", id));

    Node child = doc.createElement("default");
    child.setTextContent(defaultVal);
    node.appendChild(child);
    return node;
  }

  private String getHash(File pSourceFile) throws IOException {

    String sha256hex = AutomatonGraphmlCommon.computeHash(pSourceFile.toPath()).toLowerCase();
    return sha256hex;
  }

  /**
   *
   * Computes for each source code line the edges associated to that line
   *
   * @param pCfa the cfa to search in
   * @param lineNumberOfMain the line number of the main function
   * @param lineToEdgesOfMain the map to add elements to
   * @param pNameOfFunction the name of the function to considere
   * @return the extended map
   */
  private int getMappingLinesToEdgesOfFunction(
      CFA pCfa,
      int lineNumberOfMain,
      Map<Integer, Set<CFAEdge>> lineToEdgesOfMain,
      String pNameOfFunction) {
    if (!pNameOfFunction.equals(MAIN_FUNCTION)) {
      throw new NotImplementedError("Only main methods are supported");
    }
    for (CFANode n : pCfa.getAllNodes()) {
      if (n.getFunctionName().equals(pNameOfFunction)) {
        for (int i = 0; i < n.getNumEnteringEdges(); i++) {
          CFAEdge enteringEdge = n.getEnteringEdge(i);
          if (lineToEdgesOfMain.containsKey(enteringEdge.getLineNumber())) {
            lineToEdgesOfMain.get(enteringEdge.getLineNumber()).add(enteringEdge);
          } else {
            HashSet<CFAEdge> edges = new HashSet<>();
            edges.add(enteringEdge);
            lineToEdgesOfMain.put(enteringEdge.getLineNumber(), edges);
          }

        }
      }
    }
    if (pCfa.getMainFunction().getNumLeavingEdges() > 1) {
      throw new IllegalStateException("Expecting only one call t main");
    } else {
      lineNumberOfMain = pCfa.getMainFunction().getLeavingEdge(0).getLineNumber();
    }

    return lineNumberOfMain;
  }

  private String getNewNameForNode() {
    nodeNameCounter = nodeNameCounter + 1;
    return "N" + nodeNameCounter;
  }

}
