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
package org.sosy_lab.cpachecker.util.invariantimport;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.ZoneId;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.time.temporal.ChronoUnit;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javax.annotation.Nullable;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.CandidateGenerator;
import org.sosy_lab.cpachecker.core.algorithm.bmc.StaticCandidateProvider;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.WitnessInvariantsExtractor;
import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

public class SeahornInvariantGenerator2 implements ExternalInvariantGenerator {
  private static final int OFFSET = 4;
  private static final String NAME_OF_TOOL = "NAME";
  private static final String MAIN_FUNCTION = "main";
  private static final String TEXT_ENTERING_EDGE = "Function start dummy edge";
  private static final String DEFAULT_VALUE = "NOT_AN_INVARIANT";

  @Override
  public CandidateGenerator generateInvariant(
      CFA pCfa,
      @Nullable List<CFANode> pTargetNodesToGenerateFor,
      Specification pSpecification,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      Configuration pConfig)
      throws CPAException {
    try {

      // Start Seahorn:
      List<Path> sourceFiles = pCfa.getFileNames();
      if (sourceFiles.size() != 1) {
        throw new CPAException("Can onyl handle CFAs, where one source file is contained");
      }
      File sourceFile = sourceFiles.get(0).toFile();
      Map<Pair<Integer, String>, String> genINvs = generateInvariantsAndLoad(sourceFiles.get(0));

      // Next, create an xml file and put the header to it

      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
      Document doc = docBuilder.newDocument();
      Element graphml = getDochWithHeader("", sourceFile, pCfa, doc);

      // Extract the information about the source code file the invarinas belong to:



      Element graph = doc.createElement("graph");
      graphml.appendChild(graph);
      graph.setAttributeNode(createAttrForDoc(doc, "edgedefault", "directed"));

      graph = createAndAppandDataNode(graph, doc, "witness-type", "correctness_witness");
      graph = createAndAppandDataNode(graph, doc, "witness-type", "correctness_witness");
      graph = createAndAppandDataNode(graph, doc, "sourcecodelang", "C");
      graph = createAndAppandDataNode(graph, doc, "producer", NAME_OF_TOOL);
      graph = createAndAppandDataNode(graph, doc, "specification", pSpecification.toString());
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

      // Than, find the neccessary nodes (start node and node to enter the main function to get to
      // the
      // invariant
      CFANode cfaEntry = pCfa.getMainFunction();
      Element globalEntryElement =
          createNodeWithDataNode(graph, doc, cfaEntry.toString(), "entry", "true");
      CFANode mainEntryNode = null;
      // find the dummy entering edge:
      for (CFANode n : pCfa.getAllNodes()) {
        if (n.getFunctionName().equals(MAIN_FUNCTION)) {
          for (int i = 0; i < n.getNumEnteringEdges(); i++) {
            if (n.getEnteringEdge(i) instanceof BlankEdge
                && n.getEnteringEdge(i).getDescription().equals(TEXT_ENTERING_EDGE)) {
              mainEntryNode = n;
              break;
            }
          }
        }
      }
      if (mainEntryNode == null) {
        throw new CPAException(
            "Could not find main function, hence aborted computation of invariants");
      }

      Element mainEntryElement = createBlankNode(graph, doc, mainEntryNode.toString());
      Element toEntry =
          getEnterFunctionEdge(
              doc,
              globalEntryElement,
              mainEntryElement,
              "main",
              mainEntryNode.getEnteringEdge(0).getFileLocation());
      graph.appendChild(toEntry);
      // afterwards, find the node where the invariants belong to. If more than one, abort
      // Otherwise, add a path from entering node f main to that node

      // Therefore, iterate over the set of all edges of the main function:
      Set<CFAEdge> edgesofMain = new HashSet<>();
      for (CFANode n : pCfa.getAllNodes()) {
        if (n.getFunctionName().equals(MAIN_FUNCTION)) {
          for (int i = 0; i < n.getNumEnteringEdges(); i++) {
            edgesofMain.add(n.getEnteringEdge(i));
          }
        }
      }

      // if an edge contains the line number of the invariant, the starting node of the edge is the
      // desired one
      for (CFAEdge e : edgesofMain) {
        // If the edge is from loop start 8hence an assume edge, extent the description to check by
        // adding
        String inv = "";
        if (!(inv =
            genINvs.getOrDefault(
                Pair.of(e.getFileLocation().getStartingLineNumber(), ""),
                DEFAULT_VALUE)).equals(DEFAULT_VALUE)) {
          CFANode startingNode = e.getPredecessor();
          Element invElement = createNodeWithInvariant(doc, inv, startingNode.toString());
          graph.appendChild(invElement);

          // Create a edge in the witness from mainEntryElement to the invElement node
          CFAEdge prevEdge = startingNode.getEnteringEdge(0);

          Element edge =
              getEdge(
                  doc,
                  mainEntryElement,
                  invElement,
                  startingNode.isLoopStart(),
                  prevEdge.getFileLocation());
          graph.appendChild(edge);
          // Remove the pair to avoid duplicates (since processed once)
          genINvs.remove(Pair.of(e.getFileLocation().getStartingLineNumber(), ""));
        }
      }

      // write the content into xml file
      TransformerFactory transformerFactory = TransformerFactory.newInstance();
      Transformer transformer = transformerFactory.newTransformer();
      DOMSource source = new DOMSource(doc);
      File tempFile =
          new File(
              new URI(
                  "file:///home/cppp/Documents/cpachecker/cpachecker/output/proofWitness42.graphml"));
      StreamResult result = new StreamResult(tempFile);
      transformer.transform(source, result);

      final Set<CandidateInvariant> candidates = new LinkedHashSet<>();

      final Multimap<String, CFANode> candidateGroupLocations = HashMultimap.create();

      WitnessInvariantsExtractor extractor =
          new WitnessInvariantsExtractor(
              pConfig,
              pSpecification,
              pLogger,
              pCfa,
              pShutdownNotifier,
              tempFile.toPath());
      extractor.extractCandidatesFromReachedSet(candidates, candidateGroupLocations);
      System.out.println(candidates.toString());
      return new StaticCandidateProvider(candidates);
    } catch (TransformerException | ParserConfigurationException | NoSuchAlgorithmException
        | IOException | InvalidConfigurationException | InterruptedException
        | URISyntaxException e) {
      throw new CPAException(getMessage(), e);
    }
  }

  private String getMessage() {
    return "During computation, an interla error occured. The added exception provides a more detailed explanation"
        + System.lineSeparator()
        + "* @throws CPAException If the CFA contains more than one source file"
        + System.lineSeparator()
        + "  * @throws ParserConfigurationException in case of errors while parsing the Witness"
        + System.lineSeparator()
        + " * @throws IOException if the source file is not readable"
        + System.lineSeparator()
        + " * @throws NoSuchAlgorithmException if no SHA256 is available"
        + System.lineSeparator()
        + " * @throws TransformerException If the xml file is invalid"
        + System.lineSeparator()
        + " * @throws InterruptedException, InvalidConfigurationException  in case of problems loading the generated invariant"
        + System.lineSeparator();
  }

  private Element getEdge(
      Document pDoc,
      Element pSource,
      Element pTarget,
      boolean pIsLoopStart,
      FileLocation pFileLocation) {

    Element edge = pDoc.createElement("edge");
    edge.setAttributeNode(createAttrForDoc(pDoc, "source", pSource.getAttribute("id")));
    edge.setAttributeNode(createAttrForDoc(pDoc, "target", pTarget.getAttribute("id")));

    if (pIsLoopStart) {
      edge = createAndAppandDataNode(edge, pDoc, "enterLoopHead", "true");
    }
    edge =
        createAndAppandDataNode(
            edge,
            pDoc,
            "startline",
            String.valueOf(pFileLocation.getStartingLineNumber()));
    edge =
        createAndAppandDataNode(
            edge,
            pDoc,
            "endline",
            String.valueOf(pFileLocation.getEndingLineNumber()));
    edge =
        createAndAppandDataNode(
            edge,
            pDoc,
            "startoffset",
            String.valueOf(pFileLocation.getNodeOffset()));
    edge =
        createAndAppandDataNode(
            edge,
            pDoc,
            "endoffset",
            String.valueOf(pFileLocation.getNodeOffset() + pFileLocation.getNodeLength()));
    return edge;
  }

  private Element getEnterFunctionEdge(
      Document pDoc,
      Element pSource,
      Element pTarget,
      String nameOfEnterFunction,
      FileLocation pFileLocation) {

    Element edge = pDoc.createElement("edge");
    edge.setAttributeNode(createAttrForDoc(pDoc, "source", pSource.getAttribute("id")));
    edge.setAttributeNode(createAttrForDoc(pDoc, "target", pTarget.getAttribute("id")));

    edge =
        createAndAppandDataNode(
            edge,
            pDoc,
            "startline",
            String.valueOf(pFileLocation.getStartingLineNumber()));
    edge =
        createAndAppandDataNode(
            edge,
            pDoc,
            "endline",
            String.valueOf(pFileLocation.getEndingLineNumber()));

    edge = createAndAppandDataNode(edge, pDoc, "enterFunction", nameOfEnterFunction);
    return edge;
  }

  private Element createNodeWithInvariant(Document pDoc, String pInv, String nameOfNode) {
    Element invNode = pDoc.createElement("node");
    invNode.setAttributeNode(createAttrForDoc(pDoc, "id", nameOfNode));

    Element scope = pDoc.createElement("data");
    scope.setAttributeNode(createAttrForDoc(pDoc, "key", "invariant.scope"));
    scope.appendChild(pDoc.createTextNode("main"));
    invNode.appendChild(scope);
    Element iinvDataNode = pDoc.createElement("data");
    iinvDataNode.setAttributeNode(createAttrForDoc(pDoc, "data", "invariant"));
    iinvDataNode.setTextContent(pInv);
    invNode.appendChild(iinvDataNode);
    return invNode;
  }

  private Element createBlankNode(Element pGraph, Document pDoc, String nameOfNode) {
    Element node = pDoc.createElement("node");
    node.setAttributeNode(createAttrForDoc(pDoc, "id", nameOfNode));

    pGraph.appendChild(node);
    return pGraph;

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
    return pGraph;

  }

  private Element createAndAppandDataNode(
      Element pGraph,
      Document pDoc,
      String pStringpKeyValue,
      String textValue) {

    Element data = pDoc.createElement("data");
    data.setAttributeNode(createAttrForDoc(pDoc, "key", pStringpKeyValue));
    data.appendChild(pDoc.createTextNode(textValue));
    pGraph.appendChild(data);
    return pGraph;
  }

  private Element getDochWithHeader(String pString, File pSourceFile, CFA pCfa, Document doc)
      throws ParserConfigurationException {

    Element graphml = doc.createElement("graphml");


    graphml.setAttributeNode(createAttrForDoc( doc,"xmlns", "\"http://graphml.graphdrawing.org/xmlns\""));
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
    Element scope = doc.createElement("data");
    scope.setAttributeNode(createAttrForDoc(doc, "key", "invariant.scope"));
    scope.appendChild(doc.createTextNode("main"));

    return graphml;
  }

  private Attr createAttrForDoc(Document pDoc, String attrName, String value) {
    Attr newAttr = pDoc.createAttribute(attrName);
    newAttr.setNodeValue(value);
    return newAttr;
  }

  private Node
      getDefaultNode(Document doc, String attr1, String attr2, String attr3, String attr4) {
    Element node = doc.createElement("data");
    node.setAttributeNode(createAttrForDoc(doc, "attr.name", attr1));
    node.setAttributeNode(createAttrForDoc(doc, "attr.type", attr2));
    node.setAttributeNode(createAttrForDoc(doc, "for", attr3));
    node.setAttributeNode(createAttrForDoc(doc, "id", attr4));
    return node;
  }

  private Node getDefaultNode(
      Document doc,
      String attr1,
      String attr2,
      String attr3,
      String attr4,
      String defaultVal) {
    Element node = doc.createElement("data");
    node.setAttributeNode(createAttrForDoc(doc, "attr.name", attr1));
    node.setAttributeNode(createAttrForDoc(doc, "attr.type", attr2));
    node.setAttributeNode(createAttrForDoc(doc, "for", attr3));
    node.setAttributeNode(createAttrForDoc(doc, "id", attr4));

    Node child = doc.createElement("default");
    child.setTextContent(defaultVal);
    node.appendChild(child);
    return node;
  }

  private String getHash(File pSourceFile) throws IOException, NoSuchAlgorithmException {

    StringBuilder builder = new StringBuilder();

    @SuppressWarnings("resource")
    BufferedReader reader = new BufferedReader(new FileReader(pSourceFile));
    reader.lines().forEachOrdered(l -> builder.append(l));
    reader.close();

    MessageDigest digest = MessageDigest.getInstance("SHA-256");
    byte[] encodedhash = digest.digest(builder.toString().getBytes(StandardCharsets.UTF_8));
    System.out.println(builder.toString());

    return String.valueOf(encodedhash);
  }

  private Map<Pair<Integer, String>, String> generateInvariantsAndLoad(Path pPath) {
    // TODO Auto-generated method stub
    Map<Pair<Integer, String>, String> dummyINvs = new HashMap<>();
    dummyINvs
        // .put(Pair.of(13, "while(x>0)"), "(( ( n + - x + - y ) )<=0)&&(( ( x + y + - n ) )<=0)");
        .put(Pair.of(13, ""), "(( ( n + - x + - y  ) )<=0)&&(( ( x + y + - n  ) )<=0)");
    return dummyINvs;

  }

}
