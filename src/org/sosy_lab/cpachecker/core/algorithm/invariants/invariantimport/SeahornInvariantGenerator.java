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
package org.sosy_lab.cpachecker.core.algorithm.invariants.invariantimport;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.ZoneId;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.time.temporal.ChronoUnit;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.logging.Level;
import javax.annotation.Nullable;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.WitnessInvariantsExtractor;
import org.sosy_lab.cpachecker.util.automaton.AutomatonGraphmlCommon;
import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import scala.NotImplementedError;

@Options(prefix = "invariantGeneration.kInduction.seahorn")
public class SeahornInvariantGenerator implements ExternalInvariantGenerator {

  private static final String PATH_TO_SCRIPTS =
      "src/org/sosy_lab/cpachecker/core/algorithm/invariants/invariantimport/scripts/";

  @Option(
    secure = true,
    description = "Path to the directory where the generated files should be stored. by default we use the /output dir")
  private String pathToOutDir = "output/";
  private static final String KEY_STRING = "key";
  private static final String DATA_STRING = "data";
  private static final int OFFSET = 0;
  private static final String NAME_OF_TOOL = "CoInVerify";
  private static final String MAIN_FUNCTION = "main";
  private static final String TEXT_ENTERING_EDGE = "Function start dummy edge";

  private static final String TRUE = "true";
  private static final String FALSE = "false";
  private int nodeNameCounter;
  private final String PATH_TO_CPA_DIR;

  public SeahornInvariantGenerator(Configuration pConfiguration)
      throws InvalidConfigurationException {
    // set the output directory to the directory used by the cpa checker
    pConfiguration.inject(this);
    this.nodeNameCounter = 0;
    PATH_TO_CPA_DIR =
        SeahornInvariantGenerator.class.getProtectionDomain()
            .getCodeSource()
            .getLocation()
            .getPath() + "../";
  }

  @Override
  public Set<CandidateInvariant> generateInvariant(
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
      Map<Integer, Pair<String, String>> genINvs =
          generateInvariantsAndLoad(sourceFiles.get(0), pCfa);

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
          getMappingLinesToEdgesOfFunction(
              pCfa,
              lineNumberOfMain,
              lineToEdgesOfMain,
              SeahornInvariantGenerator.MAIN_FUNCTION);

      CFANode mainEntryNode = getEntryNodeForFunction(pCfa, MAIN_FUNCTION);
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
      for (Entry<Integer, Pair<String, String>> inv : genINvs.entrySet()) {
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

        // Determine the minimal Start and maximal end offset for a given line (if there are more
        // statements present
        int minStartOffset = Integer.MAX_VALUE;
        int maxEndOffset = Integer.MIN_VALUE;
        boolean isLoopStart = true;

        for (CFAEdge e : lineToEdgesOfMain.get(lineNumber)) {

          Set<FileLocation> fileLocs =
              AutomatonGraphmlCommon.getFileLocationsFromCfaEdge(e, pCfa.getMainFunction());
          for (FileLocation loc : fileLocs) {
            // TODO: Add handling for edges with different starting and finishing line
            minStartOffset = Math.min(minStartOffset, loc.getNodeOffset());
            maxEndOffset = Math.max(maxEndOffset, loc.getNodeOffset() + loc.getNodeLength());
          }
          // Check if the flag "enterLoopHead" is true, meaning that the edge is one into a loop
          // head. If one is not a loop head don't set the flag
          if (!e.getSuccessor().isLoopStart()) {
            isLoopStart = false;
          }
        }
        Pair<String, String> sourceAndInv = inv.getValue();
        Element invElement =
            createNodeWithInvariant(doc, sourceAndInv.getSecond(), getNewNameForNode());
        graph.appendChild(invElement);

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
                maxEndOffset);
        graph.appendChild(edge);

      }

      // write the content into xml file
      TransformerFactory transformerFactory = TransformerFactory.newInstance();

      Transformer transformer = transformerFactory.newTransformer();
      transformer.setOutputProperty(OutputKeys.INDENT, "yes");
      transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");
      DOMSource source = new DOMSource(doc);
      File tempFile = new File(PATH_TO_CPA_DIR + pathToOutDir, "proofWitness_Seahorn.graphml");
      tempFile.createNewFile();
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
      pLogger.log(Level.FINER, "The invariants imported are" + candidates.toString());
      return candidates;
    } catch (TransformerException | ParserConfigurationException | IOException
        | InvalidConfigurationException | InterruptedException e) {
      throw new CPAException(getMessage() + System.lineSeparator() + e.toString(), e);
    }
  }

  private String getNewNameForNode() {
    nodeNameCounter = nodeNameCounter + 1;
    return "N" + nodeNameCounter;
  }

  private Map<Integer, Pair<String, String>> generateInvariantsAndLoad(Path pPath, CFA pCfa)
      throws IOException, InterruptedException {

    ProcessBuilder builder = new ProcessBuilder().inheritIO();

    String absolutePathToInvFile = PATH_TO_CPA_DIR + pathToOutDir;

    builder.command(
        PATH_TO_CPA_DIR + PATH_TO_SCRIPTS + "compute_invariants_with_seahorn.sh",
        pPath.toFile().getAbsolutePath(),
        absolutePathToInvFile,
        PATH_TO_CPA_DIR + PATH_TO_SCRIPTS);
    Process process = builder.start();

    int exitCode = process.waitFor();
    // After finishing the invariant generation script ensure that everything worked out as planned!
    assert exitCode == 0;
    return parseInvFile(absolutePathToInvFile + "invars_in_c.txt", pCfa);
  }

  @SuppressWarnings("resource")
  private Map<Integer, Pair<String, String>> parseInvFile(String pPathToInvFile, CFA pCfa) {
    BufferedReader reader = null;
    Map<Integer, Pair<String, String>> invs = new HashMap<>();
    try {
      reader = Files.newBufferedReader(Paths.get(pPathToInvFile), Charset.defaultCharset());
      String line = reader.readLine();
      // Skip the first line
      FileWriter fw;
      try {
        fw = new FileWriter("/home/cppp/Documents/seahorn/generatedINvariants.txt", true);
        BufferedWriter bw = new BufferedWriter(fw);
        bw.write(pCfa.getFileNames().get(0) + ":");
        bw.newLine();

      while ((line = reader.readLine()) != null) {
        if (line.indexOf(",") == -1) {
            if (line.startsWith("main@entry")
                || line.startsWith("main@verifier.error.split")
                || line.startsWith("main@")) {
            // Cannot parse these invariants (true or false, hence ignore it)
            reader.readLine();
          } else {
            throw new IllegalArgumentException(
                "The file was not parsed as expected, the line "
                    + line
                    + "does nto have the format 'Linenumber , sourcecode");
          }
        } else {
          int lineNumber = Integer.parseInt(line.substring(0, line.indexOf(",")));
          // +1 to ignore the ','
          String code = line.substring(line.indexOf(",") + 1);
          String inv = reader.readLine();
          invs.put(lineNumber - OFFSET, Pair.of(code, inv));

            bw.write(code + " <-->" + inv);
            bw.newLine();
        }
      }
      reader.close();
        // Store the generated invariant for later evaluations
        bw.close();
      } catch (IOException e) {
        throw new IllegalArgumentException(e);
      }

    } catch (IOException e) {
      // TOO enhance error logging
      throw new IllegalArgumentException(e);
    }

    return invs;
  }

  private CFANode getEntryNodeForFunction(CFA pCfa, String pnameOfFunction) {
    CFANode mainEntryNode = null;
    // find the dummy entering edge:
    for (CFANode n : pCfa.getAllNodes()) {
      if (n.getFunctionName().equals(pnameOfFunction)) {
        for (int i = 0; i < n.getNumEnteringEdges(); i++) {
          if (n.getEnteringEdge(i) instanceof BlankEdge
              && n.getEnteringEdge(i).getDescription().equals(TEXT_ENTERING_EDGE)) {
            mainEntryNode = n;
            break;
          }
        }
      }
    }
    return mainEntryNode;
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
          if (enteringEdge instanceof CDeclarationEdge
              && enteringEdge.getRawStatement().equals("int main()")) {
            lineNumberOfMain = enteringEdge.getLineNumber();
          }
        }
      }
    }
    return lineNumberOfMain;
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

  private String getMessage() {
    return "During computation, an interla error occured. The added exception provides a more detailed explanation"
        + System.lineSeparator()
        + "* @throws CPAException If the CFA contains more than one source file"
        + System.lineSeparator()
        + "  * @throws ParserConfigurationException in case of errors while parsing the Witness"
        + System.lineSeparator()
        + " * @throws IOException if the source file is not readable"
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
      int pLineNumberStart,
      int pLineNumberEnd,
      int pStartOffset,
      int pEndOffset) {
    Element edge = pDoc.createElement("edge");
    edge.setAttributeNode(createAttrForDoc(pDoc, "source", pSource.getAttribute("id")));
    edge.setAttributeNode(createAttrForDoc(pDoc, "target", pTarget.getAttribute("id")));

    if (pIsLoopStart) {
      edge = createAndAppandDataNode(edge, pDoc, "enterLoopHead", "true");
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
}
