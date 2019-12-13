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

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.HashMap;
import java.util.Map;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class AddGeneratedInvToBlankWitness {

  public static void main(String argv[]) {

    try {
      File file =
          new File(
              new URI(
                  "file:///home/cppp/Documents/cpachecker/cpachecker/output/proofWitness1.graphml"));
      Map<String, String> nodesToInv = new HashMap<>();
      nodesToInv.put("N16", "(( ( n + - x + - y  ) )<=0)&&(( ( x + y + - n  ) )<=0)");

      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
      Document doc = docBuilder.parse(file);

      Element scope = doc.createElement("data");
      scope.setAttribute("key", "invariant.scope");
      scope.appendChild(doc.createTextNode("main"));

      // Get the root element
      Node graphml = doc.getElementsByTagName("graphml").item(0);
      Node graph = doc.getElementsByTagName("graph").item(0);

      NodeList nodes = doc.getElementsByTagName("node");
      // Get the graph
      for (int i = 0; i < nodes.getLength(); i++) {
        Node elem = nodes.item(i);
        NamedNodeMap attr = elem.getAttributes();
        Node nodeAttr = attr.getNamedItem("id");

        if (nodesToInv.containsKey(nodeAttr.getTextContent())) {

          elem.appendChild(scope);
          Element invNode = doc.createElement("data");
          invNode.setAttribute("data", "invariant");
          invNode.setTextContent(nodesToInv.get(nodeAttr.getTextContent()));
          elem.appendChild(invNode);
        }
      }

      // write the content into xml file
      TransformerFactory transformerFactory = TransformerFactory.newInstance();
      Transformer transformer = transformerFactory.newTransformer();
      DOMSource source = new DOMSource(doc);
      StreamResult result = new StreamResult(new File(file.getAbsolutePath() + "2"));
      transformer.transform(source, result);

      System.out.println("Done");

    } catch (ParserConfigurationException pce) {
      pce.printStackTrace();
    } catch (TransformerException tfe) {
      tfe.printStackTrace();
    } catch (IOException ioe) {
      ioe.printStackTrace();
    } catch (SAXException sae) {
      sae.printStackTrace();
    } catch (URISyntaxException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }

}
