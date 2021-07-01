// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.value;

import com.google.common.base.Strings;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

/** A class to load the specified testcase from testcomp-output */
public class TestCompTestcaseLoader {

  public static Map<Integer, String> loadTestcase(Path pathToFile, LogManager pLogger)
      throws ParserConfigurationException, SAXException, IOException {

    if (pathToFile.toFile().exists() && pathToFile.toFile().canRead()) {
      List<String> xml = Files.readAllLines(pathToFile);

    DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      docFactory.setValidating(false);
    DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
    Map<Integer, String> inputs = new HashMap<>();

      // AS the env may be offline, remove the validation tag:
      List<String> toRemove = Lists.newArrayList();
      for (String line : xml) {
        if (line.contains("https://sosy-lab.org/test-format/testcase-1.0.dtd")) {
          toRemove.add(line);
        }
      }
      xml.removeAll(toRemove);
      InputSource is = new InputSource(new StringReader(String.join("", xml)));

      Document doc = docBuilder.parse(is);
    // Assuming that the testcase is valid, hence directly get the input
    NodeList nList = doc.getElementsByTagName("input");

    for (int i = 0; i < nList.getLength(); i++) {
      // Expected format is similar to <input variable="int" type ="int">1</input>
      Node current = nList.item(i);
      if (!Strings.isNullOrEmpty(current.getTextContent())) {
        inputs.put(i, current.getTextContent());
      }
    }
      pLogger.log(Level.INFO, String.format("The loaded input values are '%s'", inputs));
    return inputs;
  }
    return Maps.newHashMap();
  }
}
