package org.sosy_lab.cpachecker.fllesh.cpa.productautomaton;

public class ProductAutomatonTopElement implements ProductAutomatonElement {

  private static ProductAutomatonTopElement mInstance = new ProductAutomatonTopElement();
  
  public static ProductAutomatonTopElement getInstance() {
    return mInstance;
  }
  
  private ProductAutomatonTopElement() {
    
  }

}
