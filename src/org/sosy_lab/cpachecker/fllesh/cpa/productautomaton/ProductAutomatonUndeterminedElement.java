package org.sosy_lab.cpachecker.fllesh.cpa.productautomaton;

public class ProductAutomatonUndeterminedElement implements
    ProductAutomatonElement {

  private static ProductAutomatonUndeterminedElement mInstance = new ProductAutomatonUndeterminedElement();
  
  public static ProductAutomatonUndeterminedElement getInstance() {
    return mInstance;
  }
  
  private ProductAutomatonUndeterminedElement() {
    
  }

  @Override
  public String toString() {
    return "Undetermined";
  }

}
