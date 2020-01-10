/*
 * converter.h
 *
 *  Created on: Nov 28, 2019
 *      Author: jfh
 */

#ifndef CONVERTER_H_
#define CONVERTER_H_

#include <string>

 namespace converter{

 /**
  * Converts a string containing an prefix formula into infix. The separator are whitespace
  */
std::string preToInfix(std::string pre_exp);
}
#endif /* CONVERTER_H_ */
