/*
 * WaitParam.h
 *
 *  Created on: Jul 24, 2014
 *      Author: klee
 */

#ifndef WAITPARAM_H_
#define WAITPARAM_H_

#include <string>

namespace klee {

class WaitParam {
public:
	std::string mutexName;
	unsigned threadId;

	WaitParam();
	WaitParam(std::string mutexName, unsigned threadId);
	virtual ~WaitParam();
};

}

#endif /* WAITPARAM_H_ */
