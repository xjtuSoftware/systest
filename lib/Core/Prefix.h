/*
 * Prefix.h
 *
 *  Created on: 2015年2月3日
 *      Author: berserker
 */

#ifndef LIB_CORE_PREFIX_H_
#define LIB_CORE_PREFIX_H_

#include "Event.h"
#include "llvm/Support/raw_ostream.h"
#include <iostream>
#include <vector>
#include <map>
#include <string>

namespace klee {

class Prefix {
public:
	typedef std::vector<Event*>::iterator EventIterator;

private:
	std::vector<Event*> eventList;
	std::map<Event*, uint64_t> threadIdMap;
	EventIterator pos;
	std::string name;

	unsigned breakEventId;

public:
	Prefix(std::vector<Event*>& eventList, std::map<Event*, uint64_t>& threadIdMap, std::string name);
	virtual ~Prefix();
	std::vector<Event*>* getEventList();
	void increase();
	void reuse();
	bool isFinished();
	void setFinished();
	EventIterator begin();
	EventIterator end();
	EventIterator current();
	uint64_t getNextThreadId();
	unsigned getCurrentEventThreadId();
	void print(std::ostream &out);
	void print(llvm::raw_ostream &out);
	KInstruction* getCurrentInst();
	std::string getName();

	void setBreakEventId(unsigned& eBreak);
	unsigned& getBreakEventId();
};

} /* namespace klee */

#endif /* LIB_CORE_PREFIX_H_ */
