/*
 * CoverageBasedTesting.h
 *
 *  Created on: Sep 27, 2015
 *      Author: x
 */

#ifndef COVERAGEBASEDTESTING_H_
#define COVERAGEBASEDTESTING_H_

#include "Event.h"
#include "RuntimeDataManager.h"
#include <z3++.h>
#include <stack>
#include <vector>
#include <utility>
#include <algorithm>
#include <functional>

using namespace llvm;
using namespace z3;
using namespace std;
namespace klee {

class CoverageBasedTesting {
private:
	RuntimeDataManager& runtimeData;
	Trace* trace; //all data about encoding
	context& z3_ctx;
	solver& z3_solver;
	unsigned CRType;
	unsigned coverageMode;
	map<string, Event*> latestWriteOneThread;
	map<string, Event*> latestReadOneThread;

	Event* currentEvent;

public:
	CoverageBasedTesting(RuntimeDataManager& data, unsigned crType, unsigned cMode);
	virtual ~CoverageBasedTesting();

private:
	void buildDU();
	void buildMAP();
	void buildSP();
	void generateSchedule(vector<Event*>& vecEvent);
	void coverSingleCR(std::vector<expr>& exprVec, std::vector<Event*>& correlativeEvent);
	void coverMultipleCR(vector<expr>& exprVec);
	void markLatestWriteForGlobalVar();
	void markLatestReadOrWriteForGlobalVar();
	void sortGlobalSet(std::map<std::string, std::vector<Event *> >& sourceSet);
	void reduceSet(std::map<std::string, std::vector<Event *> >& sourceSet);

	void nonCR();
	void selectCRSet(std::vector<expr>& sourceSet);
	void addAllCR(std::vector<expr>& exprVec);

	void makeFullExprForRWR(std::map<string, std::vector<Event*> >::iterator, std::vector<Event*>::iterator);
	void makeFullExprForWWR(std::map<string, std::vector<Event*> >::iterator, std::vector<Event*>::iterator);

	Event* getFirstPthreadCreateEvent();
public:
	void buildCoverageRequirement();
	void computeNewSchedule();
	void setCurrentEvent(Event*);
	Event* getCurrentEvent();

};


	bool less_tid(const Event * lEvent, const Event*);
	void printOpSet(std::map<std::string, std::vector<Event*> >&);
	void printOpSetBriefly(std::map<std::string, std::vector<Event*> >&);
	template <class T> struct displayVector;
} /* namespace klee */

#endif /* COVERAGEBASEDTESTING_H_ */
