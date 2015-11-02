/*
 * RuntimeDataManager.cpp
 *
 *  Created on: Jun 10, 2014
 *      Author: ylc
 */

#include "RuntimeDataManager.h"
#include "Transfer.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"
#else
#include "llvm/Constants.h"
#endif
#include <iostream>

using namespace std;
using namespace llvm;

namespace klee {

RuntimeDataManager::RuntimeDataManager() :
		currentTrace(NULL), z3_solver(z3_ctx) {
	// TODO Auto-generated constructor stub
	traceList.reserve(20);
	allFormulaNum = 0;
	solvingTimes = 0;
	solvingCost = 0.0;
	runningCost = 0.0;
}

RuntimeDataManager::~RuntimeDataManager() {
	// TODO Auto-generated destructor stub
	for (vector<Trace*>::iterator ti = traceList.begin(), te = traceList.end();
			ti != te; ti++) {
		delete *ti;
	}
	//added by xdzhang 2015.9.28
	for (unsigned i = 0; i < DUInfo.size(); i++) {
		if (DUInfo[i] != NULL)
			delete DUInfo[i];
	}
	for (unsigned i = 0; i < MAPInfo.size(); i++) {
		if (MAPInfo[i] != NULL)
			delete MAPInfo[i];
	}
	for (unsigned i = 0; i < SPInfo.size(); i++) {
		if (SPInfo[i] != NULL)
			delete SPInfo[i];
	}
	string ErrorInfo;
	raw_fd_ostream out_to_file("statics.txt", ErrorInfo, 0x0200);
	stringstream ss;
	ss << "SolvingCost: " << solvingCost << "\n";
	ss << "RunningCost: " << runningCost << "\n";
	ss << "SovingTimes: " << solvingTimes << "\n";
	ss << "AllFormulaNum: " << allFormulaNum << "\n";
	out_to_file << ss.str();
}

Trace* RuntimeDataManager::createNewTrace(unsigned traceId) {
	std:: cerr << "createNewTrace" << std::endl;
	currentTrace = new Trace();
	currentTrace->Id = traceId;
	traceList.push_back(currentTrace);
	return currentTrace;
}

Trace* RuntimeDataManager::getCurrentTrace() {
	return currentTrace;
}

void RuntimeDataManager::addScheduleSet(Prefix* prefix) {
	scheduleSet.push_back(prefix);
}

void RuntimeDataManager::printCurrentTrace(bool file) {
	currentTrace->print(file);
}

Prefix* RuntimeDataManager::getNextPrefix() {
	//cerr << "prefix num = " << scheduleSet.size() << endl;
	if (scheduleSet.empty()) {
		return NULL;
	} else {
		Prefix* prefix = scheduleSet.front();
		scheduleSet.pop_front();
		return prefix;
	}
}

void RuntimeDataManager::clearAllPrefix() {
	scheduleSet.clear();
}

bool RuntimeDataManager::isCurrentTraceUntested() {
	bool result = true;
	for (set<Trace*>::iterator ti = testedTraceList.begin(), te =
			testedTraceList.end(); ti != te; ti++) {
		if (currentTrace->isEqual(*ti)) {
			result = false;
			break;
		}
	}
	currentTrace->isUntested = result;
	if (result) {
		testedTraceList.insert(currentTrace);
	}
	return result;
}

void RuntimeDataManager::printAllPrefix(ostream &out) {
	out << "num of prefix: " << scheduleSet.size() << endl;
	unsigned num = 1;
	for (list<Prefix*>::iterator pi = scheduleSet.begin(), pe =
			scheduleSet.end(); pi != pe; pi++) {
		out << "Prefix " << num << endl;
		(*pi)->print(out);
		num++;
	}
}

bool RuntimeDataManager::isDeadBranch(int branch) {
	set<int>::iterator it = deadBranch.find(branch);
	return it != deadBranch.end() ? true : false;
}

void RuntimeDataManager::removeFromDeadBranch(int branch) {
	deadBranch.erase(branch);
}

void RuntimeDataManager::addToDeadBranch(int branch) {
	deadBranch.insert(branch);
}

bool RuntimeDataManager::isLiveBranch(int branch) {
	set<int>::iterator it = liveBranch.find(branch);
	return it != liveBranch.end() ? true : false;
}

void RuntimeDataManager::addToLiveBranch(int branch) {
	liveBranch.insert(branch);
}

void RuntimeDataManager::printAllTrace(ostream &out) {
	out << "\nTrace Info:\n";
	out << "num of trace: " << traceList.size() << endl << endl;
	unsigned num = 1;
	for (vector<Trace*>::iterator ti = traceList.begin(), te = traceList.end();
			ti != te; ti++) {
		Trace* trace = *ti;
		if (trace->isUntested) {
			out << "Trace " << num << endl;
			if (trace->abstract.empty()) {
				trace->createAbstract();
			}
			for (vector<string>::iterator ai = trace->abstract.begin(), ae =
					trace->abstract.end(); ai != ae; ai++) {
				out << *ai << endl;
			}
			out << endl;
			num++;
		}
	}
}
void RuntimeDataManager::addStaticsInfo(double solvcost,double runcost, unsigned formulaNum,
		unsigned times) {
	solvingCost += solvcost;
	runningCost += runcost;
	allFormulaNum += formulaNum;
	solvingTimes += times;
}
//void RuntimeDataManager::insertEvent(Event* event, unsigned threadId) {
//	//cerr << threadId << " " << eventList.size();
//	currentTrace->insertEvent(event, threadId);
//}
//
//void RuntimeDataManager::insertThreadCreateOrJoin(
//		std::pair<Event*, uint64_t> item, bool isThreadCreate) {
//	currentTrace->insertThreadCreateOrJoin(item, isThreadCreate);
//}
//
//void RuntimeDataManager::insertReadSet(string name, Event* item) {
//	currentTrace->insertReadSet(name, item);
//}
//
//void RuntimeDataManager::insertWriteSet(string name, Event* item) {
//	currentTrace->insertWriteSet(name, item);
//}
//
//void RuntimeDataManager::insertWait(string condName, Event* wait, Event* associatedLock) {
//	currentTrace->insertWait(condName, wait, associatedLock);
//}
//
//void RuntimeDataManager::insertSignal(string condName, Event* event) {
//	currentTrace->insertSignal(condName, event);
//}
//
//void RuntimeDataManager::insertLockOrUnlock(unsigned threadId, string mutex, Event* event,
//		bool isLock) {
//	currentTrace->insertLockOrUnlock(threadId, mutex, event, isLock);
//}
//
//void RuntimeDataManager::insertBarrierOperation(string name, Event* event) {
//	currentTrace->insertBarrierOperation(name, event);
//}
//
//void RuntimeDataManager::insertGlobalVariableInitializer(string name, Constant* initializer) {
//	currentTrace->insertGlobalVariableInitializer(name, initializer);
//}
//
//void RuntimeDataManager::insertPrintfParam(string name, Constant* param) {
//	currentTrace->insertPrintfParam(name, param);
//}
//
//void RuntimeDataManager::insertGlobalVariableLast(string name, Constant* finalValue) {
//	currentTrace->insertGlobalVariableLast(name, finalValue);
//}
//
//void RuntimeDataManager::insertPath(Event* event) {
//	currentTrace->insertPath(event);
//}
//
//void RuntimeDataManager::insertArgc(int argc) {
//	currentTrace->insertArgc(argc);
//}

}
