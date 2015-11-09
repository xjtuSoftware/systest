/*
 * RuntimeDataManager.h
 *
 *  Created on: Jun 10, 2014
 *      Author: ylc
 */

#ifndef RUNTIMEDATAMANAGER_H_
#define RUNTIMEDATAMANAGER_H_

#include "Trace.h"
#include "Prefix.h"
#include <set>
namespace klee {
//added by xdzhang

typedef struct DefineUse {
	Event* pre; //if=null, stand for initial event.
	Event* post;
//	int exprIndex;
//	bool flag; //1-covered,0-uncovered
} DU;

typedef struct MultipleAccessPoints {
	Event* pre;
	Event* mid;
	Event* post;
	int exprIndex;
	bool flag; //1-covered,0-uncovered
} MAP;

typedef struct SynchronizePair {
	LockPair* pre;
	LockPair* post;
	int exprIndex;
	bool flag; //1-covered,0-uncovered
} SP;


class RuntimeDataManager {

private:
	std::vector<Trace*> traceList; // store all traces;
	Trace* currentTrace; // trace associated with current execution
	std::set<Trace*> testedTraceList; // traces which have been examined
	std::list<Prefix*> scheduleSet; // prefixes which have not been examined
	std::set<int> deadBranch;
	std::set<int> liveBranch;
	//newly added stastic info
	unsigned allFormulaNum;
	unsigned solvingTimes;
	double runningCost;
	double solvingCost;

public:
	//kinds info of Coverage Requirement.
	//
	context z3_ctx;
	solver z3_solver;
	std::vector<DU*> DUInfo;
	std::vector<expr> DUExpr;
	std::vector<MAP*> MAPInfo;
	std::vector<expr> MAPExpr;
	std::vector<SP*> SPInfo;
	std::vector<expr> SPExpr;

public:

	RuntimeDataManager();
	virtual ~RuntimeDataManager();
//	void insertEvent(Event* event, unsigned threadId);
//	void insertThreadCreateOrJoin(std::pair<Event*, uint64_t> item,
//			bool isThreadCreate);
//	void insertWait(std::string condName, Event* wait, Event* associatedLock);
//	void insertSignal(std::string condName, Event* event);
//	void insertLockOrUnlock(unsigned threadId, std::string mutex, Event* event,
//			bool isLock);
//	void insertGlobalVariableInitializer(std::string name,
//			llvm::Constant* initializer);
//	void insertPrintfParam(std::string name, llvm::Constant* param);
//	void insertGlobalVariableLast(std::string name, llvm::Constant* finalValue);
//	void insertBarrierOperation(std::string barrierName, Event* event);
//	void insertPath(Event* event);
//	void insertArgc(int argc);
//	void insertReadSet(std::string name, Event* item);
//	void insertWriteSet(std::string name, Event* item);
//	Event* createEvent(unsigned threadId, KInstruction* inst, unsigned codeLine,
//			std::string codeFile, std::string codeDir, uint64_t address,
//			bool isLoad, int time);
//	Event* createEvent(unsigned threadId, KInstruction* inst, unsigned codeLine,
//			std::string codeFile, std::string codeDir);
	Trace* createNewTrace(unsigned traceId);
	Trace* getCurrentTrace();
	void addScheduleSet(Prefix* prefix);
	void printCurrentTrace(bool file);
	Prefix* getNextPrefix();
	void clearAllPrefix();
	bool isCurrentTraceUntested();
	void printAllPrefix(std::ostream &out);
	void printAllTrace(std::ostream &out);
	bool isDeadBranch(int branch);
	bool isLiveBranch(int branch);
	void removeFromDeadBranch(int branch);
	void addToDeadBranch(int branch);
	void addToLiveBranch(int branch);
	void addStaticsInfo(double slovcost,double runcost, unsigned formulaNum, unsigned times);
};

}
#endif /* RUNTIMEDATAMANAGER_H_ */
