/*
 * CoverageBasedTesting.cpp
 *
 *  Created on: Sep 27, 2015
 *      Author: x
 */

#include "CoverageBasedTesting.h"
#include "KQuery2Z3.h"
#include <map>
#include <vector>
using namespace std;
using namespace llvm;
using namespace z3;
#include "Trace.h"
#include "Encode.h"
#define DEBUG 0
#define PRINT_OPERATION_SET_DETAILED 0
#define PRINT_OPERATION_SET_BRIEFLY 1
#define PRINT_DEF_USE 1
namespace klee {

CoverageBasedTesting::CoverageBasedTesting(RuntimeDataManager& data, unsigned crType,
		unsigned cMode) :
		runtimeData(data), z3_ctx(data.z3_ctx), z3_solver(data.z3_solver), CRType(
				crType), coverageMode(cMode) {
	trace = data.getCurrentTrace();
	currentEvent = NULL;
}

CoverageBasedTesting::~CoverageBasedTesting() {
	// TODO Auto-generated destructor stub
}

void CoverageBasedTesting::buildDU() {

	std::cout << "read set size:" << trace->readSet.size() << std::endl;
	std::cout << "write set size:" << trace->writeSet.size() << std::endl;

#if PRINT_OPERATION_SET_DETAILED
	std::cout << "print readSet(detailed):" << std::endl;
	printOpSet(trace->readSet);
	std::cout << "print writeSet(detailed):" << std::endl;
	printOpSet(trace->writeSet);
#endif

#if PRINT_OPERATION_SET_BRIEFLY
	std::cout << "print readSet(briefly):" << std::endl;
	printOpSetBriefly(trace->readSet);
	std::cout << "print writeSet(briefly):" << std::endl;
	printOpSetBriefly(trace->writeSet);
#endif

	assert(trace->readSet.size() != 0 && "readSet is empty");
	markLatestWriteForGlobalVar();
//	reduceSet(trace->readSet);
//	reduceSet(trace->writeSet);

#if DEBUG
	std::map<string, vector<Event *> >::iterator iRead = trace->readSet.begin();
	std::map<string, vector<Event *> >::iterator iWrite = trace->writeSet.begin();
	while(iRead != trace->readSet.end()){
		std::cout << "read event:" << iRead->first << std::endl;
		std::vector<Event*>::iterator irEvent = iRead->second.begin();
		while(irEvent != iRead->second.end()){
			std::cout << (*irEvent)->toString() << std::endl;
			if((*irEvent)->latestWrite != NULL)
				std::cout << "LatestWrite: " << (*irEvent)->latestWrite->eventId << " ;" << (*irEvent)->latestWrite->eventName << std::endl;
			else
				std::cout << "LatestWrite: " << "NULL" << std::endl;

			if((*irEvent)->latestRead !=NULL)
				std::cout << "LatestRead: " << (*irEvent)->latestRead->eventId << " ;" << (*irEvent)->latestRead->eventName << std::endl;
			else
				std::cout << "LatestRead: " << "NULL" << std::endl;

			std::cout << std::endl;
			irEvent++;
		}
		iRead++;
	}

	while(iWrite != trace->writeSet.end()){
		std::cout << "write event:" << iWrite->first << std::endl;
		std::vector<Event*>::iterator iwEvent = iWrite->second.begin();
		while(iwEvent != iWrite->second.end()){
			std::cout << (*iwEvent)->toString() << std::endl;
//			std::cout << "LatestWrite: " << (*iwEvent)->latestWrite->eventId << " ;" << (*iwEvent)->latestWrite->eventName << std::endl;
//			std::cout << "LatestRead: " << (*iwEvent)->latestRead->eventId << " ;" << (*iwEvent)->latestRead->eventName << std::endl;

			if((*iwEvent)->latestWrite != NULL)
							std::cout << "LatestWrite: " << (*iwEvent)->latestWrite->eventId << " ;" << (*iwEvent)->latestWrite->eventName << std::endl;
						else
							std::cout << "LatestWrite: " << "NULL" << std::endl;

						if((*iwEvent)->latestRead !=NULL)
							std::cout << "LatestRead: " << (*iwEvent)->latestRead->eventId << " ;" << (*iwEvent)->latestRead->eventName << std::endl;
						else
							std::cout << "LatestRead: " << "NULL" << std::endl;

						std::cout << std::endl;

			iwEvent++;
		}
		iWrite++;
	}
#endif

	std::map<string, vector<Event *> >::iterator ir = trace->readSet.begin(); //key--variable
	for (; ir != trace->readSet.end(); ++ir) {
		map<string, vector<Event *> >::iterator iw = trace->writeSet.find(ir->first);
		//			assert(iw != trace->writeSet.end());
		if(iw == trace->writeSet.end())
			continue;
		for (unsigned k = 0; k < ir->second.size(); ++k) {
			Event *currentRead;
			Event *currentWrite;
			currentRead = ir->second[k];
			expr r = z3_ctx.int_const(currentRead->eventName.c_str());
			if (currentRead->latestWrite == NULL) { //maybe read from initialization or other thread
				expr initOp = z3_ctx.int_const("E_INIT");
				expr def_use_order_tpye1 = (initOp < r);  //read from initialization

				for (unsigned l = 0; l < iw->second.size(); ++l) {
					if (currentRead->threadId == iw->second[l]->threadId) //can't read
						continue;
					expr otherWrite = z3_ctx.int_const(
							iw->second[l]->eventName.c_str());
					def_use_order_tpye1 = def_use_order_tpye1 && (r < otherWrite);
				}
				//build define-use pair and insert it to CRSet
				runtimeData.DUExpr.push_back(def_use_order_tpye1);
				runtimeData.correlativeEvent.push_back(currentRead);

#if PRINT_DEF_USE
				std::cout << "def_use_order_type1" << std::endl;
				std::cout << def_use_order_tpye1 << std::endl;
				std::cout << currentRead->toString() << std::endl;
#endif

				//read from other thread
				for(unsigned l = 0; l < iw->second.size(); ++l){
					if(currentRead->threadId == iw->second[l]->threadId)
						continue;
					currentWrite = iw->second[l];
					expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
					expr def_use_order_type2 = (w < r);
					for(unsigned ll = 0; ll < iw->second.size(); ++ll){
						if(ll != l){
							expr otherWrite =z3_ctx.int_const(iw->second[ll]->eventName.c_str());
							def_use_order_type2 = def_use_order_type2
									&& ((otherWrite < w) || (r < otherWrite));
						}
					}
					//build define-use pair and insert it to CRSet
					runtimeData.DUExpr.push_back(def_use_order_type2);
					runtimeData.correlativeEvent.push_back(currentRead);
#if PRINT_DEF_USE
					std::cout << "def_use_order_type2" << std::endl;
					std::cout << def_use_order_type2 << std::endl;
					std::cout << currentRead->toString() << std::endl;
					std::cout << currentWrite->toString() << std::endl;
#endif
				}

#if DEBUG
				DefineUse* du = new DefineUse;
				du->pre = NULL;
				du->post = currentRead;
//				du->exprIndex = runtimeData.DUExpr.size();
//				du->flag = false;
				runtimeData.DUInfo.push_back(du);
#endif

			} else {
				for (unsigned l = 0; l < iw->second.size(); ++l) {
					currentWrite = iw->second[l];
					if (currentRead->threadId == currentWrite->threadId
							&& currentRead->latestWrite != currentWrite) { //can't read
						continue;
					}
					expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
					expr def_use_order = (w < r);
					for (unsigned ll = 0; ll < iw->second.size(); ++ll) {
						if (ll == l)
							continue;
						expr otherWrite = z3_ctx.int_const(
								iw->second[ll]->eventName.c_str());
						expr tmp = (otherWrite < w || r < otherWrite);
						def_use_order = def_use_order && tmp;
					}
					//build CR and insert to CRSet
					runtimeData.correlativeEvent.push_back(currentRead);
					runtimeData.DUExpr.push_back(def_use_order);
#if PRINT_DEF_USE
					std::cout << "debug2" << std::endl;
					std::cout << def_use_order << std::endl;
					std::cout << currentWrite->toString() << std::endl;
					std::cout << currentRead->toString() << std::endl;
#endif

#if DEBUG
					DefineUse* du = new DefineUse;
					du->pre = currentWrite;
					du->post = currentRead;
					runtimeData.DUInfo.push_back(du);
#endif
				}
			}
		}
	}
}

void CoverageBasedTesting::buildMAP() {
	//TODO:add this after testing MCP and DU

	// 4 kinds of CR(见shanlu论文):(1)R-W-R;(2)W-W-R;(3)R-W-W;(4)W-R-W
	std::cout << "Build Multiple Define-Use Pairs" << std::endl;
	std::cout << "read set size:" << trace->readSet.size() << std::endl;
	std::cout << "write set size:" << trace->writeSet.size() << std::endl;

#if PRINT_OPERATION_SET_DETAILED
	std::cout << "print readSet(detailed):" << std::endl;
	printOpSet(trace->readSet);
	std::cout << "print writeSet(detailed):" << std::endl;
	printOpSet(trace->writeSet);
#endif

#if PRINT_OPERATION_SET_BRIEFLY
	std::cout << "print readSet(briefly):" << std::endl;
	printOpSetBriefly(trace->readSet);
	std::cout << "print writeSet(briefly):" << std::endl;
	printOpSetBriefly(trace->writeSet);
#endif

	assert(trace->readSet.size() != 0 && "readSet is empty");

	sortGlobalSet(trace->readSet);
	sortGlobalSet(trace->writeSet);
	markLatestReadOrWriteForGlobalVar();

#if DEBUG
	std::map<string, vector<Event *> >::iterator iRead = trace->readSet.begin();
	std::map<string, vector<Event *> >::iterator iWrite = trace->writeSet.begin();
	while(iRead != trace->readSet.end()){
		std::cout << "read event:" << iRead->first << std::endl;
		std::vector<Event*>::iterator irEvent = iRead->second.begin();
		while(irEvent != iRead->second.end()){
			std::cout << (*irEvent)->toString() << std::endl;
			if((*irEvent)->latestWrite != NULL)
				std::cout << "LatestWrite: " << (*irEvent)->latestWrite->eventId << " ;" << (*irEvent)->latestWrite->eventName << std::endl;
			else
				std::cout << "LatestWrite: " << "NULL" << std::endl;

			if((*irEvent)->latestRead !=NULL)
				std::cout << "LatestRead: " << (*irEvent)->latestRead->eventId << " ;" << (*irEvent)->latestRead->eventName << std::endl;
			else
				std::cout << "LatestRead: " << "NULL" << std::endl;

			std::cout << std::endl;
			irEvent++;
		}
		iRead++;
	}

	while(iWrite != trace->writeSet.end()){
		std::cout << "write event:" << iWrite->first << std::endl;
		std::vector<Event*>::iterator iwEvent = iWrite->second.begin();
		while(iwEvent != iWrite->second.end()){
			std::cout << (*iwEvent)->toString() << std::endl;
//			std::cout << "LatestWrite: " << (*iwEvent)->latestWrite->eventId << " ;" << (*iwEvent)->latestWrite->eventName << std::endl;
//			std::cout << "LatestRead: " << (*iwEvent)->latestRead->eventId << " ;" << (*iwEvent)->latestRead->eventName << std::endl;

			if((*iwEvent)->latestWrite != NULL)
							std::cout << "LatestWrite: " << (*iwEvent)->latestWrite->eventId << " ;" << (*iwEvent)->latestWrite->eventName << std::endl;
						else
							std::cout << "LatestWrite: " << "NULL" << std::endl;

						if((*iwEvent)->latestRead !=NULL)
							std::cout << "LatestRead: " << (*iwEvent)->latestRead->eventId << " ;" << (*iwEvent)->latestRead->eventName << std::endl;
						else
							std::cout << "LatestRead: " << "NULL" << std::endl;

						std::cout << std::endl;

			iwEvent++;
		}
		iWrite++;
	}
#endif


	std::map<string, vector<Event*> >::iterator iread = trace->readSet.begin();
	std::map<string, vector<Event*> >::iterator iwrite;

//		R1
//		 	W		//R-W-R
//		R2
//
//	(1)R-W-R; (2)W-W-R; (3)R-W-W; (4)W-R-W
//	由于3,4均存在1,2的等价情况，所以不予构建
	while(iread != trace->readSet.end()){
		std::cout << "var name: " << iread->first << std::endl;
		iwrite = trace->writeSet.find(iread->first);
		if(iwrite == trace->writeSet.end()){
			++iread;
			continue;
		}

		std::vector<Event*>::iterator irEvent = (*iread).second.begin();
		while(irEvent != (*iread).second.end()) {
			if((*irEvent)->latestRead != NULL){
				if((*irEvent)->latestWrite != NULL) {
					if((*irEvent)->latestRead > (*irEvent)->latestWrite){
						//R-W-R
						makeFullExprForRWR(iwrite, irEvent);
						makeFullExprForWWR(iwrite, irEvent);
					} else {
						makeFullExprForWWR(iwrite, irEvent);
					}
				} else {
					makeFullExprForRWR(iwrite, irEvent);
				}
			} else {
				if((*irEvent)->latestWrite != NULL) {
					makeFullExprForWWR(iwrite, irEvent);
				}
			}
			++irEvent;
		}
		++iread;
	}
	std::cout << "Build Multiple Define-Use Pairs ,OK." << std::endl;
}

void CoverageBasedTesting::makeFullExprForRWR(std::map<string, std::vector<Event*> >::iterator iwrite,
		std::vector<Event*>::iterator irEvent){

	std::vector<Event*>::iterator iwEvent = (*iwrite).second.begin();
	while(iwEvent != (*iwrite).second.end()){
		if((*iwEvent)->threadId != (*irEvent)->threadId){

#if DEBUG
			MultipleAccessPoints* mulAccessPoint = new MultipleAccessPoints;
			mulAccessPoint->pre = (*irEvent)->latestRead;
			mulAccessPoint->mid = *iwEvent;
			mulAccessPoint->post = *irEvent;
			std::cout <<"full constrain: " << full << std::endl;
			std::cout <<"pre: " << mulAccessPoint->pre->toString() << std::endl;
			std::cout <<"mid: " << mulAccessPoint->mid->toString() << std::endl;
			std::cout <<"post: " << mulAccessPoint->post->toString() << std::endl;
#endif

			expr pre = z3_ctx.int_const((*irEvent)->latestRead->eventName.c_str());
			expr mid = z3_ctx.int_const((*iwEvent)->eventName.c_str());
			expr post = z3_ctx.int_const((*irEvent)->eventName.c_str());
			expr full = (pre < mid) && (mid < post);
			std::cout << "full constraint:" << full << std::endl;

			std::vector<Event*>::iterator ivec = (*iwrite).second.begin();
			while(ivec != (*iwrite).second.end()) {
				if((*ivec)->threadId != (*iwEvent)->threadId && (*ivec)->eventId != (*iwEvent)->eventId){
					expr tmp = z3_ctx.int_const((*ivec)->eventName.c_str());
					full = full && ((tmp < pre) || (post < tmp));
				}
				++ivec;
			}
			runtimeData.MAPExpr.push_back(full);
			runtimeData.correlativeEvent.push_back(*irEvent);
		}
		++iwEvent;
	}
}

void CoverageBasedTesting::makeFullExprForWWR(std::map<string, std::vector<Event*> >::iterator iwrite,
		std::vector<Event*>::iterator irEvent){

	std::vector<Event*>::iterator iwEvent = (*iwrite).second.begin();
	while(iwEvent != (*iwrite).second.end()){
		if((*iwEvent)->threadId != (*irEvent)->threadId){
#if DEBUG
			MultipleAccessPoints* mulAccessPoint = new MultipleAccessPoints;
			mulAccessPoint->pre = (*irEvent)->latestWrite;
			mulAccessPoint->mid = *iwEvent;
			mulAccessPoint->post = *irEvent;
#endif
			expr pre = z3_ctx.int_const((*irEvent)->latestWrite->eventName.c_str());
			expr mid = z3_ctx.int_const((*iwEvent)->eventName.c_str());
			expr post = z3_ctx.int_const((*irEvent)->eventName.c_str());
			expr full = (pre < mid) && (mid < post);
			std::cout << "full constraint:" << full << std::endl;

			std::vector<Event*>::iterator ivec = (*iwrite).second.begin();
			while(ivec != (*iwrite).second.end()) {
				if((*ivec)->threadId != (*iwEvent)->threadId && (*ivec)->eventId != (*iwEvent)->eventId){
					expr tmp = z3_ctx.int_const((*ivec)->eventName.c_str());
					full = full && ((tmp < pre) || (post < tmp));
				}
				++ivec;
			}
			runtimeData.MAPExpr.push_back(full);
			runtimeData.correlativeEvent.push_back(*irEvent);
		}
		++iwEvent;
	}
}

void CoverageBasedTesting::buildSP() {
	map<string, vector<LockPair *> >::iterator it =
			trace->all_lock_unlock.begin();
	for (; it != trace->all_lock_unlock.end(); it++) {
		vector<LockPair*> tempVec = it->second;
		int size = tempVec.size();
		for (int i = 0; i < size; i++) {
			expr oneLock = z3_ctx.int_const(
					tempVec[i]->lockEvent->eventName.c_str());
			expr oneUnlock = z3_ctx.int_const(
					tempVec[i]->unlockEvent->eventName.c_str());
			for (int j = 0; j < size; j++) {
				expr twoLock = z3_ctx.int_const(
						tempVec[j]->lockEvent->eventName.c_str());
				expr twoUnlock = z3_ctx.int_const(
						tempVec[j]->unlockEvent->eventName.c_str());
				expr synchronizePair = (oneUnlock < twoLock);
				for (int k = 0; k < size; k++) {
					if (k == j || k == i)
						continue;
					expr otherLock = z3_ctx.int_const(
							tempVec[k]->lockEvent->eventName.c_str());
					expr otherUnlock = z3_ctx.int_const(
							tempVec[k]->unlockEvent->eventName.c_str());
					synchronizePair = synchronizePair
							&& (otherUnlock < oneLock || twoUnlock < otherLock);
				}

				runtimeData.SPExpr.push_back(synchronizePair);
#if DEBUG
				SP* sp = new SP;
				sp->pre = tempVec[i];
				sp->post = tempVec[j];
				sp->exprIndex = runtimeData.SPExpr.size();
				sp->flag = false;
				runtimeData.SPInfo.push_back(sp);
#endif
			}
		}
	}
}

void CoverageBasedTesting::buildCoverageRequirement() {
	if (CRType == 1) { //Def-Use 1: relation between two shared points
		buildDU();
	} else if (CRType == 2) { //Def-Use 2: relation among three shared points
		buildMAP();
	} else if (CRType == 3) { //Synchronize Pair
		buildSP();
	} else {
		assert(0 && "Wrong CRType!!!");
	}
}

void CoverageBasedTesting::computeNewSchedule() {
//Schedule which covers kinds of coverage requirement
	if (coverageMode == 1) { //Def-Use1 and Single CR
		coverSingleCR(runtimeData.DUExpr, runtimeData.correlativeEvent);
//		nonCR();
	} else if (coverageMode == 2) { //Def-Use1 and multiple CR
//		selectCRSet(runtimeData.DUExpr);
//		addAllCR(runtimeData.DUExpr);
		coverMultipleCR(runtimeData.DUExpr);
	} else if (coverageMode == 3) { //Def-Use2 and Single CR
		coverSingleCR(runtimeData.MAPExpr, runtimeData.correlativeEvent);
	} else if (coverageMode == 4) { //Def-Use2 and multiple CR
		coverMultipleCR(runtimeData.MAPExpr);
	} else if (coverageMode == 5) { //Synchronize Pair and Single CR
//		coverSingleCR(runtimeData.SPExpr);
	} else if (coverageMode == 6) { //Synchronize Pair and multiple CR
		coverMultipleCR(runtimeData.SPExpr);
	} else {
		assert(0 && "Wrong Mode!!!");
	}
}

void CoverageBasedTesting::generateSchedule(vector<Event*>& vecEvent) {
	vector<struct Pair *> eventOrderPair;

	//get the order of event
	model m = z3_solver.get_model();
	stringstream ss;
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, size = thread->size(); index < size; index++) {
			if (thread->at(index)->eventType == Event::VIRTUAL)
				continue;

			expr eve = z3_ctx.int_const(thread->at(index)->eventName.c_str());
			stringstream ss;
			ss << m.eval(eve);
			long order = atoi(ss.str().c_str());
			//put the event to its position
			Pair * pair = new Pair; //should be deleted
			pair->order = order;
			pair->event = thread->at(index);
			eventOrderPair.push_back(pair);
		}
	}
	//sort all events according to order
	unsigned size = eventOrderPair.size();
	for (unsigned i = 0; i < size - 1; i++) {
		for (unsigned j = 0; j < size - i - 1; j++) {
			if (eventOrderPair[j]->order > eventOrderPair[j + 1]->order) {
				Pair *temp = eventOrderPair[j];
				eventOrderPair[j] = eventOrderPair[j + 1];
				eventOrderPair[j + 1] = temp;
			}
		}
	}
	//put the ordered events to vecEvent and delete Pair.
	for (unsigned i = 0; i < eventOrderPair.size(); i++) {
		//TODO: use a simple struct to log prefix
		vecEvent.push_back(eventOrderPair[i]->event);
		delete eventOrderPair[i];
	}
}

void CoverageBasedTesting::nonCR(){
	z3_solver.push();

	check_result result;
	try {
		result = z3_solver.check();
	} catch (z3::exception & ex) {
		std::cout << "\n unexpected error: " << ex << std::endl;
		return;
	}

	if (result == z3::sat) {
		vector<Event*> vecEvent;
		generateSchedule(vecEvent);
		Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint, "");
		runtimeData.addScheduleSet(prefix);
		z3_solver.pop();
	}else {
		std::cout << "\n unexpected error11111111111111111111111: " << std::endl;
	}
}
void CoverageBasedTesting::coverSingleCR(vector<expr>& exprVec, std::vector<Event*>& correlativeEvent) {
	std::cout << "Create New Prefix, Cover Single CR" << std::endl;
	std::cout << "cr set size: " << exprVec.size() << std::endl;
	std::cout << "du set size: " << correlativeEvent.size() << std::endl;
	std::vector<expr>::iterator it = exprVec.begin();

	std::vector<Event*>::iterator iCorEvent = correlativeEvent.begin();

	while (it != exprVec.end()) {
		std::cout << "the Def-Use constraint:" << std::endl;
		std::cout << *it << "\n" << std::endl;
//		std::cout << (*itDU)->pre->eventName << "  " << (*itDU)->pre->toString() << std::endl;
//		std::cout << (*itDU)->post->eventName << "  " << (*itDU)->post->toString() << std::endl;

//		std::cout << (*itDU)->pre->eventName << "  " << (*itDU)->pre->inst->info->id << std::endl;
//		std::cout << (*itDU)->post->eventName << "  " << (*itDU)->post->inst->info->id << std::endl;
		z3_solver.push();
		z3_solver.add(*it);

		check_result result;
		try {
			result = z3_solver.check();
		} catch (z3::exception & ex) {
			std::cout << "\n unexpected error: " << ex << std::endl;
			continue;
		}

		if (result == z3::sat) {
			vector<Event*> vecEvent;
			try {
				generateSchedule(vecEvent);
			}
			catch (z3::exception& ex) {
				std::cout << "\n unexpected error: " << ex << std::endl;
				assert(false && "z3 exception");
			}
			Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint, "");
			std::cout <<"eventName: " << (*iCorEvent)->eventName << "  unsigned : " << (*iCorEvent)->inst->info->id << std::endl;
			unsigned br = (*iCorEvent)->inst->info->id;
			prefix->setBreakEventId(br);
//			prefix->print(std::cout);
			runtimeData.addScheduleSet(prefix);
			it = exprVec.erase(it);
			iCorEvent = correlativeEvent.erase(iCorEvent);
			z3_solver.pop();
			return;
		}
		it = exprVec.erase(it);
		iCorEvent = correlativeEvent.erase(iCorEvent);
		std::cout << "delete\n" << std::endl;
		z3_solver.pop();
	}
	std::cout << "all done" << std::endl;
	return ;
}

void CoverageBasedTesting::coverMultipleCR(vector<expr>& exprVec) {
	std::cout << "\n#################Create New Prefix, Cover multiple CR#################" << std::endl;
	std::cout << "cr set size: " << exprVec.size() << std::endl;

	std::vector<expr>::iterator it = exprVec.begin();
	int cnt = 0;
	while (it != exprVec.end()) {

#if PRINT_DEF_USE
		std::cout << "the Def-Use constraint:" << std::endl;
		std::cout << *it << "\n" << std::endl;
#endif

		z3_solver.push();
		z3_solver.add(*it);

		check_result result;
		try {
			result = z3_solver.check();
		} catch (z3::exception& ex) {
			std::cout << "\n unexpected error: " << ex << std::endl;
			continue;
		}

		if (result == z3::sat) {
			++cnt;
			it = exprVec.erase(it);
			std::cout << "mark&&delete\n" << std::endl;
		}else{
			if(cnt == 0){
				it = exprVec.erase(it);
				std::cout << "delete\n" << std::endl;
			} else{
				it++;
				std::cout << "leave for next\n" << std::endl;
			}
			z3_solver.pop();
		}
	}
//	assert(cnt != 0 && "No useful CR left");
	if (cnt == 0){
		Prefix* prefix = NULL;
		runtimeData.addScheduleSet(prefix);
		return;
	}

	check_result result;
	try {
		result = z3_solver.check();
	} catch (z3::exception& ex) {
		std::cout << "\n unexpected error: " << ex << std::endl;
		assert(false && "first z3 exception");
	}

	if (result == z3::sat) {
		vector<Event*> vecEvent;
			try {
				generateSchedule(vecEvent);
			}
			catch (z3::exception& ex) {
				std::cout << "\n unexpected error: " << ex << std::endl;
				assert(false && "second z3 exception");
			}
			Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint, "");
			runtimeData.addScheduleSet(prefix);
	}else{
		assert(false && "third z3 exception");
	}

//	vector<Event*> vecEvent;
//	try {
//		generateSchedule(vecEvent);
//	}
//	catch (z3::exception& ex) {
//		std::cout << "\n unexpected error: " << ex << std::endl;
//		assert(false && "z3 exception");
//	}
//	Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint, "");
//	runtimeData.addScheduleSet(prefix);

	while(cnt){
		z3_solver.pop();
		--cnt;
	}

	std::cout << "all done" << std::endl;
	return ;
}

void CoverageBasedTesting::addAllCR(vector<expr>& exprVec){
	std::cout << "\n#################add all CR, Create New Prefix, Cover multiple CR#################" << std::endl;
	std::cout << "cr set size: " << exprVec.size() << std::endl;

	std::vector<expr>::iterator it = exprVec.begin();
	while (it != exprVec.end()) {
		std::cout << *it << "\n" << std::endl;
		z3_solver.push();
		z3_solver.add(*it);
		it++;
	}

	check_result result;
	try {
		result = z3_solver.check();
	} catch (z3::exception& ex) {
		std::cout << "\n unexpected error: " << ex << std::endl;
		assert(false && "first z3 exception");
	}

	if (result == z3::sat) {
		vector<Event*> vecEvent;
		try {
			generateSchedule(vecEvent);
		} catch (z3::exception& ex) {
			std::cout << "\n unexpected error: " << ex << std::endl;
			assert(false && "second z3 exception");
		}
		Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint, "");
		runtimeData.addScheduleSet(prefix);
	}else{
		assert(false && "third z3 exception");
	}
	exprVec.clear();

	std::cout << "all done" << std::endl;
	return ;
}

void CoverageBasedTesting::markLatestWriteForGlobalVar() { //called by buildReadWriteFormula
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0; index < thread->size(); index++) {
			Event* event = thread->at(index);
			if (event->isGlobal) {
				Instruction *I = event->inst->inst;
				if (StoreInst::classof(I)) { //write
					Event* writeEvent;
					map<string, Event*>::iterator it;
					it = latestWriteOneThread.find(event->varName);
					if (it != latestWriteOneThread.end()) {
						writeEvent = it->second;
					} else {
						writeEvent = NULL;
					}
					event->latestWrite = writeEvent;

					latestWriteOneThread[event->varName] = event;
				} else if (!event->implicitGlobalVar.empty()
						&& CallInst::classof(I)) {
					for (unsigned i = 0; i < event->implicitGlobalVar.size(); i++) {

						Event* writeEvent;
						map<string, Event*>::iterator it;
						it = latestWriteOneThread.find(event->varName);
						if (it != latestWriteOneThread.end()) {
							writeEvent = it->second;
						} else {
							writeEvent = NULL;
						}
						event->latestWrite = writeEvent;

						string curr = event->implicitGlobalVar[i];
						string varName = curr.substr(0, curr.find('S', 0));
						latestWriteOneThread[varName] = event;
						std::cout << "CallInst:" << std::endl;
						I->dump();
					}
				} else { //read
					Event* writeEvent;
					map<string, Event*>::iterator it;
					it = latestWriteOneThread.find(event->varName);
					if (it != latestWriteOneThread.end()) {
						writeEvent = it->second;
					} else {
						writeEvent = NULL;
					}
					event->latestWrite = writeEvent;
				}
			}
		}
		//post operations
		latestWriteOneThread.clear();
	}
}

void CoverageBasedTesting::markLatestReadOrWriteForGlobalVar() { //called by buildReadWriteFormula
	std::cout << "create latest read and write!" << std::endl;
	std::map<string, std::vector<Event*> >::iterator iread = trace->readSet.begin();
	std::map<string, std::vector<Event*> >::iterator iwrite;

	while(iread != trace->readSet.end()) {
		iwrite = trace->writeSet.find(iread->first);
		if(iwrite == trace->writeSet.end()){
			++iread;
			continue;
		}

		std::vector<Event*>::iterator irEvent = (*iread).second.begin();
		std::vector<Event*>::iterator iwEvent = (*iwrite).second.begin();
		(*irEvent)->latestRead = NULL;
		Event* readEvent = *irEvent;
		Event* writeEvent = NULL;
		while(1){
			//mark latest write for read event;
			while(iwEvent != (*iwrite).second.end()){
				Event* tmp = writeEvent;
				if((*iwEvent)->eventId < (*irEvent)->eventId){
					writeEvent = *iwEvent;
					++iwEvent;
				} else {
					writeEvent = tmp;
					break;
				}
			}
			if(writeEvent){
				if((*irEvent)->threadId == writeEvent->threadId){
					(*irEvent)->latestWrite = writeEvent;
				} else {
					(*irEvent)->latestWrite = NULL;
				}
			} else {
				(*irEvent)->latestWrite = writeEvent; //NULL
			}

			//mark latest read for read event
			if(++irEvent != (*iread).second.end()){
				if((*irEvent)->threadId == readEvent->threadId){
					(*irEvent)->latestRead = readEvent;
				} else {
					(*irEvent)->latestRead = NULL;
				}
				readEvent = *irEvent;
			} else {
				break;
			}

		}


		iwEvent = (*iwrite).second.begin();
		irEvent = (*iread).second.begin();
		(*iwEvent)->latestWrite = NULL;
		writeEvent = *iwEvent;
		readEvent = NULL;
		while(1){
			//mark latest read for write event
			while(irEvent != (*iread).second.end()){
				Event* tmp = readEvent;
				if((*irEvent)->eventId < (*iwEvent)->eventId){
					readEvent = *irEvent;
					++irEvent;
				} else {
					readEvent = tmp;
					break;
				}
			}
			if(readEvent){
				if((*iwEvent)->threadId == readEvent->threadId){
					(*iwEvent)->latestRead = readEvent;
				} else {
					(*iwEvent)->latestRead = NULL;
				}
			} else {
				(*iwEvent)->latestRead = readEvent; //NULL
			}

			//mark latest write for write event
			if(++iwEvent != (*iwrite).second.end()){
				if((*iwEvent)->threadId == writeEvent->threadId){
					(*iwEvent)->latestWrite = writeEvent;
				} else {
					(*iwEvent)->latestWrite = NULL;
				}
				writeEvent =*iwEvent;
			} else {
				break;
			}
		}
		++iread;
	}
	//post operations
}

void CoverageBasedTesting::sortGlobalSet(std::map<std::string, std::vector<Event *> >& sourceSet) {
	std::map<std::string, std::vector<Event *> >::iterator isourceSet = sourceSet.begin();
	while(isourceSet != sourceSet.end()) {
		stable_sort(isourceSet->second.begin(), isourceSet->second.end(), less_tid);
		++isourceSet;
	}
}

/*
 * reduce readSet and writeSet
 */
void CoverageBasedTesting::reduceSet(std::map<std::string, std::vector<Event *> >& sourceSet) {
	std::map<std::string, std::vector<Event *> >::iterator it = sourceSet.begin();
	while(it != sourceSet.end()) {
		std::vector<Event *>::iterator eventIt = it->second.begin();
		while(eventIt != it->second.end()) {
			std::vector<Event *>::iterator tmpIt = eventIt + 1;
			while(tmpIt != it->second.end()) {
				if((*eventIt)->inst->info->id == (*tmpIt)->inst->info->id) {
					tmpIt = it->second.erase(tmpIt);
				} else {
					tmpIt++;
				}
			}
			eventIt++;
		}
		it++;
	}
}

void CoverageBasedTesting::setCurrentEvent(Event* event){
	this->currentEvent = event;
}

Event* CoverageBasedTesting::getCurrentEvent(){
	return this->currentEvent;
}

void CoverageBasedTesting::selectCRSet(std::vector<expr>& sourceSet){
	std::cout << "\n#################Create New Prefix, Cover multiple CR#################" << std::endl;
		std::cout << "cr set size1: " << sourceSet.size() << std::endl;

		std::vector<expr>::iterator it = sourceSet.begin();
		unsigned cnt = 0;
		while (it != sourceSet.end()) {
	//		std::cout << "the Def-Use constraint:" << std::endl;
	//		std::cout << *it << "\n" << std::endl;
			z3_solver.push();
			z3_solver.add(*it);

			check_result result;
			try {
				result = z3_solver.check();
			} catch (z3::exception& ex) {
				std::cout << "\n unexpected error: " << ex << std::endl;
				continue;
			}

			if (result == z3::sat) {
				it++;
	//			std::cout << "mark\n" << std::endl;
			}else{
				it = sourceSet.erase(it);
				++cnt;
				z3_solver.pop();
			}
		}
		std::cout << "delete " << cnt << "CR, all done" << std::endl;
		return ;
}

bool less_tid(const Event* lEvent, const Event* rEvent) {
	return lEvent->threadId < rEvent->threadId;
}

#if PRINT_OPERATION_SET_DETAILED
template <class T> struct displayVector {
		void operator()(T e) const{
			std::cout << e->toString() << endl;
		}
	};

void printOpSet(std::map<std::string, std::vector<Event*> >& opSet){
	std::map<std::string, std::vector<Event*> >::iterator im = opSet.begin();
	for(; im != opSet.end(); ++im){
		std::cout << "value name: " << im->first << "; size: "<< im->second.size() << std::endl;
		for_each(im->second.begin(), im->second.end(), displayVector<Event*>());
		std::cout << endl;
	}
}
#endif

#if PRINT_OPERATION_SET_BRIEFLY
void printOpSetBriefly(std::map<std::string, std::vector<Event*> >& opSet){
	std::map<std::string, std::vector<Event*> >::iterator im = opSet.begin();
	for(; im != opSet.end(); ++im){
		std::cout << "value name: " << im->first << "; size: "<< im->second.size() << std::endl;
		std::vector<Event*>::iterator iv = im->second.begin();
		for(; iv != im->second.end(); ++iv){
			std::cout << (*iv)->eventName << " ->-> " <<
					"line:" << (*iv)->inst->info->line <<
					" ->-> thread id: " << (*iv)->threadId << std::endl;
		}
		std::cout << endl;
	}
}
#endif

} /* namespace klee */
