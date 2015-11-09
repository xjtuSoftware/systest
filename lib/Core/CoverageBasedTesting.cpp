/*
 * CoverageBasedTesting.cpp
 *
 *  Created on: Sep 27, 2015
 *      Author: xdzhang
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
namespace klee {

CoverageBasedTesting::~CoverageBasedTesting() {
	// TODO Auto-generated destructor stub
}

void CoverageBasedTesting::buildDU() {
	std::cerr << "read set size:" << trace->readSet.size() << std::endl;
	std::cerr << "write set size:" << trace->writeSet.size() << std::endl;
#if DEBUG
	std::map<string, vector<Event *> >::iterator iRead = trace->readSet.begin();
	std::map<string, vector<Event *> >::iterator iWrite = trace->writeSet.begin();
	while(iRead != trace->readSet.end()){
		std::cerr << "read event:" << iRead->first << std::endl;
		std::vector<Event*>::iterator irEvent = iRead->second.begin();
		while(irEvent != iRead->second.end()){
			std::cerr << (*irEvent)->toString() << std::endl;
			irEvent++;
		}
		iRead++;
	}

	while(iWrite != trace->writeSet.end()){
		std::cerr << "write event:" << iWrite->first << std::endl;
		std::vector<Event*>::iterator iwEvent = iWrite->second.begin();
		while(iwEvent != iWrite->second.end()){
			std::cerr << (*iwEvent)->toString() << std::endl;
			iwEvent++;
		}
		iWrite++;
	}
#endif

	assert(trace->readSet.size() != 0 && "readSet is empty");
	markLatestWriteForGlobalVar();
//	reduceSet(trace->readSet);
//	reduceSet(trace->writeSet);

	std::map<string, vector<Event *> >::iterator ir = trace->readSet.begin(); //key--variable
	for (; ir != trace->readSet.end(); ir++) {
		map<string, vector<Event *> >::iterator iw = trace->writeSet.find(ir->first);
		//			assert(iw != trace->writeSet.end());
		if(iw == trace->writeSet.end())
			continue;
		for (unsigned k = 0; k < ir->second.size(); k++) {
			Event *currentRead;
			Event *currentWrite;
			currentRead = ir->second[k];
			expr r = z3_ctx.int_const(currentRead->eventName.c_str());
			if (currentRead->latestWrite == NULL) { //maybe read from initialization
				expr w = z3_ctx.int_const("E_INIT");
				expr def_use_order = (w < r);
				for (unsigned l = 0; l < iw->second.size(); l++) {
					if (currentRead->threadId == iw->second[l]->threadId) //can't read
						continue;
					expr otherWrite = z3_ctx.int_const(
							iw->second[l]->eventName.c_str());
					def_use_order = def_use_order && (r < otherWrite);
				}
				//build CR and insert to CRSet
				runtimeData.DUExpr.push_back(def_use_order);
//				std::cerr << "debug1" << std::endl;
//				std::cerr << def_use_order << std::endl;
//				std::cerr << currentRead->toString() << std::endl;
#if !DEBUG
				DefineUse* du = new DefineUse;
				du->pre = NULL;
				du->post = currentRead;
//				du->exprIndex = runtimeData.DUExpr.size();
//				du->flag = false;
				runtimeData.DUInfo.push_back(du);
#endif
			} else {
				for (unsigned j = 0; j < iw->second.size(); j++) {
					currentWrite = iw->second[j];
					if (currentRead->threadId == currentWrite->threadId
							&& currentRead->latestWrite != currentWrite) { //can't read
						continue;
					}
					expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
					expr def_use_order = (w < r);
					for (unsigned l = 0; l < iw->second.size(); l++) {
						if (l == j)
							continue;
						expr otherWrite = z3_ctx.int_const(
								iw->second[l]->eventName.c_str());
						expr tmp = (otherWrite < w || r < otherWrite);
						def_use_order = def_use_order && tmp;
					}
					//build CR and insert to CRSet
					runtimeData.DUExpr.push_back(def_use_order);
//					std::cerr << "debug2" << std::endl;
//					std::cerr << def_use_order << std::endl;
//					std::cerr << currentWrite->toString() << std::endl;
//					std::cerr << currentRead->toString() << std::endl;
					//use to debug
#if !DEBUG
					DefineUse* du = new DefineUse;
					du->pre = currentWrite;
					du->post = currentRead;
//					du->exprIndex = runtimeData.DUExpr.size();
//					du->flag = false;
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
	std::cerr << "Build Multiple Define-Use Pairs" << std::endl;
	assert(trace->readSet.size() != 0 && "readSet is empty");
	markLatestWriteForGlobalVar();

	std::cerr << "read set size:" << trace->readSet.size() << std::endl;
	std::cerr << "write set size:" << trace->writeSet.size() << std::endl;

#if DEBUG
	std::map<string, vector<Event *> >::iterator iRead = trace->readSet.begin();
	std::map<string, vector<Event *> >::iterator iWrite = trace->writeSet.begin();
	while(iRead != trace->readSet.end()){
		std::cerr << "read event:" << iRead->first << std::endl;
		std::vector<Event*>::iterator irEvent = iRead->second.begin();
		while(irEvent != iRead->second.end()){
			std::cerr << (*irEvent)->toString() << std::endl;
			irEvent++;
		}
		iRead++;
	}

	while(iWrite != trace->writeSet.end()){
		std::cerr << "write event:" << iWrite->first << std::endl;
		std::vector<Event*>::iterator iwEvent = iWrite->second.begin();
		while(iwEvent != iWrite->second.end()){
			std::cerr << (*iwEvent)->toString() << std::endl;
			iwEvent++;
		}
			iWrite++;
	}
#endif

		std::map<string, vector<Event*> >::iterator iRead;
		std::map<string, vector<Event*> >::iterator iWrite;

		for(iRead = trace->readSet.begin(); iRead != trace->readSet.end(); iRead++){
			std::cerr << "var name: " << iRead->first << std::endl;

			iWrite = trace->writeSet.find(iRead->first);
			if(iWrite == trace->writeSet.end()){
				continue;
			}

	//		(1)R-W-R
			for(std::vector<Event*>::iterator iREventFir = iRead->second.begin();
				iREventFir != iRead->second.end(); iREventFir++){
				for(std::vector<Event*>::iterator iREventSec = (iREventFir + 1);
							iREventSec != iRead->second.end(); iREventSec++){
					for(std::vector<Event*>::iterator iWEvent = iWrite->second.begin();
						iWEvent != iWrite->second.end(); iWEvent++){
						expr rFirExpr = z3_ctx.int_const((*iREventFir)->eventName.c_str());
						expr rSecExpr = z3_ctx.int_const((*iREventSec)->eventName.c_str());
						expr wFirExpr = z3_ctx.int_const((*iWEvent)->eventName.c_str());
						expr finalExpr1 = (rFirExpr < wFirExpr) && (wFirExpr < rSecExpr);
						expr finalExpr2 = (rSecExpr < wFirExpr) && (wFirExpr < rFirExpr);

						std::vector<Event*>::iterator iWEventTmp = iWrite->second.begin();
						while(iWEventTmp != iWEvent){
							expr tmp = z3_ctx.int_const((*iWEventTmp)->eventName.c_str());
							finalExpr1 = finalExpr1 && ((tmp < rFirExpr) || (rSecExpr < tmp));
							finalExpr2 = finalExpr2 && ((tmp < rSecExpr) || (rFirExpr < tmp));
							iWEventTmp++;
						}

						iWEventTmp++;
						while(iWEventTmp != iWrite->second.end()){
							expr tmp = z3_ctx.int_const((*iWEventTmp)->eventName.c_str());
							finalExpr1 = finalExpr1 && ((tmp < rFirExpr) || (rSecExpr < tmp));
							finalExpr2 = finalExpr2 && ((tmp < rSecExpr) || (rFirExpr < tmp));
							iWEventTmp++;
						}

						runtimeData.MAPExpr.push_back(finalExpr1);
						runtimeData.MAPExpr.push_back(finalExpr2);

						std::cerr << "(1)R-W-R（expr and event information）:" << std::endl;
						std::cerr << finalExpr1 << std::endl;
						std::cerr << finalExpr2 << std::endl;
						std::cerr << (*iREventFir)->toString() << std::endl;
						std::cerr << (*iREventSec)->toString() << std::endl;
						std::cerr << (*iWEvent)->toString() << std::endl;
					}
				}
			}

	//		(2)W-W-R;(3)R-W-W;(4)W-R-W
			for(std::vector<Event*>::iterator iWEventFir = iWrite->second.begin();
				iWEventFir != iWrite->second.end(); iWEventFir++){
				for(std::vector<Event*>::iterator iWEventSec = (iWEventFir + 1);
							iWEventSec != iWrite->second.end(); iWEventSec++){
					for(std::vector<Event*>::iterator iREvent = iRead->second.begin();
						iREvent != iRead->second.end(); iREvent++){

						expr wFirExpr = z3_ctx.int_const((*iWEventFir)->eventName.c_str());
						expr wSecExpr = z3_ctx.int_const((*iWEventSec)->eventName.c_str());
						expr rFirExpr = z3_ctx.int_const((*iREvent)->eventName.c_str());
						expr finalExpr1 = (wFirExpr < wSecExpr) && (wSecExpr < rFirExpr);
						expr finalExpr2 = (wSecExpr < wFirExpr) && (wFirExpr < rFirExpr);
						expr finalExpr3 = (rFirExpr < wFirExpr) && (wFirExpr < wSecExpr);
						expr finalExpr4 = (rFirExpr < wSecExpr) && (wSecExpr < wFirExpr);
						expr finalExpr5 = (wFirExpr < rFirExpr) && (rFirExpr < wSecExpr);
						expr finalExpr6 = (wSecExpr < rFirExpr) && (rFirExpr < wFirExpr);

						std::vector<Event*>::iterator iWEventTmp = iWrite->second.begin();
						while(iWEventTmp != iWEventFir && iWEventTmp != iWEventSec){
							expr tmp = z3_ctx.int_const((*iWEventTmp)->eventName.c_str());
							finalExpr1 = finalExpr1 && ((tmp < wFirExpr) || (rFirExpr < tmp));
							finalExpr2 = finalExpr2 && ((tmp < wSecExpr) || (rFirExpr < tmp));
							finalExpr3 = finalExpr3 && ((tmp < rFirExpr) || (wSecExpr < tmp));
							finalExpr4 = finalExpr4 && ((tmp < rFirExpr) || (wFirExpr < tmp));
							finalExpr5 = finalExpr5 && ((tmp < wFirExpr) || (wSecExpr < tmp));
							finalExpr6 = finalExpr6 && ((tmp < wSecExpr) || (wFirExpr < tmp));
							iWEventTmp++;
						}

						iWEventTmp++;
						while(iWEventTmp != iWEventFir && iWEventTmp != iWEventSec){
							expr tmp = z3_ctx.int_const((*iWEventTmp)->eventName.c_str());
							finalExpr1 = finalExpr1 && ((tmp < wFirExpr) || (rFirExpr < tmp));
							finalExpr2 = finalExpr2 && ((tmp < wSecExpr) || (rFirExpr < tmp));
							finalExpr3 = finalExpr3 && ((tmp < rFirExpr) || (wSecExpr < tmp));
							finalExpr4 = finalExpr4 && ((tmp < rFirExpr) || (wFirExpr < tmp));
							finalExpr5 = finalExpr5 && ((tmp < wFirExpr) || (wSecExpr < tmp));
							finalExpr6 = finalExpr6 && ((tmp < wSecExpr) || (wFirExpr < tmp));
							iWEventTmp++;
						}

						iWEventTmp++;
						while(iWEventTmp != iWrite->second.end()){
							expr tmp = z3_ctx.int_const((*iWEventTmp)->eventName.c_str());
							finalExpr1 = finalExpr1 && ((tmp < wFirExpr) || (rFirExpr < tmp));
							finalExpr2 = finalExpr2 && ((tmp < wSecExpr) || (rFirExpr < tmp));
							finalExpr3 = finalExpr3 && ((tmp < rFirExpr) || (wSecExpr < tmp));
							finalExpr4 = finalExpr4 && ((tmp < rFirExpr) || (wFirExpr < tmp));
							finalExpr5 = finalExpr5 && ((tmp < wFirExpr) || (wSecExpr < tmp));
							finalExpr6 = finalExpr6 && ((tmp < wSecExpr) || (wFirExpr < tmp));
							iWEventTmp++;
						}

						runtimeData.MAPExpr.push_back(finalExpr1);
						runtimeData.MAPExpr.push_back(finalExpr2);
						runtimeData.MAPExpr.push_back(finalExpr3);
						runtimeData.MAPExpr.push_back(finalExpr4);
						runtimeData.MAPExpr.push_back(finalExpr5);
						runtimeData.MAPExpr.push_back(finalExpr6);

						std::cerr << "(2)W-W-R;(3)R-W-W;(4)W-R-W（expr and event information）:" << std::endl;
						std::cerr << finalExpr1 << std::endl;
						std::cerr << finalExpr2 << std::endl;
						std::cerr << finalExpr3 << std::endl;
						std::cerr << finalExpr4 << std::endl;
						std::cerr << finalExpr5 << std::endl;
						std::cerr << finalExpr6 << std::endl;
						std::cerr << (*iWEventFir)->toString() << std::endl;
						std::cerr << (*iWEventSec)->toString() << std::endl;
						std::cerr << (*iREvent)->toString() << std::endl;
					}
				}
			}
		}
		std::cerr << "Build Multiple Define-Use Pairs ,OK." << std::endl;
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
				//
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
		coverSingleCR(runtimeData.DUExpr, runtimeData.DUInfo);
//		nonCR();
	} else if (coverageMode == 2) { //Def-Use1 and multiple CR
		coverMultipleCR(runtimeData.DUExpr);
	} else if (coverageMode == 3) { //Def-Use2 and Single CR
//		coverSingleCR(runtimeData.MAPExpr);
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
		std::cerr << "\n unexpected error: " << ex << std::endl;
		return;
	}

	if (result == z3::sat) {
		vector<Event*> vecEvent;
		generateSchedule(vecEvent);
		Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint, "");
		runtimeData.addScheduleSet(prefix);
		z3_solver.pop();
	}else {
		std::cerr << "\n unexpected error11111111111111111111111: " << std::endl;
	}
}

void CoverageBasedTesting::coverSingleCR(vector<expr>& exprVec, std::vector<DU*>& duInfo) {
	std::cerr << "Create New Prefix, Cover Single CR" << std::endl;
	std::cerr << "cr set size: " << exprVec.size() << std::endl;
	std::cerr << "du set size: " << duInfo.size() << std::endl;
	std::vector<expr>::iterator it = exprVec.begin();

	std::vector<DU*>::iterator itDU = duInfo.begin();
//	std::vector<DU*>::iterator itDU = runtimeData.DUInfo.begin();

	while (it != exprVec.end()) {
		std::cerr << "the Def-Use constraint:" << std::endl;
		std::cerr << *it << "\n" << std::endl;
//		std::cerr << (*itDU)->pre->eventName << "  " << (*itDU)->pre->toString() << std::endl;
//		std::cerr << (*itDU)->post->eventName << "  " << (*itDU)->post->toString() << std::endl;

//		std::cerr << (*itDU)->pre->eventName << "  " << (*itDU)->pre->inst->info->id << std::endl;
//		std::cerr << (*itDU)->post->eventName << "  " << (*itDU)->post->inst->info->id << std::endl;
		z3_solver.push();
		z3_solver.add(*it);

		check_result result;
		try {
			result = z3_solver.check();
		} catch (z3::exception & ex) {
			std::cerr << "\n unexpected error: " << ex << std::endl;
			continue;
		}

		if (result == z3::sat) {
			vector<Event*> vecEvent;
			try {
				generateSchedule(vecEvent);
			}
			catch (z3::exception& ex) {
				std::cerr << "\n unexpected error: " << ex << std::endl;
				assert(false && "z3 exception");
			}
			Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint, "");
			std::cerr <<"eventName: " << (*itDU)->post->eventName << "  unsigned : " << (*itDU)->post->inst->info->id << std::endl;
			unsigned br = (*itDU)->post->inst->info->id;
			prefix->setBreakEventId(br);
//			prefix->print(std::cerr);
			runtimeData.addScheduleSet(prefix);
			it = exprVec.erase(it);
			itDU = duInfo.erase(itDU);
			z3_solver.pop();
			return;
		}
		it = exprVec.erase(it);
		itDU = duInfo.erase(itDU);
		std::cerr << "delete\n" << std::endl;
		z3_solver.pop();
	}
	std::cerr << "all done" << std::endl;
	return ;
}

void CoverageBasedTesting::coverMultipleCR(vector<expr>& exprVec) {
	std::cerr << "\n#################Create New Prefix, Cover multiple CR#################" << std::endl;
	std::cerr << "cr set size: " << exprVec.size() << std::endl;

	std::vector<expr>::iterator it = exprVec.begin();
	int cnt = 0;
	while (it != exprVec.end()) {
//		std::cerr << "the Def-Use constraint:" << std::endl;
//		std::cerr << *it << "\n" << std::endl;
		z3_solver.push();
		z3_solver.add(*it);

		check_result result;
		try {
			result = z3_solver.check();
		} catch (z3::exception& ex) {
			std::cerr << "\n unexpected error: " << ex << std::endl;
			continue;
		}

		if (result == z3::sat) {
			++cnt;
			it = exprVec.erase(it);
//			std::cerr << "mark\n" << std::endl;
		}else{
			if(cnt == 0){
				it = exprVec.erase(it);
//				std::cerr << "delete\n" << std::endl;
			} else{
				it++;
//				std::cerr << "nothing\n" << std::endl;
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
		std::cerr << "\n unexpected error: " << ex << std::endl;
		assert(false && "first z3 exception");
	}

	if (result == z3::sat) {
		vector<Event*> vecEvent;
			try {
				generateSchedule(vecEvent);
			}
			catch (z3::exception& ex) {
				std::cerr << "\n unexpected error: " << ex << std::endl;
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
//		std::cerr << "\n unexpected error: " << ex << std::endl;
//		assert(false && "z3 exception");
//	}
//	Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint, "");
//	runtimeData.addScheduleSet(prefix);

	while(cnt){
		z3_solver.pop();
		--cnt;
	}

	std::cerr << "all done" << std::endl;
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
					latestWriteOneThread[event->varName] = event;
				} else if (!event->implicitGlobalVar.empty()
						&& CallInst::classof(I)) {
					for (unsigned i = 0; i < event->implicitGlobalVar.size(); i++) {
						string curr = event->implicitGlobalVar[i];
						string varName = curr.substr(0, curr.find('S', 0));
						latestWriteOneThread[varName] = event;
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

} /* namespace klee */



