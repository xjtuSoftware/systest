/*
 * PSOListener.cpp
 *
 *  Created on: May 16, 2014
 *      Author: ylc
 */

#include "PSOListener.h"
#include <iostream>
#include <fstream>
#include <unistd.h>
#include <malloc.h>
#include <string>
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/DebugInfo.h"
#else
#include "llvm/Metadata.h"
#include "llvm/Module.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/DebugInfo.h"
#endif
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include "klee/Expr.h"
#include "Encode.h"
#include "PTree.h"
#include "Trace.h"
#include "Transfer.h"
#include "KQuery2Z3.h"

using namespace std;
using namespace llvm;

#define EVENTS_DEBUG 0
#define BIT_WIDTH 32

#define PRINT_RUNTIMEINFO 0
#define DEBUGSTRCPY 0
#define DEBUGSYMBOLIC 0
#define COND_DEBUG 0
bool isPrefixFinished = false;

namespace klee {

Event* lastEvent;
std::vector<Event*>::iterator currentEvent, endEvent;
//此Map更新有三处，全局变量初始化、Store、某些函数。
std::map<std::string, ref<Expr> > symbolicMap;
std::map<string, std::vector<unsigned> > assertMap;
bool kleeBr;

PSOListener::PSOListener(Executor* executor) :
		BitcodeListener(), executor(executor), temporalVariableID(0) {
	// TODO Auto-generated constructor stub
#if PRINT_RUNTIMEINFO
	//获取当前目录绝对路径,由于executeInstruction函数执行过程中相对路径根目录会发生变化（被测程序调用chdir()）,
	//所以需要提前获取cwd,用绝对路径指定用到的输出文件
	char current_absolute_path[1000];
	if (NULL == getcwd(current_absolute_path, 1000)) {
		assert(0 && "get cwd failed\n");
	}
	this->cwd = current_absolute_path;
	this->cwd.append("/");
	this->failedTraceDir = this->cwd + "failed_trace/";
	this->redundantTraceDir = this->cwd + "redundant_trace/";
	this->uniqueTraceDir = this->cwd + "unique_trace/";
	this->prefixDir = this->cwd + "prefix/";

	//获取可执行文件位置，用于定位稍候执行的脚本preparation.sh
	char dir[300] = {0};
	int n = readlink("/proc/self/exe", dir, 300);
	string base(dir);
	base = base.substr(0, base.rfind('/') + 1);
	this->prepareShellPos = base + "preparation.sh";
	this->moveShellPos = base + "move.sh";
	string command = this->prepareShellPos + " " + this->failedTraceDir + " "
	+ this->redundantTraceDir + " " + this->uniqueTraceDir + " "
	+ this->prefixDir;
	int ret = system(command.c_str());
	assert(WIFEXITED(ret) != 0 && "preparation failed");
#endif
}

PSOListener::~PSOListener() {
	// TODO Auto-generated destructor stub
	for (map<uint64_t, BarrierInfo*>::iterator bri = barrierRecord.begin(),
			bre = barrierRecord.end(); bri != bre; bri++) {
		if (bri->second) {
			delete bri->second;
		}
	}
}

/**
 * 指令调用消息响应函数，在指令解释执行前被调用
 */
void PSOListener::executeInstruction(ExecutionState &state, KInstruction *ki) {
#if PRINT_RUNTIMEINFO
//	printInstrcution(state, ki);
	string errorMsg;
	stringstream ss;
	ss << "/home/zhy/Temp/trace.txt" << executor->executionNum;
	raw_fd_ostream out(ss.str().c_str(), errorMsg, raw_fd_ostream::F_Append);
	out << "\nthread" << state.currentThread->threadId << ": ";
	ki->inst->print(out);
	out << "------";
	switch (ki->inst->getOpcode()) {
		case Instruction::Call: {
			CallSite cs(ki->inst);
			Value *fp = cs.getCalledValue();
			Function *f = executor->getTargetFunction(fp, state);
			if (!f) {
				ref<Expr> expr = executor->eval(ki, 0, state.currentThread).value;
				ConstantExpr* constExpr = dyn_cast<ConstantExpr>(expr.get());
				uint64_t functionPtr = constExpr->getZExtValue();
				f = (Function*) functionPtr;
			}
			out << " " << f->getName().str();
			if (f->getName().str() == "pthread_mutex_lock") {
				ref<Expr> param = executor->eval(ki, 1, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			} else if (f->getName().str() == "pthread_mutex_unlock") {
				ref<Expr> param = executor->eval(ki, 1, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			} else if (f->getName().str() == "pthread_cond_wait") {
				//get lock
				ref<Expr> param = executor->eval(ki, 2, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
				//get cond
				param = executor->eval(ki, 1, state.currentThread).value;
				cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			} else if (f->getName().str() == "pthread_cond_signal") {
				ref<Expr> param = executor->eval(ki, 1, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			} else if (f->getName().str() == "pthread_cond_broadcast") {
				ref<Expr> param = executor->eval(ki, 1, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			}
			break;
		}
	}

#endif

	Trace* trace = rdManager.getCurrentTrace();
	Instruction* inst = ki->inst;
//	inst->dump();
	lastEvent = NULL;
	Thread* thread = state.currentThread;
	Event* item = NULL;
	KModule* kmodule = executor->kmodule;
	// filter the instruction linked by klee force-import such as klee_div_zero_check
	if (kmodule->kleeFunctions.find(inst->getParent()->getParent())
			== kmodule->kleeFunctions.end()
			&& kmodule->intrinsicFunctions.find(inst->getParent()->getParent())
					== kmodule->intrinsicFunctions.end()) {
		//cerr << " dir: " << dir << " file: " << file << " line: " << line << endl;
		item = trace->createEvent(thread->threadId, ki, Event::NORMAL);
	} else {
		item = trace->createEvent(thread->threadId, ki, Event::IGNORE);
	}

	vector<Event*> frontVirtualEvents, backVirtualEvents; // the virtual event which should be inserted before/behind item
	frontVirtualEvents.reserve(10);
	backVirtualEvents.reserve(10);
	switch (inst->getOpcode()) {
	case Instruction::Call: {
//		inst->dump();
		CallSite cs(inst);
		Value *fp = cs.getCalledValue();
		Function *f = executor->getTargetFunction(fp, state);
		if (!f) {
			ref<Expr> expr = executor->eval(ki, 0, thread).value;
			ConstantExpr* constExpr = dyn_cast<ConstantExpr>(expr.get());
			uint64_t functionPtr = constExpr->getZExtValue();
			f = (Function*) functionPtr;
		}
//		if (executor->kmodule->functionMap.find(f) == executor->kmodule->functionMap.end()) {
//			assert(0 && "function not exist");
//		}
		item->calledFunction = f;
		if (f && f->isDeclaration() &&
				f->getIntrinsicID() == Intrinsic::not_intrinsic
//				&& !f->isDeclaration()
//				&& kmodule->kleeFunctions.find(f)
//						== kmodule->kleeFunctions.end()
//				&& kmodule->intrinsicFunctions.find(f)
//						== kmodule->intrinsicFunctions.end()
		) {

			item->isFunctionWithSourceCode = false;
		}

		//by hy
		//store all call arg
		if (!item->isFunctionWithSourceCode) {
			unsigned numArgs = cs.arg_size();
			item->value.reserve(numArgs);
			for (unsigned j = 0; j < numArgs; ++j) {
				item->value.push_back(executor->eval(ki, j + 1, thread).value);
			}
		}
//		std::cerr<<"call name : "<< f->getName().str().c_str() <<"\n";
//		if(f->getName().str() == "open"){
//			cerr<<f->getName().str()<<"\n";
//			ref<Expr> Address = executor->eval(ki, 1, thread).value;
//			ObjectPair op;
//			getMemoryObject(op, state, Address);
//			const ObjectState* destos = op.second;
//			const MemoryObject* mo = op.first;
//			Expr::Width size = 8;
//			int i = 0;
//			for ( ; i < mo->size; i++) {
//				ref<Expr> value = destos->read(i, size);
//				if(value->isZero()){
//					break;
//				}
//						ConstantExpr *value1 = cast<ConstantExpr>(value);
//						uint64_t scraddress = value1->getZExtValue();
//						char valuec = scraddress;
//					std::cerr<<"value : "<<valuec<<std::endl;
//			}
//		}
		if (f->getName().str() == "pthread_create") {
//			CallInst* calli = dyn_cast<CallInst>(inst);
//			assert(
//					calli->getNumArgOperands() == 4
//							&& "pthread_create has 4 params");
//			Value* threadEntranceFP = calli->getArgOperand(2);
//			Function *threadEntrance = executor->getTargetFunction(
//					threadEntranceFP, state);
//			if (!threadEntrance) {
//				ref<Expr> param = executor->eval(ki, 3, thread).value;
//				ConstantExpr* functionPtr = dyn_cast<ConstantExpr>(param);
//				threadEntrance = (Function*)(functionPtr->getZExtValue());
//				//assert(0 && "thread entrance not exist");
//				//						KFunction *kf =
//				//								executor->kmodule->functionMap[threadEntrance];
//				//runtime.pushStackFrame(kf->function, kf->numRegisters, executor->nextThreadId);
//			}
			ref<Expr> pthreadAddress = executor->eval(ki, 1,
					state.currentThread).value;
			ObjectPair pthreadop;
			bool success = getMemoryObject(pthreadop, state, pthreadAddress);
			if (success) {
				const ObjectState* pthreados = pthreadop.second;
				const MemoryObject* pthreadmo = pthreadop.first;
				if (isGlobalMO(pthreadmo)) {
					item->isGlobal = true;
				} else {
					item->isLocal = true;
				}
				string varName = createVarName(pthreadmo->id, pthreadAddress,
						item->isGlobal);
				item->varName = varName;
			}
		} else if (f->getName().str() == "pthread_join") {
			CallInst* calli = dyn_cast<CallInst>(inst);
			IntegerType* paramType =
					(IntegerType*) (calli->getArgOperand(0)->getType());
			ref<Expr> param = executor->eval(ki, 1, thread).value;
			ConstantExpr* joinedThreadIdExpr = dyn_cast<ConstantExpr>(param);
			uint64_t joinedThreadId = joinedThreadIdExpr->getZExtValue(
					paramType->getBitWidth());
			trace->insertThreadCreateOrJoin(make_pair(item, joinedThreadId),
					false);
		} else if (f->getName().str() == "pthread_cond_wait") {
			ref<Expr> param;
			ObjectPair op;
			Event *lock, *unlock;
			bool success;
			//get lock
			param = executor->eval(ki, 2, thread).value;
			success = getMemoryObject(op, state, param);
			if (success) {
				const MemoryObject* mo = op.first;
				string mutexName = createVarName(mo->id, param, isGlobalMO(mo));
//				unlock = trace->createEvent(thread->threadId, ki,
//						Event::VIRTUAL);
//				unlock->calledFunction = f;
//				string temp = item->eventName;
//				item->eventName = unlock->eventName;
//				unlock->eventName = temp;
//				unlock->eventName = item->eventName;
//				frontVirtualEvents.push_back(unlock);
				lock = trace->createEvent(thread->threadId, ki, Event::VIRTUAL);
				lock->calledFunction = f;
				backVirtualEvents.push_back(lock);
				trace->insertLockOrUnlock(thread->threadId, mutexName, item,
						false);
				trace->insertLockOrUnlock(thread->threadId, mutexName, lock,
						true);
				item->mutexName = mutexName;
			} else {
				assert(0 && "mutex not exist");
			}
			//get cond
			param = executor->eval(ki, 1, thread).value;
			success = getMemoryObject(op, state, param);
			if (success) {
				const MemoryObject* mo = op.first;
				string condName = createVarName(mo->id, param, isGlobalMO(mo));
				trace->insertWait(condName, item, lock);
				item->condName = condName;
			} else {
				assert(0 && "cond not exist");
			}
#if COND_DEBUG
			ki->inst->dump();
			cerr << "event name : " << item->eventName << "\n";
			cerr << "wait : " << item->condName << "\n";
#endif
		} else if (f->getName().str() == "pthread_cond_signal") {
			ref<Expr> param = executor->eval(ki, 1, thread).value;
			ObjectPair op;
			bool success = getMemoryObject(op, state, param);
			if (success) {
				const MemoryObject* mo = op.first;
				string condName = createVarName(mo->id, param, isGlobalMO(mo));
				trace->insertSignal(condName, item);
				item->condName = condName;
			} else {
				assert(0 && "cond not exist");
			}
#if COND_DEBUG
			ki->inst->dump();
			cerr << "event name : " << item->eventName << "\n";
			cerr << "signal  : " << item->condName << "\n";
#endif
		} else if (f->getName().str() == "pthread_cond_broadcast") {
			ref<Expr> param = executor->eval(ki, 1, thread).value;
			ObjectPair op;
			bool success = getMemoryObject(op, state, param);
			if (success) {
				const MemoryObject* mo = op.first;
				string condName = createVarName(mo->id, param, isGlobalMO(mo));
				trace->insertSignal(condName, item);
				item->condName = condName;
			} else {
				assert(0 && "cond not exist");
			}
#if COND_DEBUG
			ki->inst->dump();
			cerr << "event name : " << item->eventName << "\n";
			cerr << "broadcast cond  : " << item->condName << "\n";
#endif
		} else if (f->getName().str() == "pthread_mutex_lock") {
			ref<Expr> param = executor->eval(ki, 1, thread).value;
			ObjectPair op;
			bool success = getMemoryObject(op, state, param);
			if (success) {
				const MemoryObject* mo = op.first;
				string mutexName = createVarName(mo->id, param, isGlobalMO(mo));
				trace->insertLockOrUnlock(thread->threadId, mutexName, item,
						true);
				item->mutexName = mutexName;
			} else {
				assert(0 && "mutex not exist");
			}
		} else if (f->getName().str() == "pthread_mutex_unlock") {
			ref<Expr> param = executor->eval(ki, 1, thread).value;
			ObjectPair op;
			bool success = getMemoryObject(op, state, param);
			if (success) {
				const MemoryObject* mo = op.first;
				string mutexName = createVarName(mo->id, param, isGlobalMO(mo));
				trace->insertLockOrUnlock(thread->threadId, mutexName, item,
						false);
				item->mutexName = mutexName;
			} else {
				assert(0 && "mutex not exist");
			}
		} else if (f->getName().str() == "pthread_barrier_wait") {
			ref<Expr> param = executor->eval(ki, 1, thread).value;
			ConstantExpr* barrierAddressExpr = dyn_cast<ConstantExpr>(param);
			uint64_t barrierAddress = barrierAddressExpr->getZExtValue();
			map<uint64_t, BarrierInfo*>::iterator bri = barrierRecord.find(
					barrierAddress);
			BarrierInfo* barrierInfo = NULL;
			if (bri == barrierRecord.end()) {
				barrierInfo = new BarrierInfo();
				barrierRecord.insert(make_pair(barrierAddress, barrierInfo));
			} else {
				barrierInfo = bri->second;
			}
			string barrierName = createBarrierName(barrierAddress,
					barrierInfo->releasedCount);
			trace->insertBarrierOperation(barrierName, item);
			//					cerr << "insert " << barrierName << " " << item->eventName << endl;
			bool isReleased = barrierInfo->addWaitItem();
			if (isReleased) {
				barrierInfo->addReleaseItem();
			}
		} else if (f->getName().str() == "pthread_barrier_init") {
			ref<Expr> param = executor->eval(ki, 1, thread).value;
			ConstantExpr* barrierAddressExpr = dyn_cast<ConstantExpr>(param);
			uint64_t barrierAddress = barrierAddressExpr->getZExtValue();
			map<uint64_t, BarrierInfo*>::iterator bri = barrierRecord.find(
					barrierAddress);
			BarrierInfo* barrierInfo = NULL;
			if (bri == barrierRecord.end()) {
				barrierInfo = new BarrierInfo();
				barrierRecord.insert(make_pair(barrierAddress, barrierInfo));
			} else {
				barrierInfo = bri->second;
			}

			param = executor->eval(ki, 3, thread).value;
			ConstantExpr* countExpr = dyn_cast<ConstantExpr>(param);
			barrierInfo->count = countExpr->getZExtValue();
			//				} else if (f->getName().str() == "printf") {
			//					//find variable used in printf and insert its value into rdManaget
			//					// have serious bug! need to repair!
			//					//ylc
			//					CallInst* calli = dyn_cast<CallInst>(inst);
			//					unsigned argNum = calli->getNumArgOperands();
			//					//printf is external, having no element in stack, so the top of stack is the caller
			//					KFunction* kf = state.stack.back().kf;
			//					//skip the first param : format
			//					for (unsigned i = 1; i < argNum; i++) {
			//						ref<Expr> param = executor->eval(ki, i + 1, state).value;
			//						Type* paramType = calli->getArgOperand(i)->getType();
			//						Constant* constant = expr2Constant(param.get(),
			//								paramType);
			//						int index = ki->operands[i + 1]
			//								- kf->function->arg_size();
			//						KInstruction* paramLoad = kf->instructions[index];
			//						string name;
			//						if (paramLoad->inst->getOpcode() == Instruction::Load) {
			//							ref<Expr> address = executor->eval(paramLoad, 0,
			//									state).value;
			//							ObjectPair op;
			//							bool success = getMemoryObject(op, state, address);
			//							if (success) {
			//								const MemoryObject *mo = op.first;
			//								name = createVarName(mo->id, address,
			//										isGlobalMO(mo));
			//							} else {
			//								assert(0 && "resolve param address failed");
			//							}
			//						} else {
			//							name = createTemporalName();
			//						}
			//						item->outputParams.push_back(constant);
			//						rdManager.insertPrintfParam(name, constant);
			//					}
		}else if (kmodule->kleeFunctions.find(f)
				!= kmodule->kleeFunctions.end()) {
			item->eventType = Event::IGNORE;
		}
		//cerr << item->calledFunction->getName().str() << " " << item->isUserDefinedFunction << endl;
		break;
	}

	case Instruction::Ret: {
		//runtime.popStackFrame(state.threadId);
		break;
	}

	case Instruction::Add: {
		break;
	}

	case Instruction::Sub: {
		break;
	}

	case Instruction::Mul: {
		break;
	}

	case Instruction::GetElementPtr: {
		//对于对数组解引用的GetElementPtr，获取其所有元素的地址，存放在Event中
		//目前只处理一维数组,多维数组及指针数组赞不考虑，该处理函数存在问题
		//ylc
		GetElementPtrInst* gp = dyn_cast<GetElementPtrInst>(inst);
		KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
		for (std::vector<std::pair<unsigned, uint64_t> >::iterator it =
				kgepi->indices.begin(), ie = kgepi->indices.end(); it != ie;
				++it) {
			ref<Expr> index = executor->eval(ki, it->first, thread).value;
			item->value.push_back(index);
		}
		if (kgepi->offset) {
			item->value.push_back(ConstantExpr::create(kgepi->offset, 64));
		}
		Type* pointedTy =
				gp->getPointerOperand()->getType()->getPointerElementType();
		switch (pointedTy->getTypeID()) {
		case Type::ArrayTyID: {
			//只处理索引值是变量的getElementPtr属性，因为索引值是常量时其访问的元素不会随线程交织变化
			if (inst->getOperand(2)->getValueID() != Value::ConstantIntVal) {
				uint64_t num = pointedTy->getArrayNumElements();
				uint64_t elementBitWidth =
						executor->kmodule->targetData->getTypeSizeInBits(
								pointedTy->getArrayElementType());
				Expr* expr = executor->eval(ki, 0, thread).value.get();
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(expr);
				uint64_t base = cexpr->getZExtValue();
				expr = executor->eval(ki, 2, thread).value.get();
				cexpr = dyn_cast<ConstantExpr>(expr);
				uint64_t selectedIndex = cexpr->getZExtValue();
				VectorInfo* vectorInfo = new VectorInfo(base, elementBitWidth,
						num, selectedIndex);
				item->vectorInfo = vectorInfo;
				getElementPtrRecord.insert(std::make_pair(inst, vectorInfo));
			}
			break;
		}

		case Type::HalfTyID:
		case Type::FloatTyID:
		case Type::DoubleTyID:
		case Type::X86_FP80TyID:
		case Type::FP128TyID:
		case Type::PPC_FP128TyID:
		case Type::IntegerTyID: {
			if (inst->getOperand(1)->getValueID() != Value::ConstantIntVal) {
				Type* pointedTy =
						inst->getOperand(0)->getType()->getPointerElementType();
				uint64_t elementBitWidth =
						executor->kmodule->targetData->getTypeSizeInBits(
								pointedTy);
				Expr* expr = executor->eval(ki, 0, thread).value.get();
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(expr);
				uint64_t base = cexpr->getZExtValue();
				expr = executor->eval(ki, 1, thread).value.get();
				cexpr = dyn_cast<ConstantExpr>(expr);
				uint64_t index = cexpr->getZExtValue();
				uint64_t startAddress = base + index * elementBitWidth / 8;
				ObjectPair op;
//				cerr << "base = " << base << " index = " << index << " startAddress = " << startAddress << " pointerWidth = " << Context::get().getPointerWidth() << endl;
				bool success = getMemoryObject(op, state,
						ConstantExpr::create(startAddress,
								Context::get().getPointerWidth()));
				if (success) {
					const MemoryObject* mo = op.first;
					uint64_t elementNum = mo->size / (elementBitWidth / 8);
					if (elementNum > 1) {
						uint64_t selectedIndex = (startAddress - mo->address)
								/ (elementBitWidth / 8);
						VectorInfo* vectorInfo = new VectorInfo(mo->address,
								elementBitWidth, elementNum, selectedIndex);
						item->vectorInfo = vectorInfo;
						getElementPtrRecord.insert(
								std::make_pair(inst, vectorInfo));
					}
				} else {
					inst->dump();
					cerr << "access address: " << startAddress
							<< "has not been allocated" << endl;
					//assert(0 && "the address has not been allocated");
				}
			}
			break;
		}

		default: {
			//cerr << "unhandled type " << pointedTy->getTypeID() << endl;
		}

		}
		break;
	}

	case Instruction::ICmp: {
		break;
	}

	case Instruction::BitCast: {
		break;
	}

	case Instruction::PHI: {
		break;
	}

	case Instruction::Br: {
		BranchInst *bi = dyn_cast<BranchInst>(inst);
		if (!bi->isUnconditional()) {
			item->isConditionIns = true;
			ref<Expr> param = executor->eval(ki, 0, thread).value;
			ConstantExpr* condition = dyn_cast<ConstantExpr>(param);
			if (condition->isTrue()) {
				item->condition = true;
			} else {
				item->condition = false;
			}
		}
		break;
	}

	case Instruction::Load: {
		LoadInst* li = dyn_cast<LoadInst>(ki->inst);
		if (li->getPointerOperand()->getName().equals("stdout")
				|| li->getPointerOperand()->getName().equals("stderr")) {
			item->eventType = Event::IGNORE;
		} else {
			ref<Expr> address = executor->eval(ki, 0, thread).value;
			ConstantExpr* realAddress = dyn_cast<ConstantExpr>(address.get());
			if (realAddress) {
				Expr::Width size = executor->getWidthForLLVMType(
						ki->inst->getType());
				ref<Expr> value = readExpr(state, address, size);
//				cerr << "load value : " << value << "\n";
				uint64_t key = realAddress->getZExtValue();
				ObjectPair op;
				bool success = getMemoryObject(op, state, address);
				if (success) {
					const MemoryObject *mo = op.first;
					if (isGlobalMO(mo)) {
						item->isGlobal = true;
//						if(mo->isArg){
//							item->isArg = 1;
//						}
					} else {
						item->isLocal = true;
					}
					//					if (mo->isGlobal) {
					//						insertGlobalVariable(address, inst->getOperand(0)->getType()->getPointerElementType());
					//					}
					string varName = createVarName(mo->id, address,
							item->isGlobal);
					string varFullName;
					if (item->isGlobal) {
						unsigned loadTime = getLoadTime(key);
						varFullName = createGlobalVarFullName(varName, loadTime,
								false);
					}
					item->globalVarFullName = varFullName;
					item->varName = varName;
					if (!inst->getType()->isPointerTy() && item->isGlobal) {
						trace->insertReadSet(varName, item);
					}
					if (inst->getOperand(0)->getValueID()
							== Value::InstructionVal
									+ Instruction::GetElementPtr) {
						Instruction* i = dyn_cast<Instruction>(
								inst->getOperand(0));
						map<Instruction*, VectorInfo*>::iterator gi =
								getElementPtrRecord.find(i);
						if (gi != getElementPtrRecord.end()) {
							item->vectorInfo = gi->second;
						}
					}
					//					if (item->vectorInfo) {
					//						vector<uint64_t> v = item->vectorInfo->getAllPossibleAddress();
					//						for(vector<uint64_t>::iterator vi = v.begin(), ve = v.end(); vi != ve; vi++) {
					//							cerr << *vi << " ";
					//						}
					//						cerr << endl;
					//					}
					//					cerr << "address = " << realAddress->getZExtValue() << endl;
				} else {
					cerr << "Load address = " << realAddress->getZExtValue() << endl;
					assert(0 && "load resolve unsuccess");
				}
			} else {
				assert(0 && " address is not const");
			}
		}
		break;
	}

	case Instruction::Store: {
		ref<Expr> value = executor->eval(ki, 0, thread).value;
		item->value.push_back(value);
		ref<Expr> address = executor->eval(ki, 1, thread).value;
		ConstantExpr* realAddress = dyn_cast<ConstantExpr>(address.get());
		if (realAddress) {
			uint64_t key = realAddress->getZExtValue();
			ObjectPair op;
			bool success = getMemoryObject(op, state, address);
			if (success) {
				const MemoryObject *mo = op.first;
				if (isGlobalMO(mo)) {
					item->isGlobal = true;
				} else {
					item->isLocal = true;
				}
				//					if (mo->isGlobal) {
				//						insertGlobalVariable(address, inst->getOperand(1)->getType()->getPointerElementType());
				//					}
				string varName = createVarName(mo->id, address, item->isGlobal);
				string varFullName;
				if (item->isGlobal) {
					unsigned storeTime = getStoreTime(key);
					varFullName = createGlobalVarFullName(varName, storeTime,
							true);
				}
				item->globalVarFullName = varFullName;
				item->varName = varName;
				if (!inst->getOperand(0)->getType()->isPointerTy()
						&& item->isGlobal) {
					trace->insertWriteSet(varName, item);
				}
				if (inst->getOperand(1)->getValueID()
						== Value::InstructionVal + Instruction::GetElementPtr) {
					Instruction* i = dyn_cast<Instruction>(inst->getOperand(1));
					map<Instruction*, VectorInfo*>::iterator gi =
							getElementPtrRecord.find(i);
					if (gi != getElementPtrRecord.end()) {
						item->vectorInfo = gi->second;
					}
				}
				//					if (item->vectorInfo) {
				//						vector<uint64_t> v = item->vectorInfo->getAllPossibleAddress();
				//						for(vector<uint64_t>::iterator vi = v.begin(), ve = v.end(); vi != ve; vi++) {
				//							cerr << *vi << " ";
				//						}
				//						cerr << endl;
				//					}
				//					cerr << "address = " << realAddress->getZExtValue() << endl;
			} else {
				cerr << "Store address = " << realAddress->getZExtValue() << endl;
				assert(0 && "store resolve unsuccess");
			}
		} else {
			assert(0 && " address is not const");
		}
		break;
	}
	case Instruction::Switch: {
		SwitchInst *si = cast<SwitchInst>(inst);
		ref<Expr> cond = executor->eval(ki, 0, thread).value;
		item->value.push_back(cond);
		break;
	}

	default: {
		//			cerr << inst->getOpcodeName();
		//			assert(0 && "unsupport");
		break;
	}

	}
	//runtime.printRunTime();
	for (vector<Event*>::iterator ei = frontVirtualEvents.begin(), ee =
			frontVirtualEvents.end(); ei != ee; ei++) {
		trace->insertEvent(*ei, thread->threadId);
	}
	trace->insertEvent(item, thread->threadId);
	for (vector<Event*>::iterator ei = backVirtualEvents.begin(), ee =
			backVirtualEvents.end(); ei != ee; ei++) {
		trace->insertEvent(*ei, thread->threadId);
	}
	trace->insertPath(item);
	lastEvent = item;
}

/**
 * 指令调用消息响应函数，在指令解释执行之后调用
 */
void PSOListener::instructionExecuted(ExecutionState &state, KInstruction *ki) {
	if (lastEvent) {
		Instruction* inst = ki->inst;
		Thread* thread = state.currentThread;
		switch (inst->getOpcode()) {

		case Instruction::Switch: {
			BasicBlock* bb = thread->pc->inst->getParent();
			SwitchInst* si = dyn_cast<SwitchInst>(ki->inst);
			unsigned bbIndex = 0;
			bool isDefault = true;
			for (SwitchInst::CaseIt sci = si->case_begin(), sce =
					si->case_end(); sci != sce; sci++) {
				bbIndex++;
				if (sci.getCaseSuccessor() == bb) {
					isDefault = false;
					break;
				}
			}
			//对于switch语句的default块，index标记为-1
			if (isDefault) {
				bbIndex = 0;
			}
			break;
		}

		case Instruction::Ret: {
//			if (executor->isAllThreadTerminate()) {
//				for (map<uint64_t, Type*>::iterator mi =
//						usedGlobalVariableRecord.begin(), me =
//						usedGlobalVariableRecord.end(); mi != me; mi++) {
//					ObjectPair op;
//					//					cerr << mi->second->getTypeID() << endl;
//					ref<ConstantExpr> address = ConstantExpr::alloc(mi->first,
//							Context::get().getPointerWidth());
//					getMemoryObject(op, state, address);
//					ref<Expr> value = getExprFromMemory(address, op,
//							mi->second);
//					rdManager.insertGlobalVariableLast(
//							createVarName(op.first->id, address, true),
//							expr2Constant(value.get(), mi->second));
//				}
//			}
			break;
		}

		case Instruction::Call: {
			Constant* returnValue = handleFunctionReturnValue(state, ki);
			if (returnValue) {
			}
			handleExternalFunction(state, ki);
			break;
		}

		case Instruction::Load: {
			break;
		}

		case Instruction::Store: {
			break;
		}

		case Instruction::GetElementPtr: {
			break;
		}

		}
	}
}

/**
 * 消息响应函数，在被测程序解释执行之前调用
 */
void PSOListener::beforeRunMethodAsMain(ExecutionState &initialState) {
	//push main function's stackframe
//	KFunction* kf = initialState.stack[0].kf;
	//runtime.pushStackFrame(kf->function, kf->numRegisters, initialState.threadId);

	//statics
	gettimeofday(&start, NULL);
	//收集全局变量初始化值
	Trace* trace = rdManager.createNewTrace(executor->executionNum);
	Module* m = executor->kmodule->module;
	for (Module::global_iterator i = m->global_begin(), e = m->global_end();
			i != e; ++i) {
		if (i->hasInitializer() && i->getName().str().at(0) != '.') {
			MemoryObject *mo = executor->globalObjects.find(i)->second;
			Constant* initializer = i->getInitializer();
			uint64_t address = mo->address;
//			cerr << i->getName().str() << " " << initializer->getType()->getTypeID() << endl;
			handleInitializer(initializer, mo, address);
		}
	}
	for (std::vector<KFunction*>::iterator i =
			executor->kmodule->functions.begin(), e =
			executor->kmodule->functions.end(); i != e; ++i) {
		KInstruction **instructions = (*i)->instructions;
		for (unsigned j = 0; j < (*i)->numInstructions; j++) {
			KInstruction *ki=instructions[j];
			Instruction* inst = ki->inst;
//			instructions[j]->inst->dump();
			if (inst->getOpcode() == Instruction::Call) {
				CallSite cs(inst);
				Value *fp = cs.getCalledValue();
				Function *f = executor->getTargetFunction(fp, initialState);
				if (f && f->getName().str() == "__assert_fail") {
					string fileName = ki->info->file;
					unsigned line = ki->info->line;
					assertMap[fileName].push_back(line);
//					printf("fileName : %s, line : %d\n",fileName.c_str(),line);
//					std::cerr << "call name : " << f->getName().str() << "\n";
				}
			}
		}
	}
	//获取argc，argv
//	StackFrame sf = initialState.currentThread->stack.back();
//	Function* main = sf.kf->function;
//	Function::arg_iterator ai = main->arg_begin(), ae = main->arg_end();
//	if (ai != ae) {
//		// handle argc
//		ref<Expr> value = sf.locals[0].value;
//		ConstantExpr* cexpr = dyn_cast < ConstantExpr > (value);
//		uint64_t argc = cexpr->getZExtValue();
////		trace->insertArgc(argc);
//		//ConstantInt* ci = ConstantInt::get(type, argc, true);
//		if (++ai != ae) {
//			//handle argv  ignore env
//			value = sf.locals[1].value;
//			cexpr = dyn_cast < ConstantExpr > (value);
//			ObjectPair op;
//			getMemoryObject(op, initialState, cexpr);
//			const MemoryObject* mo = op.first;
//			const ObjectState* os = op.second;
//			unsigned ptrBytes = Context::get().getPointerWidth() / 8;
//			IntegerType* chTy =
//					dyn_cast < IntegerType
//							> (ai->getType()->getPointerElementType()->getPointerElementType());
//			for (unsigned i = 0; i < argc; i++) {
//				uint64_t address = mo->address + i * ptrBytes;
//				ref<Expr> offset = mo->getOffsetExpr(
//						ConstantExpr::create(address,
//								Context::get().getPointerWidth()));
//				ref<Expr> result = os->read(offset,
//						Context::get().getPointerWidth());
//				cexpr = dyn_cast < ConstantExpr > (result.get());
//				ObjectPair arg;
//				getMemoryObject(arg, initialState, cexpr);
//				const MemoryObject* argMo = arg.first;
//				const ObjectState* argOs = arg.second;
//				for (unsigned j = 0; j < argMo->size; j++) {
//					ref<Expr> ch = argOs->read(j, 8);
//					cexpr = dyn_cast < ConstantExpr > (ch.get());
//					string name = createVarName(argMo->id, argMo->address + j,
//							isGlobalMO(argMo));
//					ConstantInt* ci = ConstantInt::get(chTy,
//							cexpr->getZExtValue(), true);
//					trace->insertGlobalVariableInitializer(name, ci);
//				}
//
//			}
//		}
//	}

	//
	unsigned traceNum = executor->executionNum;
	cerr << endl;
	cerr
			<< "************************************************************************\n";
	cerr << "第" << traceNum << "次执行,路径文件为trace" << traceNum << ".txt";
	if (traceNum == 0) {
		cerr << " 初始执行" << endl;
	} else {
		cerr << " 前缀执行,前缀文件为prefix" << executor->prefix->getName() << ".txt"
				<< endl;
	}
	cerr
			<< "************************************************************************\n";
	cerr << endl;
#if PRINT_RUNTIMEINFO
	printPrefix();
#endif
}

/**
 * 消息响应函数，在被测程序解释执行之后调用
 */
void PSOListener::afterRunMethodAsMain() {
	//TODO: Add Encoding Feature
	//statics
	gettimeofday(&finish, NULL);
	double cost = (double) (finish.tv_sec * 1000000UL + finish.tv_usec
			- start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
	rdManager.addStaticsInfo(0.0, cost, 0, 0);
	CoverageBasedTesting cbt(rdManager, 1, 1);

//	Trace* trace = rdManager.getCurrentTrace();
//	std::cerr << "print all event:\n";
//	trace->printAllEvent(std::cerr);
//	std::cerr << "print end.\n";


	if (executor->isSymbolicRun == 0) {
		if (executor->execStatus != Executor::SUCCESS) {
			std::cerr << "######################上述为第" << executor->executionNum << "次执行，执行有错误,放弃####################\n";
			std::cerr << "\n######################下面开始第" << executor->executionNum + 1 << "次执行####################\n";
			executor->isFinished = true;
//			assert(0 && "debug");
//			executor->execStatus = Executor::IGNOREDERROR;
//			cbt.computeNewSchedule();
			getNewPrefix();
		} else if (!rdManager.isCurrentTraceUntested()){
			rdManager.getCurrentTrace()->traceType = Trace::REDUNDANT;
			std::cerr << "######################上述为第" << executor->executionNum << "次执行，执行正确####################\n";
			std::cerr << "\n######################下面开始第" << executor->executionNum + 1 << "次执行####################\n";
			cbt.computeNewSchedule();
			getNewPrefix();
		} else {
			executor->isSymbolicRun = 1;
		}
	} else if (executor->isSymbolicRun == 1) {
//		assert(0);
		rdManager.getCurrentTrace()->traceType = Trace::UNIQUE;
		Encode encode(rdManager, rdManager.z3_ctx, rdManager.z3_solver);
		encode.buildAllFormula();
		cbt.buildCoverageRequirement();
		std::cerr << "######################下面开始第" << executor->executionNum + 1<< "次执行####################\n";
		cbt.computeNewSchedule();
		getNewPrefix();
	}

#if PRINT_RUNTIMEINFO
	//移动trace文件到对应的文件夹
	string fileName = cwd + "/trace"
	+ Transfer::uint64toString(rdManager.getCurrentTrace()->Id)
	+ ".txt";
	string command;
	command.append(moveShellPos);
	command.append(" ");
	command.append(fileName);
	command.append(" ");
	switch (rdManager.getCurrentTrace()->traceType) {
		case Trace::FAILED: {
			command.append(failedTraceDir);
			break;
		}

		case Trace::REDUNDANT: {
			command.append(redundantTraceDir);
			break;
		}

		case Trace::UNIQUE: {
			command.append(uniqueTraceDir);
			break;
		}

	}

	int ret = system(command.c_str());
	assert(WIFEXITED(ret) != 0 && "move failed");
//	rdManager.printAllPrefix(cerr);
#endif

//	unsigned mbs = 0;
//	  	struct mallinfo mi = ::mallinfo();
//	  	#if defined(__GLIBC__)
//	  	mbs = mi.uordblks + mi.hblkhd;
//	  	#else
//	  	mbs = mi.uordblks;
//	  	#endif
//	//  	mbs = mbs >> 20;
//	  	cout << "Memory cost: " << mbs << "\n5555555555555555555555555\n";
}

/**
 * 获取address对应的ObjectPair
 */
bool PSOListener::getMemoryObject(ObjectPair& op, ExecutionState& state,
		ref<Expr> address) {
	TimingSolver* solver = executor->getTimeSolver();
	bool success;
	if (!state.addressSpace.resolveOne(state, solver, address, op, success)) {
		address = executor->toConstant(state, address, "resolveOne failure");
		success = state.addressSpace.resolveOne(cast<ConstantExpr>(address),
				op);
	}
	return success;
}

/**
 * 处理全局函数初始值
 */
void PSOListener::handleInitializer(Constant* initializer, MemoryObject* mo,
		uint64_t& startAddress) {
	Trace* trace = rdManager.getCurrentTrace();
	DataLayout* layout = executor->kmodule->targetData;
	if (dyn_cast<ConstantInt>(initializer)) {
		Type* type = initializer->getType();
		unsigned alignment = layout->getABITypeAlignment(type);
		if (startAddress % alignment != 0) {
			startAddress = (startAddress / alignment + 1) * alignment;
		}
		string globalVariableName = createVarName(mo->id, startAddress,
				isGlobalMO(mo));
		trace->insertGlobalVariableInitializer(globalVariableName, initializer);
//		cerr << "globalVariableName : " << globalVariableName << "    value : "
//				<< executor->evalConstant(initializer) << "\n";
		symbolicMap[globalVariableName] = executor->evalConstant(initializer);
		//startAddress += TypeUtils::getPrimitiveTypeWidth(type);
		startAddress += executor->kmodule->targetData->getTypeSizeInBits(type)
				/ 8;
	} else if (dyn_cast<ConstantFP>(initializer)) {
		Type* type = initializer->getType();
		unsigned alignment = layout->getABITypeAlignment(type);
		if (startAddress % alignment != 0) {
			startAddress = (startAddress / alignment + 1) * alignment;
		}
		string globalVariableName = createVarName(mo->id, startAddress,
				isGlobalMO(mo));
		trace->insertGlobalVariableInitializer(globalVariableName, initializer);
//		cerr << "globalVariableName : " << globalVariableName << "    value : "
//				<< executor->evalConstant(initializer) << "\n";
		symbolicMap[globalVariableName] = executor->evalConstant(initializer);
		//startAddress += TypeUtils::getPrimitiveTypeWidth(type);
		startAddress += executor->kmodule->targetData->getTypeSizeInBits(type)
				/ 8;
	} else if (ConstantDataArray* carray = dyn_cast<ConstantDataArray>(
			initializer)) {
		ArrayType* arrayType = carray->getType();
		uint64_t elementNum = arrayType->getNumElements();
		for (unsigned index = 0; index < elementNum; index++) {
			Constant* element = carray->getAggregateElement(index);
			handleInitializer(element, mo, startAddress);
		}
	} else if (ConstantAggregateZero* caggregate = dyn_cast<
			ConstantAggregateZero>(initializer)) {
		uint64_t elementNum;
		switch (caggregate->getType()->getTypeID()) {

		case Type::StructTyID: {
			StructType* structType = dyn_cast<StructType>(
					caggregate->getType());
			if (structType->getStructName() == "union.pthread_mutex_t"
					|| structType->getStructName() == "union.pthread_cond_t"
					|| structType->getStructName()
							== "union.pthread_barrier_t") {
				unsigned alignment = layout->getABITypeAlignment(structType);
				if (startAddress % alignment != 0) {
					startAddress = (startAddress / alignment + 1) * alignment;
				}
				startAddress +=
						executor->kmodule->targetData->getTypeSizeInBits(
								structType) / 8;
			} else {
				elementNum = caggregate->getType()->getStructNumElements();
				for (unsigned index = 0; index < elementNum; index++) {
					Constant* element = caggregate->getAggregateElement(index);
					handleInitializer(element, mo, startAddress);
				}
			}

			break;
		}

		case Type::ArrayTyID: {
			elementNum = caggregate->getType()->getArrayNumElements();
			for (unsigned index = 0; index < elementNum; index++) {
				Constant* element = caggregate->getAggregateElement(index);
				handleInitializer(element, mo, startAddress);
			}
			break;
		}

		case Type::VectorTyID: {
			elementNum = caggregate->getType()->getVectorNumElements();
			for (unsigned index = 0; index < elementNum; index++) {
				Constant* element = caggregate->getAggregateElement(index);
				handleInitializer(element, mo, startAddress);
			}
			break;
		}

		default: {
			cerr << caggregate->getType()->getTypeID() << endl;
			assert(0 && "unknown aggregatezero type");
		}

		}
	} else if (ConstantStruct* cstruct = dyn_cast<ConstantStruct>(
			initializer)) {
		StructType* structType = cstruct->getType();
		if (structType->getStructName() == "union.pthread_mutex_t"
				|| structType->getStructName() == "union.pthread_cond_t"
				|| structType->getStructName() == "union.pthread_barrier_t") {
			unsigned alignment = layout->getABITypeAlignment(structType);
			if (startAddress % alignment != 0) {
				startAddress = (startAddress / alignment + 1) * alignment;
			}
			startAddress += executor->kmodule->targetData->getTypeSizeInBits(
					structType) / 8;
		} else {
			uint64_t elementNum = structType->getNumElements();
			for (unsigned index = 0; index < elementNum; index++) {
				Constant* element = cstruct->getAggregateElement(index);
				handleInitializer(element, mo, startAddress);
			}
		}
	} else if (ConstantPointerNull* cpoint = dyn_cast<ConstantPointerNull>(
			initializer)) {
		Type* type = initializer->getType();
		unsigned alignment = layout->getABITypeAlignment(type);
		if (startAddress % alignment != 0) {
			startAddress = (startAddress / alignment + 1) * alignment;
		}

		startAddress += executor->kmodule->targetData->getTypeSizeInBits(type)
				/ 8;
	} else if (llvm::ConstantExpr* cexpr = dyn_cast<llvm::ConstantExpr>(
			initializer)) {
		// handle global pointer which has been initialized. For example, char * a = "hello"
		handleConstantExpr(cexpr);
	} else if (ConstantArray * carray = dyn_cast<ConstantArray>(initializer)) {
		//handle array which has more than one dimension and initial value
		for (unsigned i = 0; i < carray->getNumOperands(); i++) {
			Constant* element = carray->getAggregateElement(i);
			handleInitializer(element, mo, startAddress);
		}
	} else {
		cerr << "value = " << initializer->getValueID() << " type = "
				<< initializer->getType()->getTypeID() << endl;
		assert(0 && "unsupported initializer");
	}
}
/**
 * 处理LLVM::ConstantExpr类型
 */
void PSOListener::handleConstantExpr(llvm::ConstantExpr* expr) {
	switch (expr->getOpcode()) {

	case Instruction::GetElementPtr: {
		GlobalVariable* op0 = dyn_cast<GlobalVariable>(expr->getOperand(0));
		Constant* trueInitializer = op0->getInitializer();
		MemoryObject *mo = executor->globalObjects.find(op0)->second;
		uint64_t address = mo->address;
		handleInitializer(trueInitializer, mo, address);
		break;
	}

	default: {
		cerr << expr->getOpcode() << endl;
		assert("0 && unsupported Opcode");
	}

	}
}

/**
 * 向全局变量表插入全局变量
 */
void PSOListener::insertGlobalVariable(ref<Expr> address, Type* type) {
	ConstantExpr* realAddress = dyn_cast<ConstantExpr>(address.get());
	uint64_t key = realAddress->getZExtValue();
	map<uint64_t, Type*>::iterator mi = usedGlobalVariableRecord.find(key);
	if (mi == usedGlobalVariableRecord.end()) {
		usedGlobalVariableRecord.insert(make_pair(key, type));
	}
}

/**
 * 根据Type，在MemoryObject中提取address对应的内存单元，存储成Expr对象
 */
ref<Expr> PSOListener::getExprFromMemory(ref<Expr> address, ObjectPair & op,
		Type * type) {
	const MemoryObject* mo = op.first;
	const ObjectState* os = op.second;
	ref<Expr> offset = mo->getOffsetExpr(address);
	ref<Expr> result = os->read(offset,
			executor->kmodule->targetData->getTypeSizeInBits(type));
	return result;
}

/**
 * 获取外部函数的返回值,必须在Call指令解释执行之后调用
 */
Constant * PSOListener::handleFunctionReturnValue(ExecutionState & state,
		KInstruction * ki) {
	Instruction* inst = ki->inst;
	Function *f = lastEvent->calledFunction;
	Type* returnType = inst->getType();
	Constant* result = NULL;
	if (!f->getName().startswith("klee") && !executor->kmodule->functionMap[f]
			&& !returnType->isVoidTy()) {
		ref<Expr> returnValue =
				executor->getDestCell(state.currentThread, ki).value;
		result = Transfer::expr2Constant(returnValue.get(), returnType);
//		if (dyn_cast<ConstantInt>(result)) {
//			ConstantInt* ci = dyn_cast<ConstantInt>(result);
//			cerr << ci->getType()->getBitWidth() << " " << ci->getZExtValue() << endl;
//		} else if (dyn_cast<ConstantFP>(result)) {
//			ConstantFP* cfp = dyn_cast<ConstantFP>(result);
//			if (cfp->getType()->isFloatTy()) {
//				cerr << "float: " << cfp->getValueAPF().convertToFloat() << endl;
//			} else if (cfp->getType()->isDoubleTy()) {
//				cerr << "double: " << cfp->getValueAPF().convertToDouble() << endl;
//			}
//		}
	}
	return result;
}

/**
 * 获取某些对指针参数指向空间进行写操作的外部函数的输入参数,必须在Call指令解释执行之后调用
 */
void PSOListener::handleExternalFunction(ExecutionState& state,
		KInstruction *ki) {
	Trace* trace = rdManager.getCurrentTrace();
	Instruction* inst = ki->inst;
	Function *f = lastEvent->calledFunction;
	if (f->getName() == "strcpy") {

//		ref<Expr> scrAddress = executor->eval(ki, 2, state.currentThread).value;
//		ObjectPair scrop;
//		//处理scr
//		getMemoryObject(scrop, state, scrAddress);
//
//		const MemoryObject* scrmo = scrop.first;
//		const ObjectState* scros = scrop.second;
//
//		ConstantExpr *caddress = cast<ConstantExpr>(scrAddress);
//		uint64_t scraddress = caddress->getZExtValue();
//		std::cerr << "dest" <<isGlobalMO(scrmo)<< std::endl;
//		for (unsigned i = 0; i < scrmo->size; i++) {
//			std::cerr << "dest" << std::endl;
//			ref<Expr> ch = scros->read(i, 8);
//			Constant* constant = Transfer::expr2Constant(ch.get(),
//					Type::getInt8Ty(inst->getContext()));
//			ConstantExpr* cexpr = dyn_cast<ConstantExpr>(ch.get());
//			string name = createVarName(scrmo->id, scraddress + i,
//					isGlobalMO(scrmo));
//			if (isGlobalMO(scrmo)) {
//				unsigned loadTime = getLoadTime(scraddress + i);
//				trace->insertReadSet(name, lastEvent);
//				name = createGlobalVarFullName(name, loadTime, false);
//				lastEvent->isGlobal = true;
//			}
//			lastEvent->scrVariables.insert(make_pair(name, constant));
//			//cerr << "address = " << name << "value = " << ((ConstantInt*)constant)->getSExtValue() << endl;
//			//判断是否是字符串的末尾
//			if (cexpr->getZExtValue() == 0) {
//				break;
//			}
//		}
		ref<Expr> destAddress = executor->eval(ki, 1, state.currentThread).value;
		ObjectPair destop;
		//处理dest
		getMemoryObject(destop, state, destAddress);
		const MemoryObject* destmo = destop.first;
		const ObjectState* destos = destop.second;
		ConstantExpr *caddress = cast<ConstantExpr>(destAddress);
		uint64_t destaddress = caddress->getZExtValue();
		for (unsigned i = 0; i < destmo->size - destaddress + destmo->address;
				i++) {
			ref<Expr> ch = destos->read(i, 8);
			ConstantExpr* cexpr = dyn_cast<ConstantExpr>(ch.get());
			string name = createVarName(destmo->id, destaddress + i,
					isGlobalMO(destmo));
			if (isGlobalMO(destmo)) {
				unsigned storeTime = getStoreTime(destaddress + i);
				trace->insertWriteSet(name, lastEvent);

				name = createGlobalVarFullName(name, storeTime, true);

				lastEvent->isGlobal = true;
			}
#if DEBUGSTRCPY
			cerr << "Event name : " << lastEvent->eventName << "\n";
			cerr<<"name : "<<name<<std::endl;
#endif
			lastEvent->implicitGlobalVar.push_back(name);
			//cerr << "address = " << name << "value = " << ((ConstantInt*)constant)->getSExtValue() << endl;
			//判断是否是字符串的末尾
			if (cexpr->getZExtValue() == 0) {
				break;
			}
		}

	} else if (f->getName() == "getrlimit") {
		ref<Expr> address = executor->eval(ki, 2, state.currentThread).value;
		ObjectPair op;
		Type* type = inst->getOperand(1)->getType()->getPointerElementType();
		getMemoryObject(op, state, address);
		uint64_t start = dyn_cast<ConstantExpr>(address)->getZExtValue();
		analyzeInputValue(start, op, type);
	} else if (f->getName() == "lstat") {
		ref<Expr> address = executor->eval(ki, 2, state.currentThread).value;
		ObjectPair op;
		Type* type = inst->getOperand(1)->getType()->getPointerElementType();
		getMemoryObject(op, state, address);
		uint64_t start = dyn_cast<ConstantExpr>(address)->getZExtValue();
		analyzeInputValue(start, op, type);
	} else if (f->getName() == "time") {
		ref<Expr> address = executor->eval(ki, 1, state.currentThread).value;
		ObjectPair op;
		Type* type = inst->getOperand(0)->getType()->getPointerElementType();
		getMemoryObject(op, state, address);
		uint64_t start = dyn_cast<ConstantExpr>(address)->getZExtValue();
		analyzeInputValue(start, op, type);
	}

}

/**
 * 解析一个MemoryObject，差分成每一个基本类型（Consant*）。对于指针不展开
 */
void PSOListener::analyzeInputValue(uint64_t& address, ObjectPair& op,
		Type* type) {
	Trace* trace = rdManager.getCurrentTrace();
	DataLayout* layout = executor->kmodule->targetData;
	switch (type->getTypeID()) {
	case Type::HalfTyID:
	case Type::FloatTyID:
	case Type::DoubleTyID:
	case Type::X86_FP80TyID:
	case Type::FP128TyID:
	case Type::PPC_FP128TyID:
	case Type::IntegerTyID:
	case Type::PointerTyID: {
		const MemoryObject* mo = op.first;
		const ObjectState* os = op.second;
		//ABI or preferable
		//ylc
		unsigned alignment = layout->getABITypeAlignment(type);
		if (address % alignment != 0) {
			address = (address / alignment + 1) * alignment;
		}
		ref<Expr> value = os->read(address - mo->address,
				type->getPrimitiveSizeInBits());
		string variableName = createVarName(mo->id, address, isGlobalMO(mo));
		map<uint64_t, unsigned>::iterator index = storeRecord.find(address);
		unsigned storeTime = getStoreTime(address);
		address += type->getPrimitiveSizeInBits() / 8;
		if (isGlobalMO(mo)) {
			trace->insertWriteSet(variableName, lastEvent);
			variableName = createGlobalVarFullName(variableName, storeTime,
					true);
		}
		lastEvent->implicitGlobalVar.push_back(variableName);

//		if (constant->getType()->isIntegerTy()) {
//			cerr << variableName << " " << ((ConstantInt*)constant)->getSExtValue() << endl;
//		} else if (constant->getType()->isFloatTy()) {
//			cerr << variableName << " " << ((ConstantFP*)constant)->getValueAPF().convertToFloat() << endl;
//		} else if (constant->getType()->isDoubleTy()) {
//			cerr << variableName << " " << ((ConstantFP*)constant)->getValueAPF().convertToDouble() << endl;
//		}
		break;
	}

	case Type::StructTyID: {
		//opaque struct 无法解析
		assert(!dyn_cast<StructType>(type)->isOpaque());
		for (unsigned i = 0; i < type->getStructNumElements(); i++) {
			Type* elementType = type->getStructElementType(i);
			analyzeInputValue(address, op, elementType);
		}
		break;
	}

	case Type::ArrayTyID: {
		for (unsigned i = 0; i < type->getArrayNumElements(); i++) {
			Type* elementType = type->getArrayElementType();
			analyzeInputValue(address, op, elementType);
		}
		break;
	}

	case Type::VectorTyID: {
		for (unsigned i = 0; i < type->getVectorNumElements(); i++) {
			Type* elementType = type->getVectorElementType();
			analyzeInputValue(address, op, elementType);
		}
		break;
	}

	default: {
		cerr << "typeID: " << type->getTypeID() << endl;
		assert(0 && "unsupport type");
	}

	}
}

/**
 * 计算全局变量的读操作次数
 */
unsigned PSOListener::getLoadTime(uint64_t address) {
	unsigned loadTime;
	map<uint64_t, unsigned>::iterator index = loadRecord.find(address);
	if (index == loadRecord.end()) {
		loadRecord.insert(make_pair(address, 1));
		loadTime = 1;
	} else {
		loadTime = index->second + 1;
		loadRecord[address] = loadTime;
	}
	return loadTime;
}

/**
 * 计算全局变量的写操作次数
 */
unsigned PSOListener::getStoreTime(uint64_t address) {
	unsigned storeTime;
	map<uint64_t, unsigned>::iterator index = storeRecord.find(address);
	if (index == storeRecord.end()) {
		storeRecord.insert(make_pair(address, 1));
		storeTime = 1;
	} else {
		storeTime = index->second + 1;
		storeRecord[address] = storeTime;
	}
	return storeTime;
}

/**
 * 获取函数指针指向的Function
 */
Function * PSOListener::getPointeredFunction(ExecutionState & state,
		KInstruction * ki) {
	StackFrame* sf = &state.currentThread->stack.back();
	//外部函数调用不会创建函数栈,其它函数调用会创建,此处需判断之前Call指令的执行是否已经创建了新的函数栈,
	//如果是,则倒数第二个元素是Call指令所在的函数栈.
	if (!ki->inst->getParent()->getParent()->getName().equals(
			sf->kf->function->getName())) {
		sf = &state.currentThread->stack[state.currentThread->stack.size() - 2];
	}
	int vnumber = ki->operands[0];
	ref<Expr> result;
	if (vnumber < 0) {
		unsigned index = -vnumber - 2;
		result = executor->kmodule->constantTable[index].value;
	} else {
		//cerr << "locals = " << sf->locals << " vnumber = " << vnumber << " function name = " << sf->kf->function->getName().str() << endl;
		result = sf->locals[vnumber].value;
	}
	ConstantExpr* addrExpr = dyn_cast<klee::ConstantExpr>(result);
	uint64_t addr = addrExpr->getZExtValue();
	return (Function*) addr;
}

/**
 * 消息相应函数，在初始化所有全局变量之后调用
 */
void PSOListener::afterPreparation() {

}

/**
 * 消息相应函数，在创建了新线程之后调用
 */
void PSOListener::createThread(ExecutionState &state, Thread* thread) {
	Trace* trace = rdManager.getCurrentTrace();
	trace->insertThreadCreateOrJoin(make_pair(lastEvent, thread->threadId),
			true);
}

/**
 * 消息相应函数，在前缀执行出错之后程序推出之前调用
 */
void PSOListener::executionFailed(ExecutionState &state, KInstruction *ki) {
	rdManager.getCurrentTrace()->traceType = Trace::FAILED;
}

/**
 * 打印函数，用于打印执行的指令
 */
void PSOListener::printInstrcution(ExecutionState& state, KInstruction* ki) {
	string fileName = cwd + "/trace"
			+ Transfer::uint64toString(rdManager.getCurrentTrace()->Id)
			+ ".txt";
	string errorMsg;
	raw_fd_ostream out(fileName.c_str(), errorMsg, raw_fd_ostream::F_Append);
	//ostream& out = cerr;
	Prefix* prefix = executor->prefix;
	if (prefix && !isPrefixFinished && prefix->isFinished()) {
		isPrefixFinished = true;
		out << "prefix finished\n";
	}
	Instruction* inst = ki->inst;
	if (MDNode *mdNode = inst->getMetadata("dbg")) { // Here I is an LLVM instruction
		DILocation loc(mdNode); // DILocation is in DebugInfo.h
		unsigned line = loc.getLineNumber();
		string file = loc.getFilename().str();
		string dir = loc.getDirectory().str();
		out << "thread" << state.currentThread->threadId << " " << dir << "/"
				<< file << " " << line << ": ";
		inst->print(out);
		//cerr << "thread" << state.currentThread->threadId << " " << dir << "/" << file << " " << line << ": " << inst->getOpcodeName() << endl;
		switch (inst->getOpcode()) {
		case Instruction::Call: {
			CallSite cs(inst);
			Value *fp = cs.getCalledValue();
			Function *f = executor->getTargetFunction(fp, state);
			if (!f) {
				ref<Expr> expr =
						executor->eval(ki, 0, state.currentThread).value;
				ConstantExpr* constExpr = dyn_cast<ConstantExpr>(expr.get());
				uint64_t functionPtr = constExpr->getZExtValue();
				f = (Function*) functionPtr;
			}
			out << " " << f->getName().str();
			if (f->getName().str() == "pthread_mutex_lock") {
				ref<Expr> param =
						executor->eval(ki, 1, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			} else if (f->getName().str() == "pthread_mutex_unlock") {
				ref<Expr> param =
						executor->eval(ki, 1, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			} else if (f->getName().str() == "pthread_cond_wait") {
				//get lock
				ref<Expr> param =
						executor->eval(ki, 2, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
				//get cond
				param = executor->eval(ki, 1, state.currentThread).value;
				cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			} else if (f->getName().str() == "pthread_cond_signal") {
				ref<Expr> param =
						executor->eval(ki, 1, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			} else if (f->getName().str() == "pthread_cond_broadcast") {
				ref<Expr> param =
						executor->eval(ki, 1, state.currentThread).value;
				ConstantExpr* cexpr = dyn_cast<ConstantExpr>(param);
				out << " " << cexpr->getZExtValue();
			}
			break;
		}

		}
		out << '\n';
	} else {
		out << "thread" << state.currentThread->threadId << " klee/internal 0: "
				<< inst->getOpcodeName() << '\n';
	}

	out.close();
	if (prefix && prefix->current() + 1 == prefix->end()) {
		inst->print(errs());
		Event* event = *prefix->current();
		ref<Expr> param = executor->eval(ki, 0, state.currentThread).value;
		ConstantExpr* condition = dyn_cast<ConstantExpr>(param);
		if (condition->getAPValue().getBoolValue() != event->condition) {
			cerr << "\n前缀已被取反\n";
		} else {
			cerr << "\n前缀未被取反\n";
		}
	}
}

void PSOListener::printPrefix() {
	if (executor->prefix) {
		string fileName = prefixDir + executor->prefix->getName() + ".txt";
		string errorMsg;
		raw_fd_ostream out(fileName.c_str(), errorMsg,
				raw_fd_ostream::F_Append);
		executor->prefix->print(out);
		out.close();
		//prefix->print(cerr);
	}
}

ref<Expr> PSOListener::manualMakeSymbolic(ExecutionState& state, ref<Expr> address,
		std::string name, unsigned size, bool isFloat) {

	//删除旧的符号变量
//	if(!isFirst){
//		for (unsigned int i=0; i != state.symbolics.size(); i++){
//			if(state.symbolics[i].first->id == mo->id){
//				state.symbolics.at(i).first->setName(name);
//				break;
//			}
//		}
//	}else {

//		cerr<<"size : "<<size<<std::endl;
	//添加新的符号变量
	const Array *array = new Array(name, size, isFloat);
	ObjectState *os = new ObjectState(size, array);
	ref<Expr> offset = ConstantExpr::create(0, BIT_WIDTH);
	ref<Expr> result = os->read(offset, size);
	if (isFloat)
			result.get()->isFloat = true;
#if DEBUGSYMBOLIC
	cerr << "Event name : " << (*currentEvent)->eventName << "\n";
	cerr << "make symboic:" << name << std::endl;
	cerr << "is float:" << isFloat << std::endl;
	std::cerr << "result : ";
	result->dump();
#endif

	return result;
}

ref<Expr> PSOListener::readExpr(ExecutionState &state, ref<Expr> address,
		Expr::Width size) {
	ObjectPair op;
	getMemoryObject(op, state, address);
	const MemoryObject *mo = op.first;
	ref<Expr> offset = mo->getOffsetExpr(address);
	const ObjectState *os = op.second;
	ref<Expr> result = os->read(offset, size);
	return result;
}

void PSOListener::storeZeroToExpr(ExecutionState& state, ref<Expr> address,
		Expr::Width size) {

	ref<Expr> value = ConstantExpr::create(0, size);
	executor->executeMemoryOperation(state, true, address, value, 0);
}

void PSOListener::prepareSymbolicRun(ExecutionState &initialState) {
	Trace* trace = rdManager.getCurrentTrace();
	lastEvent = NULL;
	currentEvent = trace->path.begin();
	endEvent = trace->path.end();
}

void PSOListener::getNewPrefix() {
	//获取新的前缀

//	if(executor->executionNum == 5)
//		assert(false);
	Prefix* prefix = rdManager.getNextPrefix();
	//Prefix* prefix = NULL;
	if (prefix) {
		delete executor->prefix;
		executor->prefix = prefix;
		executor->isFinished = false;
	} else {
		executor->isFinished = true;
#if PRINT_RUNTIMEINFO
		rdManager.printAllTrace(cerr);
#endif
	}
}

void PSOListener::beforeSymbolicRun(ExecutionState &state, KInstruction *ki) {
	Trace* trace = rdManager.getCurrentTrace();
	if ((*currentEvent)) {
		Instruction* inst = ki->inst;
//		cerr << "event name : " << (*currentEvent)->eventName << " ";
		Thread* thread = state.currentThread;
//		cerr << "thread id : " << thread->threadId ;
//		inst->dump();
//		cerr << "thread id : " << (*currentEvent)->threadId ;
//		(*currentEvent)->inst->inst->dump();
		switch (inst->getOpcode()) {
		case Instruction::Load: {
			ref<Expr> address = executor->eval(ki, 0, thread).value;
			Expr::Width size = executor->getWidthForLLVMType(
					ki->inst->getType());
			ConstantExpr* realAddress = dyn_cast<ConstantExpr>(
					address.get());
			ref<Expr> value = readExpr(state, address, size);
//			cerr << "load value : " << value << "\n";
			if ((*currentEvent)->isGlobal) {
				bool isFloat = 0;
				Type::TypeID id = ki->inst->getType()->getTypeID();
				if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
					isFloat = 1;
				}
				if (isFloat || id == Type::IntegerTyID) {
					trace->storeSymbolicExpr.push_back(value);
					if (realAddress) {
						ObjectPair op;
						bool success = getMemoryObject(op, state, address);
						if (success) {
							manualMakeSymbolic(state, address,
									(*currentEvent)->globalVarFullName, size,
									isFloat);
						}
					}
				}
			}
			break;
		}
		case Instruction::Store: {
			if ((*currentEvent)->isGlobal) {
				bool isFloat = 0;
				Type::TypeID id =
						ki->inst->getOperand(0)->getType()->getTypeID();
//					cerr<<"id : "<<id<<std::endl;
				if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
					isFloat = 1;
				}
				if (isFloat || id == Type::IntegerTyID) {

				}

			}
			break;
		}
		case Instruction::Br: {
//			inst->dump();
			BranchInst *bi = dyn_cast<BranchInst>(inst);
			if (!bi->isUnconditional()) {

				unsigned isAssert = 0;
				string fileName = ki->info->file;
				std::map<string, std::vector<unsigned> >::iterator it =
						assertMap.find(fileName);
				unsigned line = ki->info->line;
				if (it != assertMap.end()) {
					if (find(assertMap[fileName].begin(),
							assertMap[fileName].end(), line)
							!= assertMap[fileName].end()) {
						isAssert = 1;
					}
				}
//					cerr << "file name : " << fileName << " line : " << line << "\n";

				ref<Expr> value1 = executor->eval(ki, 0, thread).value;
				if (value1->getKind() != Expr::Constant) {
					Expr::Width width = value1->getWidth();
					ref<Expr> value2;
					if ((*currentEvent)->condition == true) {
						value2 = ConstantExpr::create(true, width);
					} else {
						value2 = ConstantExpr::create(false, width);
					}
					ref<Expr> constraint = EqExpr::create(value1, value2);
//					cerr << "br constraint : " << constraint << "\n";
					if (isAssert) {
//						cerr << "event name : " << (*currentEvent)->eventName << "\n";
//						cerr << "constraint : " << constraint << "\n";
						trace->assertSymbolicExpr.push_back(constraint);
						trace->assertEvent.push_back((*currentEvent));

						//line = 0 may be some br like phi or other IR
						//}else if(line != 0){

					} else if (kleeBr == false) {
//						cerr << "event name : " << (*currentEvent)->eventName << "\n";
//						cerr << "constraint : " << constraint << "\n";
						trace->brSymbolicExpr.push_back(constraint);
						trace->brEvent.push_back((*currentEvent));
					}
					executor->evalAgainst(ki, 0, thread, value2);
				}
				if (kleeBr == true) {
					kleeBr = false;
				}
			}
			break;
		}
		case Instruction::Select: {

			break;
		}
		case Instruction::Call: {
			CallSite cs(inst);
//			(*currentEvent)->inst->inst->dump();
//			inst->dump();
//			std::cerr<<"isFunctionWithSourceCode : "<<(*currentEvent)->isFunctionWithSourceCode<<"\n";
			if (!(*currentEvent)->isFunctionWithSourceCode) {
				unsigned numArgs = cs.arg_size();
				for (unsigned j = numArgs; j > 0; j--) {
					ref<Expr> value1 = executor->eval(ki, j, thread).value;
//		    		cerr<<"value1->getKind() : "<<value1->getKind()<<std::endl;
//		    		cerr<<"value1 : ";
//		    		value1->dump();
					if (value1->getKind() != Expr::Constant) {
						ref<Expr> value2 = (*currentEvent)->value.back();
						if(value1->getKind() == Expr::Concat || value1->getKind() == Expr::Read){
//							std::cerr<<"value->getKind() : "<<value1->getKind()<<std::endl;
//							std::cerr<<"value : "<<value1<<std::endl;
//							cerr<<"filter.getVarName(value1) :"<<filter.getVarName(value1)<<"\n";
							ref<Expr> value = symbolicMap[filter.getVarName(value1)];

//				    		cerr<<"value->getKind() : "<<value->getKind()<<std::endl;
//				    		cerr<<"value : ";
//				    		value->dump();
							if(value->getKind() == Expr::Constant){
								value2 = value;
							}
						}
//					    		cerr<<"value1->getKind() : "<<value1->getKind()<<std::endl;
//					    		cerr<<"value1 : ";
//					    		value1->dump();
//					    		cerr<<"value2 : ";
//					    		value2->dump();
						executor->evalAgainst(ki, j, thread, value2);
					}
					(*currentEvent)->value.pop_back();
				}
			}
//			Function *f = (*currentEvent)->calledFunction;
//			std::cerr<<"call name : "<< f->getName().str().c_str() <<"\n";
//			if (f->getName() == "strcpy") {
//				//处理load
//				ref<Expr> scrAddress = executor->eval(ki, 2,
//						state.currentThread).value;
//				ObjectPair scrop;
//
//				getMemoryObject(scrop, state, scrAddress);
//				const MemoryObject* scrmo = scrop.first;
//				if (isGlobalMO(scrmo)) {
//					Expr::Width size = 8;
//					int i = 0;
//					for (std::map<std::string, llvm::Constant*>::iterator it =
//							(*currentEvent)->scrVariables.begin(), ie =
//							(*currentEvent)->scrVariables.end(); it != ie;
//							i++, it++) {
//						manualMakeSymbolic(state,
//								AddExpr::create(scrAddress,
//										ConstantExpr::create(i, 32)), it->first,
//								size, false);
//					}
//				}
//			}
//			else if (f->getName() == "__xstat64") {
//				exit(1);
//			}
			break;
		}
		case Instruction::GetElementPtr: {
			KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
			std::vector<ref<klee::Expr> >::iterator first =
					(*currentEvent)->value.begin();
			for (std::vector<std::pair<unsigned, uint64_t> >::iterator it =
					kgepi->indices.begin(), ie = kgepi->indices.end(); it != ie;
					++it) {
				ref<Expr> index = executor->eval(ki, it->first, thread).value;
//				std::cerr<<"kgepi->index : "<<index<<std::endl;
				if (index->getKind() != Expr::Constant) {
					executor->evalAgainst(ki, it->first, thread, *first);
					ref<Expr> constraint = EqExpr::create(index, *first);
//					(*currentEvent)->isConditionIns = true;
//					(*currentEvent)->condition = true;
//					cerr << "event name : " << (*currentEvent)->eventName << "\n";
//					cerr << "constraint : " << constraint << "\n";
					trace->brSymbolicExpr.push_back(constraint);
					trace->brEvent.push_back((*currentEvent));
				}
				++first;
			}
			if (kgepi->offset) {
//				std::cerr<<"kgepi->offset : "<<kgepi->offset<<std::endl;
				//目前没有这种情况...
//				assert(0 &&"kgepi->offset");
			}
			break;
		}
		case Instruction::Switch: {
//			SwitchInst *si = cast<SwitchInst>(inst);
			ref<Expr> cond1 = executor->eval(ki, 0, thread).value;
			if (cond1->getKind() != Expr::Constant) {
				ref<Expr> cond2 = (*currentEvent)->value.back();
				ref<Expr> constraint = EqExpr::create(cond1, cond2);
				trace->brSymbolicExpr.push_back(constraint);
				trace->brEvent.push_back((*currentEvent));
				executor->evalAgainst(ki, 0, thread, cond2);
			}
			break;
		}
		default: {
			break;
		}
		}
	}
}

void PSOListener::afterSymbolicRun(ExecutionState &state, KInstruction *ki) {
	Trace* trace = rdManager.getCurrentTrace();
	if ((*currentEvent)) {
		Instruction* inst = ki->inst;
		Thread* thread = state.currentThread;
		switch (inst->getOpcode()) {
			case Instruction::Load: {
				bool isFloat=0;
				Type::TypeID id = ki->inst->getType()->getTypeID();
				if((id >= Type::HalfTyID)&&(id <= Type::DoubleTyID)){
						isFloat=1;
				}
				if (isFloat) {
						thread->stack.back().locals[ki->dest].value.get()->isFloat = true;
				}
				if((*currentEvent)->isGlobal){
					bool isFloat=0;
					Type::TypeID id = ki->inst->getType()->getTypeID();
					if((id >= Type::HalfTyID)&&(id <= Type::DoubleTyID)){
						isFloat=1;
					}
					if(isFloat || id == Type::IntegerTyID){
						Expr::Width size = executor->getWidthForLLVMType(ki->inst->getType());
						ref<Expr> address = executor->eval(ki, 0, thread).value;
						ref<Expr> value = trace->storeSymbolicExpr.back();
						trace->storeSymbolicExpr.pop_back();
//						ref<Expr> value2 = readExpr(state, address, size);
						executor->executeMemoryOperation(state, true, address, value, 0);
//				    	ref<Expr> constraint = EqExpr::create(value, value2);
//				    	cerr << "load constraint : " << constraint << "\n";
//				    	allSymbolicExpr.push_back(constraint);
					}
				}
				break;
			}

		case Instruction::Store: {
			if ((*currentEvent)->isGlobal) {
				bool isFloat = 0;
				Type::TypeID id =
						ki->inst->getOperand(0)->getType()->getTypeID();
				if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
					isFloat = 1;
				}
				if (isFloat || id == Type::IntegerTyID) {
					ref<Expr> address = executor->eval(ki, 1, thread).value;
					ref<Expr> value = executor->eval(ki, 0, thread).value;
					Expr::Width size = value->getWidth();
					ConstantExpr* realAddress = dyn_cast<ConstantExpr>(
							address.get());
					if (realAddress) {
//						uint64_t key = realAddress->getZExtValue();
						ObjectPair op;
						bool success = getMemoryObject(op, state, address);
						if (success) {
							ref<Expr> value2 = manualMakeSymbolic(state, address,
									(*currentEvent)->globalVarFullName, size,
									isFloat);
							ref<Expr> constraint = EqExpr::create(value,
									value2);
							trace->storeSymbolicExpr.push_back(constraint);
//							cerr << "store constraint : " << constraint << "\n";
//							cerr<<"(*currentEvent)->varName :"<<(*currentEvent)->varName<<"\n";
//							std::cerr<<"symbolicMap value1 : "<<value1<<std::endl;
//							std::cerr<<"symbolicMap value2 : "<<value2<<std::endl;

							//当value->getKind() == Expr::Cancat时，可能有问题，
							//某函数对一个内存进行写操作，没有将其记录在symbolicMap中。
							//比如pthread_create()函数，对此函数已经过特殊处理。
							if(value->getKind() != Expr::Constant){
								if(value->getKind() == Expr::Concat || value->getKind() == Expr::Read){
//									std::cerr<<"value->getKind() : "<<value->getKind()<<std::endl;
//									std::cerr<<"value : "<<value<<std::endl;
									value = symbolicMap[filter.getVarName(value)];
								}else{
									value = (*currentEvent)->value.back();
								}
							}
//							cerr << "Store Map varName : " << (*currentEvent)->varName << "\n";
//							cerr << "Store Map value : " << value << "\n";
							symbolicMap[(*currentEvent)->varName] = value;
							executor->executeMemoryOperation(state, true, address, value, 0);
							(*currentEvent)->value.pop_back();
						}
					}
				}
			}
			break;
		}
		case Instruction::Call: {
			CallSite cs(inst);
			Function *f = (*currentEvent)->calledFunction;
			//存在未知错误
//			Value *fp = cs.getCalledValue();
//			Function *f = executor->getTargetFunction(fp, state);
//			if (!f) {
//				ref<Expr> expr = executor->eval(ki, 0, thread).value;
//				ConstantExpr* constExpr = dyn_cast<ConstantExpr>(expr.get());
//				uint64_t functionPtr = constExpr->getZExtValue();
//				f = (Function*) functionPtr;
//			}

			if (!f->getName().startswith("klee")
					&& !executor->kmodule->functionMap[f]
					&& !inst->getType()->isVoidTy()) {
				ref<Expr> returnValue = executor->getDestCell(
						state.currentThread, ki).value;
				bool isFloat = 0;
				Type::TypeID id = inst->getType()->getTypeID();
				if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
					isFloat = 1;
				}
				if (isFloat) {
					returnValue.get()->isFloat = true;
				}
				executor->setDestCell(state.currentThread, ki, returnValue);
			}

			//需要添加Map操作
			if(f->getName().startswith("klee_div_zero_check")){
				kleeBr = true;
			}else if (f->getName() == "strcpy") {
				//地址可能还有问题
				ref<Expr> destAddress = executor->eval(ki, 1,
						state.currentThread).value;
//				ref<Expr> scrAddress = executor->eval(ki, 0,
//						state.currentThread).value;
//				ObjectPair scrop;
				ObjectPair destop;
//				getMemoryObject(scrop, state, scrAddress);
				getMemoryObject(destop, state, destAddress);
				const ObjectState* destos = destop.second;
				const MemoryObject* destmo = destop.first;
//				std::cerr<<destAddress<<std::endl;
//				std::cerr<<destmo->address<<std::endl;
//				std::cerr<<"destmo->size : "<<destmo->size<<std::endl;
				Expr::Width size = 8;
				for (int i = 0; i< (*currentEvent)->implicitGlobalVar.size(); i++) {
//					std::cerr<<"dest"<<std::endl;
					ref<Expr> address = AddExpr::create(destAddress,
							ConstantExpr::create(i, BIT_WIDTH));
					ref<Expr> value = destos->read(
							destmo->getOffsetExpr(address), size);
//					std::cerr<<"value : "<<value<<std::endl;
//					std::cerr<<"value : "<<value<<std::endl;
//					executor->executeMemoryOperation(state, true,
//							AddExpr::create(destAddress,
//									ConstantExpr::create(i, 32)), value, 0);
					if (isGlobalMO(destmo)) {
						manualMakeSymbolic(state, address,
								(*currentEvent)->implicitGlobalVar[i], size,
								false);
						ref<Expr> value1 = value;
						ref<Expr> value2 = readExpr(state,
								AddExpr::create(destAddress,
										ConstantExpr::create(i, BIT_WIDTH)),
								size);
						ref<Expr> constraint = EqExpr::create(value1, value2);
#if DEBUGSTRCPY
						cerr << "constraint : " << constraint << "\n";
//						cerr << (char)value.
#endif
						trace->storeSymbolicExpr.push_back(constraint);
//						cerr << "Store Map varName : " << (*currentEvent)->varName << "\n";
//						cerr << "Store Map value : " << value << "\n";
						symbolicMap[filter.getVarName(value2)] = value1;
						executor->executeMemoryOperation(state, true,
							AddExpr::create(destAddress,ConstantExpr::create(i, BIT_WIDTH)),
									value1, 0);
					}
					if (value->isZero()) {
						break;
					}
				}
			}else if(f->getName() == "pthread_create"){
				ref<Expr> pthreadAddress = executor->eval(ki, 1,
						state.currentThread).value;
				ObjectPair pthreadop;
				getMemoryObject(pthreadop, state, pthreadAddress);
				const ObjectState* pthreados = pthreadop.second;
				const MemoryObject* pthreadmo = pthreadop.first;
				Expr::Width size = BIT_WIDTH;
				ref<Expr> value = pthreados->read(0, size);
				if (isGlobalMO (pthreadmo)) {
					string varName = (*currentEvent)->varName;
#if DEBUGSTRCPY
					cerr << "varName : " << varName << "\n";
#endif
					symbolicMap[varName] = value;
				}
#if DEBUGSTRCPY
				std::cerr << "value : " << value << std::endl;
				cerr << "pthread id : " << value << "\n";
#endif
//			}else if (f->getName() == "__xstat64") {
//				exit(1);
			}
			break;
		}
		case Instruction::PHI:{
			ref<Expr> result = executor->eval(ki, thread->incomingBBIndex, thread).value;
//			cerr << "PHI : " << result << "\n";
			break;
		}
		default: {

			break;
		}

		}
	}
	if (currentEvent != endEvent)
		currentEvent++;
}

void PSOListener::afterprepareSymbolicRun(ExecutionState &initialState) {

	symbolicMap.clear();
	Trace* trace = rdManager.getCurrentTrace();
#if DEBUGSYMBOLIC
	cerr << "all constraint :" << std::endl;
	std::cerr << "storeSymbolicExpr = " << trace->storeSymbolicExpr.size()
	<< std::endl;
	for (std::vector<ref<Expr> >::iterator it = trace->storeSymbolicExpr.begin(),
			ie = trace->storeSymbolicExpr.end(); it != ie; ++it) {
		it->get()->dump();
	}
#endif
#if DEBUGSYMBOLIC
	std::cerr << "brSymbolicExpr = " << trace->brSymbolicExpr.size()
	<< std::endl;
	for (std::vector<ref<Expr> >::iterator it = trace->brSymbolicExpr.begin(),
			ie = trace->brSymbolicExpr.end(); it != ie; ++it) {
		it->get()->dump();
	}
#endif
#if DEBUGSYMBOLIC
	std::cerr << "assertSymbolicExpr = " << trace->assertSymbolicExpr.size()
	<< std::endl;

	for (std::vector<ref<Expr> >::iterator it = trace->assertSymbolicExpr.begin(),
			ie = trace->assertSymbolicExpr.end(); it != ie; ++it) {
		it->get()->dump();
	}
#endif
//	filter.filterUseless(trace->storeSymbolicExpr, trace->brSymbolicExpr,
//			trace->kQueryExpr, trace->writeSet, trace->readSet, trace->global_variable_initializer);
#if DEBUGSYMBOLIC
	std::cerr << "kQueryExpr = " << trace->kQueryExpr.size()
	<< std::endl;
	for (std::vector<ref<Expr> >::iterator it = trace->kQueryExpr.begin(),
			ie = trace->kQueryExpr.end(); it != ie; ++it) {
		it->get()->dump();
	}
#endif

//	getNewPrefix();
}

void PSOListener::getGlobalSymbolic() {
//	Trace* trace = rdManager.getCurrentTrace();
}

void PSOListener::testForKquery2Z3() {
	Trace* trace = rdManager.getCurrentTrace();
//	std::cerr << "execute once\n";
	if (executor->isSymbolicRun) {
//		std::cerr << "kQueryExprSize = " << trace->kQueryExpr.size()
//				<< std::endl;
//		std::cerr << "printf\n";
//		z3::context *ctx = new context();
//		KQuery2Z3 *kq = new KQuery2Z3(trace->kQueryExpr, *ctx);

//		kq->getZ3Expr();
//		kq->printKquery();
//		kq->printZ3AndKqueryExpr();
	} else {
		std::cerr << "not execute\n";
	}
}

}
