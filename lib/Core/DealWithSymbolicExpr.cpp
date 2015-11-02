//by hy 2015.7.21

#include "DealWithSymbolicExpr.h"
#include <sstream>
#include <ostream>
#include <set>

namespace klee {

//这里的是否使用一个map有待考虑.
std::vector<std::string> remainingExprVarName;
std::vector<ref<klee::Expr> > remainingExpr;
std::set<std::string> relatedSymbolicExpr;
std::map<std::string, std::vector<Event *> > usefulReadSet;
std::map<std::string, std::vector<Event *> > usefulWriteSet;
std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;

std::string DealWithSymbolicExpr::getVarName(ref<klee::Expr> value) {

	std::stringstream varName;
	varName.str("");
	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		return varName.str();
	}
	std::string globalVarFullName = revalue->updates.root->name;
	unsigned int i = 0;
	while ((globalVarFullName.at(i) != 'S') && (globalVarFullName.at(i) != 'L')) {
		varName << globalVarFullName.at(i);
		i++;
	}
	return varName.str();
}

//std::unsigned int DealWithSymbolicExpr::getAddress(ref<klee::Expr> value){
//	std::unsigned int address = 0;
//	ReadExpr *revalue;
//	if(value->getKind() == Expr::Concat){
//		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
//		revalue = cast<ReadExpr>(ccvalue->getKid(0));
//	}
//	else if(value->getKind() == Expr::Read){
//		revalue = cast<ReadExpr>(value);
//	}
//	else {
//		return address;
//	}
//	std::string globalVarFullName = revalue->updates.root->name;
//	std::unsigned int i = 0;
//	std::unsigned int t = 0;
//	for(i=0;;i++){
//		char c =globalVarFullName.at(i);
//		if(c == '_'){
//			t=1;
//		}else if((c == 'S')||(c == 'L')){
//			break;
//		}else if(t==1){
//			address = address*10 + c-'0';
//		}
//	}
//	return address;
//}

void DealWithSymbolicExpr::resolveSymbolicExpr(ref<klee::Expr> value) {
	if (value->getKind() == Expr::Read) {
		std::string varName = getVarName(value);
		if (relatedSymbolicExpr.find(varName) == relatedSymbolicExpr.end()) {
			relatedSymbolicExpr.insert(varName);
		}
		return;
	} else {
		unsigned kidsNum = value->getNumKids();
		if (kidsNum == 2 && value->getKid(0) == value->getKid(1)) {
			resolveSymbolicExpr(value->getKid(0));
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveSymbolicExpr(value->getKid(i));
			}
		}
	}
}

void DealWithSymbolicExpr::filterUseless(
		std::vector<ref<klee::Expr> > &storeSymbolicExpr,
		std::vector<ref<klee::Expr> > &brSymbolicExpr,
		std::vector<ref<klee::Expr> > &kQueryExpr,
		std::map<std::string, std::vector<Event *> > &readSet,
		std::map<std::string, std::vector<Event *> > &writeSet,
		std::map<std::string, llvm::Constant*> &global_variable_initializer) {
	std::string varName;
	relatedSymbolicExpr.clear();
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(), ie =
			storeSymbolicExpr.end(); it != ie; ++it) {
		varName = getVarName(it->get()->getKid(1));
		remainingExprVarName.push_back(varName);
		remainingExpr.push_back(it->get());
	}
	for (std::vector<ref<Expr> >::iterator it = brSymbolicExpr.begin(), ie =
			brSymbolicExpr.end(); it != ie; ++it) {
		resolveSymbolicExpr(it->get());
//		kQueryExpr.push_back(it->get());
	}
	for (std::set<std::string>::iterator nit = relatedSymbolicExpr.begin();
			nit != relatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
		std::vector<ref<Expr> >::iterator itt = remainingExpr.begin();
		for (std::vector<std::string>::iterator it =
				remainingExprVarName.begin(), ie = remainingExprVarName.end();
				it != ie;) {
			if (varName == *it) {
				remainingExprVarName.erase(it);
				--ie;
				kQueryExpr.push_back(*itt);
				resolveSymbolicExpr(itt->get());
				remainingExpr.erase(itt);
			} else {
				++it;
				++itt;
			}
		}
	}
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (relatedSymbolicExpr.find(varName) != relatedSymbolicExpr.end()) {
			usefulReadSet.insert(*nit);
		}
	}
	readSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulReadSet.begin(), nie = usefulReadSet.end(); nit != nie;
			++nit) {
		readSet.insert(*nit);
	}
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (relatedSymbolicExpr.find(varName) != relatedSymbolicExpr.end()) {
			usefulWriteSet.insert(*nit);
		}
	}
	writeSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulWriteSet.begin(), nie = usefulWriteSet.end(); nit != nie;
			++nit) {
		writeSet.insert(*nit);
	}
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (relatedSymbolicExpr.find(varName) != relatedSymbolicExpr.end()) {
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
	global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			usefulGlobal_variable_initializer.begin(), nie = usefulGlobal_variable_initializer.end(); nit != nie;
			++nit) {
		global_variable_initializer.insert(*nit);
	}
}

}
