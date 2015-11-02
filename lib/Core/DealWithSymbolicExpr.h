//by hy 2015.7.21

#include "klee/Expr.h"
#include "Event.h"
#include <vector>
#include <map>
#include <string>

namespace klee {

class DealWithSymbolicExpr {

private:

	void resolveSymbolicExpr(ref<Expr> value);


public:
	void filterUseless(
			std::vector<ref<klee::Expr> > &storeSymbolicExpr,
			std::vector<ref<klee::Expr> > &brSymbolicExpr,
			std::vector<ref<klee::Expr> > &kQueryExpr,
			std::map<std::string, std::vector<Event *> > &readSet,
			std::map<std::string, std::vector<Event *> > &writeSet,
			std::map<std::string, llvm::Constant*> &global_variable_initializer);
	std::string getVarName(ref<Expr> value);

};

}
