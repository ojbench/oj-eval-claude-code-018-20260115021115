/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    //TODO: check if the first element is a symbol
    //If not, use Apply function to package to a closure;
    //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        //TODO: TO COMPLETE THE LOGIC
        // First element is not a symbol, treat as function application
        vector<Expr> rand;
        for (size_t i = 1; i < stxs.size(); i++) {
            rand.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), rand));
    }else{
    string op = id->s;
    if (find(op, env).get() != nullptr) {
        //TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
        // Variable found in environment, treat as function application
        vector<Expr> rand;
        for (size_t i = 1; i < stxs.size(); i++) {
            rand.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(Expr(new Var(op)), rand));
    }
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        //TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }

        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 2) {
                return Expr(new Plus(parameters[0], parameters[1]));
            } else {
                return Expr(new PlusVar(parameters));
            }
        } else if (op_type == E_MINUS) {
            if (parameters.size() == 2) {
                return Expr(new Minus(parameters[0], parameters[1]));
            } else {
                return Expr(new MinusVar(parameters));
            }
        } else if (op_type == E_MUL) {
            if (parameters.size() == 2) {
                return Expr(new Mult(parameters[0], parameters[1]));
            } else {
                return Expr(new MultVar(parameters));
            }
        }  else if (op_type == E_DIV) {
            if (parameters.size() == 2) {
                return Expr(new Div(parameters[0], parameters[1]));
            } else {
                return Expr(new DivVar(parameters));
            }
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_EXPT) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for expt");
            }
            return Expr(new Expt(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            if (parameters.size() == 2) {
                return Expr(new Less(parameters[0], parameters[1]));
            } else {
                return Expr(new LessVar(parameters));
            }
        } else if (op_type == E_LE) {
            if (parameters.size() == 2) {
                return Expr(new LessEq(parameters[0], parameters[1]));
            } else {
                return Expr(new LessEqVar(parameters));
            }
        } else if (op_type == E_EQ) {
            if (parameters.size() == 2) {
                return Expr(new Equal(parameters[0], parameters[1]));
            } else {
                return Expr(new EqualVar(parameters));
            }
        } else if (op_type == E_GE) {
            if (parameters.size() == 2) {
                return Expr(new GreaterEq(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterEqVar(parameters));
            }
        } else if (op_type == E_GT) {
            if (parameters.size() == 2) {
                return Expr(new Greater(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterVar(parameters));
            }
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if (op_type == E_NOT) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for not");
            }
            return Expr(new Not(parameters[0]));
        } else if (op_type == E_EQQ) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for eq?");
            }
            return Expr(new IsEq(parameters[0], parameters[1]));
        } else if (op_type == E_BOOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for boolean?");
            }
            return Expr(new IsBoolean(parameters[0]));
        } else if (op_type == E_INTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for number?");
            }
            return Expr(new IsFixnum(parameters[0]));
        } else if (op_type == E_NULLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for null?");
            }
            return Expr(new IsNull(parameters[0]));
        } else if (op_type == E_PAIRQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for pair?");
            }
            return Expr(new IsPair(parameters[0]));
        } else if (op_type == E_PROCQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for procedure?");
            }
            return Expr(new IsProcedure(parameters[0]));
        } else if (op_type == E_SYMBOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for symbol?");
            }
            return Expr(new IsSymbol(parameters[0]));
        } else if (op_type == E_STRINGQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for string?");
            }
            return Expr(new IsString(parameters[0]));
        } else if (op_type == E_LISTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for list?");
            }
            return Expr(new IsList(parameters[0]));
        } else if (op_type == E_CONS) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for cons");
            }
            return Expr(new Cons(parameters[0], parameters[1]));
        } else if (op_type == E_CAR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for car");
            }
            return Expr(new Car(parameters[0]));
        } else if (op_type == E_CDR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for cdr");
            }
            return Expr(new Cdr(parameters[0]));
        } else if (op_type == E_SETCAR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-car!");
            }
            return Expr(new SetCar(parameters[0], parameters[1]));
        } else if (op_type == E_SETCDR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-cdr!");
            }
            return Expr(new SetCdr(parameters[0], parameters[1]));
        } else if (op_type == E_DISPLAY) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for display");
            }
            return Expr(new Display(parameters[0]));
        } else if (op_type == E_VOID) {
            if (parameters.size() != 0) {
                throw RuntimeError("Wrong number of arguments for (void)");
            }
            return Expr(new MakeVoid());
        } else if (op_type == E_EXIT) {
            if (parameters.size() != 0) {
                throw RuntimeError("Wrong number of arguments for (exit)");
            }
            return Expr(new Exit());
        } else {
            throw RuntimeError("Unknown primitive: " + op);
        }
    }

    if (reserved_words.count(op) != 0) {
    	switch (reserved_words[op]) {
            case E_QUOTE: {
                if (stxs.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for quote");
                }
                return Expr(new Quote(stxs[1]));
            }
            case E_BEGIN: {
                vector<Expr> es;
                for (size_t i = 1; i < stxs.size(); i++) {
                    es.push_back(stxs[i]->parse(env));
                }
                return Expr(new Begin(es));
            }
            case E_IF: {
                if (stxs.size() != 4) {
                    throw RuntimeError("Wrong number of arguments for if");
                }
                return Expr(new If(stxs[1]->parse(env), stxs[2]->parse(env), stxs[3]->parse(env)));
            }
            case E_COND: {
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); i++) {
                    List* clauseList = dynamic_cast<List*>(stxs[i].get());
                    if (!clauseList) {
                        throw RuntimeError("Cond clause must be a list");
                    }
                    vector<Expr> clauseExprs;
                    for (auto& s : clauseList->stxs) {
                        clauseExprs.push_back(s->parse(env));
                    }
                    clauses.push_back(clauseExprs);
                }
                return Expr(new Cond(clauses));
            }
            case E_LAMBDA: {
                if (stxs.size() != 3) {
                    throw RuntimeError("Wrong number of arguments for lambda");
                }
                List* paramsList = dynamic_cast<List*>(stxs[1].get());
                if (!paramsList) {
                    throw RuntimeError("Lambda parameters must be a list");
                }
                vector<string> params;
                for (auto& s : paramsList->stxs) {
                    SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(s.get());
                    if (!sym) {
                        throw RuntimeError("Lambda parameters must be symbols");
                    }
                    params.push_back(sym->s);
                }
                return Expr(new Lambda(params, stxs[2]->parse(env)));
            }
            case E_DEFINE: {
                if (stxs.size() != 3) {
                    throw RuntimeError("Wrong number of arguments for define");
                }
                SymbolSyntax* varSym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (varSym) {
                    // Simple define: (define x expr)
                    return Expr(new Define(varSym->s, stxs[2]->parse(env)));
                } else {
                    // Function define: (define (f x y) body)
                    List* defList = dynamic_cast<List*>(stxs[1].get());
                    if (!defList || defList->stxs.empty()) {
                        throw RuntimeError("Invalid define syntax");
                    }
                    SymbolSyntax* funcName = dynamic_cast<SymbolSyntax*>(defList->stxs[0].get());
                    if (!funcName) {
                        throw RuntimeError("Function name must be a symbol");
                    }
                    vector<string> params;
                    for (size_t i = 1; i < defList->stxs.size(); i++) {
                        SymbolSyntax* param = dynamic_cast<SymbolSyntax*>(defList->stxs[i].get());
                        if (!param) {
                            throw RuntimeError("Parameters must be symbols");
                        }
                        params.push_back(param->s);
                    }
                    Expr lambda = Expr(new Lambda(params, stxs[2]->parse(env)));
                    return Expr(new Define(funcName->s, lambda));
                }
            }
            case E_LET: {
                if (stxs.size() != 3) {
                    throw RuntimeError("Wrong number of arguments for let");
                }
                List* bindingsList = dynamic_cast<List*>(stxs[1].get());
                if (!bindingsList) {
                    throw RuntimeError("Let bindings must be a list");
                }
                vector<pair<string, Expr>> bindings;
                for (auto& s : bindingsList->stxs) {
                    List* binding = dynamic_cast<List*>(s.get());
                    if (!binding || binding->stxs.size() != 2) {
                        throw RuntimeError("Each binding must be a list of 2 elements");
                    }
                    SymbolSyntax* var = dynamic_cast<SymbolSyntax*>(binding->stxs[0].get());
                    if (!var) {
                        throw RuntimeError("Binding variable must be a symbol");
                    }
                    bindings.push_back({var->s, binding->stxs[1]->parse(env)});
                }
                return Expr(new Let(bindings, stxs[2]->parse(env)));
            }
            case E_LETREC: {
                if (stxs.size() != 3) {
                    throw RuntimeError("Wrong number of arguments for letrec");
                }
                List* bindingsList = dynamic_cast<List*>(stxs[1].get());
                if (!bindingsList) {
                    throw RuntimeError("Letrec bindings must be a list");
                }
                vector<pair<string, Expr>> bindings;
                for (auto& s : bindingsList->stxs) {
                    List* binding = dynamic_cast<List*>(s.get());
                    if (!binding || binding->stxs.size() != 2) {
                        throw RuntimeError("Each binding must be a list of 2 elements");
                    }
                    SymbolSyntax* var = dynamic_cast<SymbolSyntax*>(binding->stxs[0].get());
                    if (!var) {
                        throw RuntimeError("Binding variable must be a symbol");
                    }
                    bindings.push_back({var->s, binding->stxs[1]->parse(env)});
                }
                return Expr(new Letrec(bindings, stxs[2]->parse(env)));
            }
            case E_SET: {
                if (stxs.size() != 3) {
                    throw RuntimeError("Wrong number of arguments for set!");
                }
                SymbolSyntax* varSym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (!varSym) {
                    throw RuntimeError("Set! variable must be a symbol");
                }
                return Expr(new Set(varSym->s, stxs[2]->parse(env)));
            }
			default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
    }

    //default: use Apply to be an expression
    vector<Expr> rand;
    for (size_t i = 1; i < stxs.size(); i++) {
        rand.push_back(stxs[i]->parse(env));
    }
    return Expr(new Apply(Expr(new Var(op)), rand));
}
}
