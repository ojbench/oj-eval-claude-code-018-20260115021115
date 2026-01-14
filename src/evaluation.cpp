/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 *
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp"
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (auto& r : rands) {
        args.push_back(r->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            // Return the primitive as a procedure
            ExprType primType = primitives[x];
            // Create a closure that represents this primitive
            // For now, we'll create special procedure values for primitives
            // This is handled by returning a special marker
            throw RuntimeError("Primitive " + x + " used as variable without being called");
        }
        throw RuntimeError("Undefined variable: " + x);
    }
    return matched_value;
}

// Helper function to add two numeric values (int or rational)
Value addValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 + n2);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
        int den = r1->denominator * r2->denominator;
        return RationalV(num, den);
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = n1 * r2->denominator + r2->numerator;
        return RationalV(num, r2->denominator);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int num = r1->numerator + n2 * r1->denominator;
        return RationalV(num, r1->denominator);
    }
    throw RuntimeError("Cannot add non-numeric values");
}

// Helper function to subtract two numeric values
Value subtractValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 - n2);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
        int den = r1->denominator * r2->denominator;
        return RationalV(num, den);
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = n1 * r2->denominator - r2->numerator;
        return RationalV(num, r2->denominator);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int num = r1->numerator - n2 * r1->denominator;
        return RationalV(num, r1->denominator);
    }
    throw RuntimeError("Cannot subtract non-numeric values");
}

// Helper function to multiply two numeric values
Value multiplyValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 * n2);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = r1->numerator * r2->numerator;
        int den = r1->denominator * r2->denominator;
        return RationalV(num, den);
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = n1 * r2->numerator;
        return RationalV(num, r2->denominator);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int num = r1->numerator * n2;
        return RationalV(num, r1->denominator);
    }
    throw RuntimeError("Cannot multiply non-numeric values");
}

// Helper function to divide two numeric values
Value divideValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        if (n1 % n2 == 0) {
            return IntegerV(n1 / n2);
        }
        return RationalV(n1, n2);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        int num = r1->numerator * r2->denominator;
        int den = r1->denominator * r2->numerator;
        return RationalV(num, den);
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        int num = n1 * r2->denominator;
        int den = r2->numerator;
        return RationalV(num, den);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        int num = r1->numerator;
        int den = r1->denominator * n2;
        return RationalV(num, den);
    }
    throw RuntimeError("Cannot divide non-numeric values");
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    return addValues(rand1, rand2);
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    return subtractValues(rand1, rand2);
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    return multiplyValues(rand1, rand2);
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    return divideValues(rand1, rand2);
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.size() == 0) {
        return IntegerV(0);
    }
    Value result = IntegerV(0);
    for (size_t i = 0; i < args.size(); i++) {
        if (i == 0) {
            result = args[i];
        } else {
            result = addValues(result, args[i]);
        }
    }
    return result;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.size() == 0) {
        throw RuntimeError("- requires at least 1 argument");
    }
    if (args.size() == 1) {
        // Negation
        if (args[0]->v_type == V_INT) {
            return IntegerV(-(dynamic_cast<Integer*>(args[0].get())->n));
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            return RationalV(-r->numerator, r->denominator);
        }
        throw RuntimeError("Cannot negate non-numeric value");
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = subtractValues(result, args[i]);
    }
    return result;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.size() == 0) {
        return IntegerV(1);
    }
    Value result = IntegerV(1);
    for (size_t i = 0; i < args.size(); i++) {
        result = multiplyValues(result, args[i]);
    }
    return result;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.size() == 0) {
        throw RuntimeError("/ requires at least 1 argument");
    }
    if (args.size() == 1) {
        // Reciprocal
        if (args[0]->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(args[0].get())->n;
            if (n == 0) throw RuntimeError("Division by zero");
            return RationalV(1, n);
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            if (r->numerator == 0) throw RuntimeError("Division by zero");
            return RationalV(r->denominator, r->numerator);
        }
        throw RuntimeError("Cannot compute reciprocal of non-numeric value");
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = divideValues(result, args[i]);
    }
    return result;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;

        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }

        long long result = 1;
        long long b = base;
        int exp = exponent;

        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }

        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2) {
        throw RuntimeError("< requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2) {
        throw RuntimeError("<= requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2) {
        throw RuntimeError("= requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2) {
        throw RuntimeError(">= requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2) {
        throw RuntimeError("> requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    if (args.size() == 0) {
        return NullV();
    }
    Value result = NullV();
    for (int i = args.size() - 1; i >= 0; i--) {
        result = PairV(args[i], result);
    }
    return result;
}

Value IsList::evalRator(const Value &rand) { // list?
    if (rand->v_type == V_NULL) {
        return BooleanV(true);
    }
    if (rand->v_type != V_PAIR) {
        return BooleanV(false);
    }
    // Check if it's a proper list (ends with null)
    Value current = rand;
    while (current->v_type == V_PAIR) {
        Pair* p = dynamic_cast<Pair*>(current.get());
        current = p->cdr;
    }
    return BooleanV(current->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("car requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("cdr requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    // We need to modify the pair in place
    // Since Pair is shared_ptr, we can modify it directly
    const_cast<Pair*>(p)->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    // We need to modify the pair in place
    const_cast<Pair*>(p)->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    if (es.size() == 0) {
        return VoidV();
    }
    Value result = VoidV();
    for (auto& expr : es) {
        result = expr->eval(e);
    }
    return result;
}

// Helper function to convert Syntax to Value
Value syntaxToValue(Syntax &s, Assoc &env) {
    if (auto num = dynamic_cast<Number*>(s.get())) {
        return IntegerV(num->n);
    } else if (auto rat = dynamic_cast<RationalSyntax*>(s.get())) {
        return RationalV(rat->numerator, rat->denominator);
    } else if (auto str = dynamic_cast<StringSyntax*>(s.get())) {
        return StringV(str->s);
    } else if (auto sym = dynamic_cast<SymbolSyntax*>(s.get())) {
        return SymbolV(sym->s);
    } else if (auto trueSyn = dynamic_cast<TrueSyntax*>(s.get())) {
        return BooleanV(true);
    } else if (auto falseSyn = dynamic_cast<FalseSyntax*>(s.get())) {
        return BooleanV(false);
    } else if (auto list = dynamic_cast<List*>(s.get())) {
        if (list->stxs.empty()) {
            return NullV();
        }
        // Build pairs from the list
        Value result = NullV();
        for (int i = list->stxs.size() - 1; i >= 0; i--) {
            result = PairV(syntaxToValue(list->stxs[i], env), result);
        }
        return result;
    }
    throw RuntimeError("Unknown syntax type in quote");
}

Value Quote::eval(Assoc& e) {
    return syntaxToValue(s, e);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    Value result = BooleanV(true);
    for (auto& expr : rands) {
        result = expr->eval(e);
        if (result->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(result.get());
            if (!b->b) {
                return BooleanV(false);
            }
        }
    }
    if (rands.size() == 0) {
        return BooleanV(true);
    }
    return result;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    for (auto& expr : rands) {
        Value result = expr->eval(e);
        if (result->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(result.get());
            if (!b->b) {
                continue;
            }
        }
        // Either not false or not a boolean
        if (rands.size() == 0) {
            return BooleanV(false);
        }
        return result;
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    if (rand->v_type == V_BOOL) {
        bool b = dynamic_cast<Boolean*>(rand.get())->b;
        return BooleanV(!b);
    }
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value condValue = cond->eval(e);
    bool isTrue = true;
    if (condValue->v_type == V_BOOL) {
        Boolean* b = dynamic_cast<Boolean*>(condValue.get());
        isTrue = b->b;
    }
    if (isTrue) {
        return conseq->eval(e);
    } else {
        return alter->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    for (auto& clause : clauses) {
        if (clause.size() == 0) {
            continue;
        }
        // Check if this is the else clause (symbol "else")
        bool isElse = false;
        if (clause.size() >= 1) {
            // Check if the first element is a symbol "else"
            // This requires checking if it's a Var expression that evaluates to "else"
            // For now, we'll evaluate it
            Value condValue = clause[0]->eval(env);
            bool isTrue = true;
            if (condValue->v_type == V_BOOL) {
                Boolean* b = dynamic_cast<Boolean*>(condValue.get());
                isTrue = b->b;
            }

            if (isTrue) {
                if (clause.size() == 1) {
                    // Single expression in clause, return the condition value
                    return condValue;
                }
                Value result = VoidV();
                for (size_t i = 1; i < clause.size(); i++) {
                    result = clause[i]->eval(env);
                }
                return result;
            }
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value ratorValue = rator->eval(e);
    if (ratorValue->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}

    Procedure* clos_ptr = dynamic_cast<Procedure*>(ratorValue.get());

    //TODO: TO COMPLETE THE ARGUMENT PARSER LOGIC
    std::vector<Value> args;
    for (auto& r : rand) {
        args.push_back(r->eval(e));
    }
    if (args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");

    //TODO: TO COMPLETE THE PARAMETERS' ENVIRONMENT LOGIC
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < clos_ptr->parameters.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

// Global environment pointer - we need to define this as extern in Def.hpp
extern Assoc global_env;

Value Define::eval(Assoc &env) {
    Value value = e->eval(env);
    // Check if variable already exists in global environment
    // For simplicity, we just add it to the current environment
    // In a real implementation, define should only work at top level
    extend(var, value, env);
    return VoidV();
}

Value Let::eval(Assoc &env) {
    // Create new environment with bindings
    Assoc newEnv = env;
    for (auto& binding : bind) {
        Value value = binding.second->eval(env);
        newEnv = extend(binding.first, value, newEnv);
    }
    return body->eval(newEnv);
}

Value Letrec::eval(Assoc &env) {
    // Create new environment with placeholders
    Assoc newEnv = env;
    for (auto& binding : bind) {
        newEnv = extend(binding.first, NullV(), newEnv);
    }

    // Now evaluate the expressions in the new environment
    for (auto& binding : bind) {
        Value value = binding.second->eval(newEnv);
        modify(binding.first, value, newEnv);
    }

    return body->eval(newEnv);
}

Value Set::eval(Assoc &env) {
    Value value = e->eval(env);
    modify(var, value, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }

    return VoidV();
}
