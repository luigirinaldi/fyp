from pysmt.smtlib.parser import SmtLibParser
from pysmt.fnode import FNode
from pysmt.operators import (FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF,
                             SYMBOL, FUNCTION,
                             REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT,
                             PLUS, MINUS, TIMES, DIV,
                             LE, LT, EQUALS,
                             ITE,
                             TOREAL,
                             BV_CONSTANT, BV_NOT, BV_AND, BV_OR, BV_XOR,
                             BV_CONCAT, BV_EXTRACT,
                             BV_ULT, BV_ULE, BV_NEG, BV_ADD, BV_SUB,
                             BV_MUL, BV_UDIV, BV_UREM,
                             BV_LSHL, BV_LSHR,
                             BV_ROL, BV_ROR,
                             BV_ZEXT, BV_SEXT,
                             BV_SLT, BV_SLE,
                             BV_COMP,
                             BV_SDIV, BV_SREM,
                             BV_ASHR,
                             STR_CONSTANT,
                             STR_LENGTH, STR_CONCAT, STR_CONTAINS,
                             STR_INDEXOF, STR_REPLACE, STR_SUBSTR,
                             STR_PREFIXOF, STR_SUFFIXOF,
                             STR_TO_INT, INT_TO_STR,
                             STR_CHARAT,
                             ARRAY_SELECT, ARRAY_STORE, ARRAY_VALUE,
                             ALGEBRAIC_CONSTANT,
                             op_to_str)

import sys

def to_bv_lang(expr: FNode) -> str:
    match expr.node_type():
        case t if t == BV_ADD:
            a, b = expr.args()
            return f"(bw k (+ {to_bv_lang(a)} {to_bv_lang(b)}))"
        case t if t == BV_SUB:
            a, b = expr.args()
            return f"(bw k (- {to_bv_lang(a)} {to_bv_lang(b)}))"
        case t if t == BV_MUL:
            a, b = expr.args()
            return f"(bw k (* {to_bv_lang(a)} {to_bv_lang(b)}))"
        case t if t == BV_NEG:
            a = expr.args()[0]
            return f"(bw k (- {to_bv_lang(a)}))"
        case t if t == SYMBOL:
            return f"(bw k {str(expr)})"
        case t if t == BV_CONSTANT:
            return f"(bw k {expr.bv_signed_value()})"
        case t if t in [BV_XOR, BV_AND, BV_NOT, BV_OR, ITE]:
            raise AssertionError(f"{op_to_str(t)} unsupported")
        case other:
            print(other, str(expr))
            raise ValueError("unsupported node type", expr, op_to_str(other))
            return str(expr)
    # print(expr.node_type(), expr.bv_width())
    # for child in expr.args():
    #     to_bv_lang(child)

def parse_smt(file) -> tuple[str, str]:
    # Load the SMT-LIB query
    parser = SmtLibParser()
    script = parser.get_script(file)

    # print(script.commands)

    formulas = [cmd.args[0] for cmd in script.commands if cmd.name == "assert"]

    # all queries have the rewrite as the first assertion
    formula = formulas[0]
    print(formula)
    # print("Type:", type(formula))

    assert formula.is_not(), "Only support unconditional equalities atm"
    eq = formula.args()[0]
    assert eq.is_equals(), f"{eq} is not an equality"
    lhs, rhs = eq.args()
    
    
    print(lhs, '->', bw_lhs:=to_bv_lang(lhs))
    print(rhs, '->', bw_rhs:=to_bv_lang(rhs))
    
    return (bw_lhs, bw_rhs)
    # breakpoint()
    # print(formula)
    # print(list_file, formula)
    # Traverse AST (example)
    # for sub in formula.get_atoms():
    #     print("  Atom:", sub)
    
if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python parse_smt.py query.smt2")
        sys.exit(1)
    list_file = sys.argv[1]
    with open(list_file, 'r') as f:
        parse_smt(f)