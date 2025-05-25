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

# function to convert between smt-lib and bw_lang
def to_bw_lang(expr: FNode) -> str:
    match expr.node_type():
        case t if t == BV_ADD:
            a, b = expr.args()
            return f"(bw k (+ {to_bw_lang(a)} {to_bw_lang(b)}))"
        case t if t == BV_SUB:
            a, b = expr.args()
            return f"(bw k (- {to_bw_lang(a)} {to_bw_lang(b)}))"
        case t if t == BV_MUL:
            a, b = expr.args()
            return f"(bw k (* {to_bw_lang(a)} {to_bw_lang(b)}))"
        case t if t == BV_NEG:
            a = expr.args()[0]
            return f"(bw k (- {to_bw_lang(a)}))"
        case t if t == SYMBOL:
            symb = str(expr).replace('%', 'var_')
            return f"(bw k {symb})"
        case t if t == BV_CONSTANT:
            return f"(bw k {expr.bv_signed_value()})"
        case t if t == BV_LSHL:
            a, b = expr.args()
            return f"(bw k (<< {to_bw_lang(a)} {to_bw_lang(b)}))"
        case t if t == BV_LSHR:
            a, b = expr.args()
            return f"(bw k (>> {to_bw_lang(a)} {to_bw_lang(b)}))"
        case t if t == BV_XOR:
            a, b = expr.args()
            return f"(bw k (xor {to_bw_lang(a)} {to_bw_lang(b)}))"
        case t if t == BV_OR:
            a, b = expr.args()
            return f"(bw k (| {to_bw_lang(a)} {to_bw_lang(b)}))"
        case t if t == BV_AND:
            a, b = expr.args()
            return f"(bw k (& {to_bw_lang(a)} {to_bw_lang(b)}))"
        case t if t == BV_NOT:
            return f"(bw k (~ {to_bw_lang(expr.arg(0))}))"
        case t if t in [ITE, BV_ASHR]:
            raise AssertionError(f"{op_to_str(t)} unsupported")
        case other:
            print(other, str(expr))
            raise ValueError("unsupported node type", expr, op_to_str(other))

# convert preconditions into bw_lang
# necessary because preconditions are currently handled separately
def precond_to_bw_lang(expr: FNode) -> str:
    match expr.node_type():
        case t if t == BV_ULE:
            a, b = expr.args()
            return f"(<= {to_bw_lang(a)} {to_bw_lang(b)})"
        case t if t == BV_ULT:
            a, b = expr.args()
            return f"(< {to_bw_lang(a)} {to_bw_lang(b)})"
        case t if t in [EQUALS, BV_SLE, BV_SLT]:
            raise AssertionError(f"{op_to_str(t)} unsupported")
        case other:
            print(other, str(expr))
            raise ValueError("unsupported node type", expr, op_to_str(other))

def parse_smt(file) -> tuple[str, str, list[str]]:
    # Load the SMT-LIB query
    parser = SmtLibParser()
    script = parser.get_script(file)

    # print(script.commands)

    formulas = [cmd.args[0] for cmd in script.commands if cmd.name == "assert"]

    # all queries have the rewrite as the first assertion
    formula = formulas[0]
    # print(formula)
    # print("Type:", type(formula))

    if formula.is_not():
        # This is the case where there are no preconditions necessary for the equality to hold
        # Look for specifically a rewrite of the form (! (lhs = rhs))
        # ignore the ones that are (! (lhs <-> rhs))
        eq = formula.args()[0]
        assert eq.is_equals(), f"{eq} is not an equality"
        lhs, rhs = eq.args()
        
        return (to_bw_lang(lhs), to_bw_lang(rhs), [])
    elif formula.is_and():
        # And means there are preconditions
        # print(formula.args())
        
        rewrite = None
        preconditions = []
        for i, expr in enumerate(formula.args()):
            # Look for specifically a rewrite of the form (! (lhs = rhs))
            # ignore the ones that are (! (lhs <-> rhs))
            if expr.is_not() and expr.args()[0].is_equals():
                assert rewrite is None, f"More than one rewrite candidate: {rewrite}, {expr}"
                rewrite = expr.args()[0].args()
            else:
                preconditions.append(expr)
        
        assert rewrite is not None, f"Rewrite not found in {formula}"
        
        # print("rewrite", rewrite)
        # print("preconditions", preconditions)
        
        
        lhs_out, rhs_out = to_bw_lang(rewrite[0]), to_bw_lang(rewrite[1])
        precond_out = [precond_to_bw_lang(e) for e in preconditions]
        
        return lhs_out, rhs_out, precond_out
    else:
        # print(op_to_str(formula.node_type()))
        # print(formula)
        raise AssertionError(f"skipping {formula}")
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