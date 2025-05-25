from pysmt.smtlib.parser import SmtLibParser
import sys

def parse_smt(file):
    # Load the SMT-LIB query
    parser = SmtLibParser()
    script = parser.get_script(file)

    # print(script.commands)

    formulas = [cmd.args[0] for cmd in script.commands if cmd.name == "assert"]

    # all queries have the rewrite as the first assertion
    formula = formulas[0]
    # print(formula)
    # print("Type:", type(formula))

    assert formula.is_not(), "Only support unconditional equalities atm"
    eq = formula.args()[0]
    assert eq.is_equals(), f"{eq} is not an equality"
    lhs, rhs = eq.args()
    
    print(lhs, rhs)
    
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