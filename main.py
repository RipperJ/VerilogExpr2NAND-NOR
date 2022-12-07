import sys
import os
import re
import ply.lex as lex
import ply.yacc as yacc
import math
import logging
import pyeda
from graphviz import Digraph
from pyeda.inter import *
from itertools import product

def loggingSetup():
    root = logging.getLogger()
    root.setLevel(logging.DEBUG)
    formatter = logging.Formatter("[%(levelname)s: %(funcName)25s() ] %(message)s")
    
    info_file_handler = logging.FileHandler(filename='parse.log', mode='w')
    info_file_handler.setLevel(logging.INFO)
    stdout_handler = logging.StreamHandler(sys.stdout)
    stdout_handler.setLevel(logging.INFO)

    handlers = [info_file_handler, stdout_handler]
    for handler in handlers:
        handler.setFormatter(formatter)
        root.addHandler(handler) 
    return root


# Lexer ------------------------------------------------------------------
# List of token names:
tokens = (
    "CONSTANT",     #
    "IDENTIFIER",   # 
    "PAR_L",        # (
    "PAR_R",        # )
    "BITWISE_AND",  # &: bit-wise AND / reduction AND
    "BITWISE_OR",   # |: bit-wise OR / reduction OR
    "BITWISE_NEG",  # ~: bit-wise NEGATION
    "LOGICAL_AND",  # &&: logical AND
    "LOGICAL_OR",   # ||: logical OR
    "LOGICAL_NEG"   # \!: logical NEGATION
)

# Regular Expression Rules for Tokens
t_PAR_L         = "\("
t_PAR_R         = "\)"
t_BITWISE_AND   = "\&"
t_BITWISE_OR    = "\|"
t_BITWISE_NEG   = "\~"
t_LOGICAL_AND   = "\&\&"
t_LOGICAL_OR    = "\|\|"
t_LOGICAL_NEG   = "\!"

#     #! constant value is tuncated to fit in <n> bits.
#     #! illegal character in binary number
#     # TODO: add "_" between numbers
#     # TODO: scientific notation
#     # TODO: decimal notation
t_CONSTANT = r"(\d*'(b|B)[0-1]+|\d*'(o|O)[0-7]+|\d*'(d|D)[0-9]+|\d*'(h|H)[0-9a-fA-F]+|\d+)"

t_IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_]*"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    
t_ignore = r" \t"

# Error handling rule
def t_error(t):
    logging.info("Illegal character '{}'".format(t.value[0]))
    t.lexer.skip(1)
    exit(1)

def test(data):
    lexer.input(data)
    # Tokenize
    while True:
        tok = lexer.token()
        if not tok:
            break      # No more input
        logging.info("{:12s}\t{}".format(tok.type, tok.value)) # , tok.lineno, tok.lexpos
        # logging.info(tok)


# Parser ------------------------------------------------------------------

class ASTnode(object):
    def __init__(self, name, left_child, right_child):
        self.name = name
        self.left_child = left_child
        self.right_child = right_child

    def get_name(self):
        return self.name
    
    '''
    1. Add full parentheses to clarify the priority, since the previous parentheses will not cause any difference in the mid-order traversal sequence
    2. Parse the mid-order result in string 
    '''
    def in_order_traverse(self, root):
        # global logic_expression
        if root != None:
            if root.left_child:
                logic.logic_list.append("(")
            self.in_order_traverse(root.left_child)
            if root.left_child:
                logic.logic_list.append(")")
            logic.logic_list.append(root.name)
            if root.right_child:
                logic.logic_list.append("(")
            self.in_order_traverse(root.right_child)
            if root.right_child:
                logic.logic_list.append(")")

precedence = (
    ('left', "LOGICAL_OR"),
    ('left', "LOGICAL_AND"),
    ('left', "BITWISE_OR"),
    ('left', "BITWISE_AND"),
    ('right', 'LOGICAL_NEG', 'BITWISE_NEG', 'UBITWISE_AND', 'UBITWISE_OR'), # with fictitious tokens
    ('left', 'PAR_L', 'PAR_R'),
)

def p_expr_identifier(p):
    "expr : IDENTIFIER"
    head[0] = ASTnode(p[1], None, None)
    p[0] = head[0]
    logging.info("Creating Node for {}".format(p[0].get_name()))
    dg.node(str(hash(p[0])), p[0].get_name(), shape="ellipse", color="green2", style="filled")
    
def p_expr_const(p):
    "expr : CONSTANT"
    head[0] = ASTnode(p[1], None, None)
    p[0] = head[0]
    logging.info("Creating Node for {}".format(p[0].get_name()))
    dg.node(str(hash(p[0])), p[0].get_name(), shape="ellipse", color="deepskyblue2", style="filled")
    
def p_expr_par(p):
    "expr : PAR_L expr PAR_R"
    p[0] = p[2]
    # No need to add viz node here.

def p_expr_binop(p):
    '''expr : expr LOGICAL_OR expr
            | expr LOGICAL_AND expr
            | expr BITWISE_OR expr
            | expr BITWISE_AND expr'''
    head[0] = ASTnode(p[2], p[1], p[3])
    p[0] = head[0]
    logging.info("Creating Node for {}".format(p[0].get_name()))
    dg.node(str(hash(p[0])), p[0].get_name(), shape="box", color="yellow2", style="filled")
    logging.info("Creating edge {} -> {}".format(p[0].get_name(), p[1].get_name()))
    dg.edge(str(hash(p[0])), str(hash(p[1])))
    try:
        logging.info("Creating edge {} -> {}".format(p[0].get_name(), p[3].get_name()))
    except Exception as e:
        logging.info("Creating edge {} -> {}".format(p[0].get_name(), p[3]))
        
    dg.edge(str(hash(p[0])), str(hash(p[3])))
    # logging.info("{} {} {}".format(p[1], p[2], p[3]))
    
def p_expr_uniop(p):
    '''expr : LOGICAL_NEG expr
            | BITWISE_NEG expr'''
    head[0] = ASTnode(p[1], None, p[2])
    p[0] = head[0]
    logging.info("Creating Node for {}".format(p[0].get_name()))
    dg.node(str(hash(p[0])), p[0].get_name(), shape="box", color="yellow2", style="filled")
    logging.info("Creating edge {} -> {}".format(p[0].get_name(), p[2].get_name()))
    dg.edge(str(hash(p[0])), str(hash(p[2])))

def p_expr_uBITWISE_AND(p):
    "expr : BITWISE_AND expr %prec UBITWISE_AND"
    head[0] = ASTnode("UNI-"+p[1], None, p[2])
    p[0] = head[0]
    logging.info("Creating Node for {}".format(p[0].get_name()))
    dg.node(str(hash(p[0])), p[0].get_name(), shape="box", color="yellow2", style="filled")
    logging.info("Creating edge {} -> {}".format(p[0].get_name(), p[2].get_name()))
    dg.edge(str(hash(p[0])), str(hash(p[2])))
    
def p_expr_uBITWISE_OR(p):
    "expr : BITWISE_OR expr %prec UBITWISE_OR"
    head[0] = ASTnode("UNI-"+p[1], None, p[2])
    p[0] = head[0]
    logging.info("Creating Node for {}".format(p[0].get_name()))
    dg.node(str(hash(p[0])), p[0].get_name(), shape="box", color="yellow2", style="filled")
    logging.info("Creating edge {} -> {}".format(p[0].get_name(), p[2].get_name()))
    dg.edge(str(hash(p[0])), str(hash(p[2])))
    
def p_error(p):
    if p:
        logging.info("Syntax error at {}!".format(p))
    else:
        logging.info("Syntax error at EOF!")
    exit(1)


'''
NOR logic:
* ~/!: NOT(A)   ->  A NAND A
* &/&&: A AND B ->  (A NAND B) NAND (A NAND B)
* |/||: A OR B  ->  (A NAND A) NAND (B NAND B)
* &/|(reduction)->  A [itself]

NAND logic:
* ~/!: NOT(A)   ->  A NOR A
* &/&&: A AND B ->  (A NOR A) NOR (B NOR B)
* |/||: A OR B  ->  (A NOR B) NOR (A NOR B)
* &/|(reduction)->  A [itself]
'''
class Logic(object):
    def __init__(self):
        self.logic_list = []
        self.e_str = ""
        self.vars = []
    def logic_tidy(self):
        for e in self.logic_list:
            if e == "(" or e == ")" or e == "~":
                self.e_str += "{} ".format(e)
            elif e == "!":
                self.e_str += "~ "
            elif e.startswith("UNI"):
                continue
            elif e == "&" or e == "&&":
                self.e_str += "& "
            elif e == "|" or e == "||":
                self.e_str += "| "
            elif re.match(t_CONSTANT, e):
                ones_place_value = re.findall(r"[0-9]", e)[-1]
                # self.e_str += "True " if ones_place_value == "1" else "False "
                self.e_str += ones_place_value + " "
            elif re.match(t_IDENTIFIER, e):
                self.e_str += e + " "
                self.vars.append(e)
                
        return self.e_str
    def get_vars(self):
        return self.vars
    
v_template = '''
module func({}output out);

// wire declaration
{}

// Gates
{}

endmodule
'''
    
vivado_template = '''
module func_vivado({}output out);

// wire declaration
{}

// Gates
{}

endmodule
'''

sim_v_template = '''
module sim_func;

// reg declaration
{}
wire out;
wire out_golden;

// error count
reg[{}:0] error_count;

// func declaration
func_vivado _func_({}.out(out));

// golden
assign out_golden = {};

initial begin
    $display("");
    error_count = 0;
    
    // enumerate all states
{}
    if (error_count == 1'b0) begin
        $display("### Verilog code generation is correct~~~");
    end
    else begin
        $display("### Fail!!!");
    end
    $display("### Error Count: %d\\n", error_count);
    // $stop;
end

endmodule
'''

def And2NandNor(f2m, gate_str, gate_num, vars_num, wire_list, notSingleLevel):
    ## initial pair
    if isinstance(f2m.xs[0], pyeda.boolalg.expr.Variable) and isinstance(f2m.xs[1], pyeda.boolalg.expr.Variable):
        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, str(f2m.xs[0].inputs[0]), str(f2m.xs[1].inputs[0]), "t{}".format(gate_num))
        wire_list.append("t{}".format(gate_num))
        gate_num += 1                
        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num) if vars_num > 2 or notSingleLevel else "out")
        wire_list.append("t{}".format(gate_num))
        gate_num += 1                
    elif isinstance(f2m.xs[0], pyeda.boolalg.expr.Variable) and isinstance(f2m.xs[1], pyeda.boolalg.expr.Complement):
        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, str(f2m.xs[0].inputs[0]), str(f2m.xs[0].inputs[0]), "t{}".format(gate_num))
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), str(f2m.xs[1].inputs[0]), "t{}".format(gate_num) if vars_num > 2 or notSingleLevel else "out")
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
    elif isinstance(f2m.xs[0], pyeda.boolalg.expr.Complement) and isinstance(f2m.xs[1], pyeda.boolalg.expr.Variable):
        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, str(f2m.xs[1].inputs[0]), str(f2m.xs[1].inputs[0]), "t{}".format(gate_num))
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), str(f2m.xs[0].inputs[0]), "t{}".format(gate_num) if vars_num > 2 or notSingleLevel else "out")
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
    elif isinstance(f2m.xs[0], pyeda.boolalg.expr.Complement) and isinstance(f2m.xs[1], pyeda.boolalg.expr.Complement):
        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, str(f2m.xs[0].inputs[0]), str(f2m.xs[1].inputs[0]), "t{}".format(gate_num) if vars_num > 2 or notSingleLevel else "out")
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
        
    ## following pairs
    if vars_num > 2:
        for i in range(2, vars_num):
            if isinstance(f2m.xs[i], pyeda.boolalg.expr.Variable):
                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), str(f2m.xs[i].inputs[0]), "t{}".format(gate_num))
                wire_list.append("t{}".format(gate_num))
                gate_num += 1                
                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num) if i < vars_num - 1 or notSingleLevel else "out")
                wire_list.append("t{}".format(gate_num))
                gate_num += 1                
            elif isinstance(f2m.xs[i], pyeda.boolalg.expr.Complement):
                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num))
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), str(f2m.xs[i].inputs[0]), "t{}".format(gate_num) if i < vars_num - 1 or notSingleLevel else "out")
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
    return gate_str, gate_num, wire_list

def Or2NandNor(f2m, gate_str, gate_num, vars_num, wire_list, notSingleLevel):
    ## initial pair
    if isinstance(f2m.xs[0], pyeda.boolalg.expr.Variable) and isinstance(f2m.xs[1], pyeda.boolalg.expr.Variable):
        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, str(f2m.xs[0].inputs[0]), str(f2m.xs[1].inputs[0]), "t{}".format(gate_num))
        wire_list.append("t{}".format(gate_num))
        gate_num += 1                
        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num) if vars_num > 2 or notSingleLevel else "out")
        wire_list.append("t{}".format(gate_num))
        gate_num += 1                
    elif isinstance(f2m.xs[0], pyeda.boolalg.expr.Variable) and isinstance(f2m.xs[1], pyeda.boolalg.expr.Complement):
        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, str(f2m.xs[0].inputs[0]), str(f2m.xs[0].inputs[0]), "t{}".format(gate_num))
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), str(f2m.xs[1].inputs[0]), "t{}".format(gate_num) if vars_num > 2 or notSingleLevel else "out")
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
    elif isinstance(f2m.xs[0], pyeda.boolalg.expr.Complement) and isinstance(f2m.xs[1], pyeda.boolalg.expr.Variable):
        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, str(f2m.xs[1].inputs[0]), str(f2m.xs[1].inputs[0]), "t{}".format(gate_num))
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), str(f2m.xs[0].inputs[0]), "t{}".format(gate_num) if vars_num > 2 or notSingleLevel else "out")
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
    elif isinstance(f2m.xs[0], pyeda.boolalg.expr.Complement) and isinstance(f2m.xs[1], pyeda.boolalg.expr.Complement):
        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, str(f2m.xs[0].inputs[0]), str(f2m.xs[1].inputs[0]), "t{}".format(gate_num) if vars_num > 2 or notSingleLevel else "out")
        wire_list.append("t{}".format(gate_num))
        gate_num += 1
        
    ## following pairs
    if vars_num > 2:
        for i in range(2, vars_num):
            if isinstance(f2m.xs[i], pyeda.boolalg.expr.Variable):
                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), str(f2m.xs[i].inputs[0]), "t{}".format(gate_num))
                wire_list.append("t{}".format(gate_num))
                gate_num += 1                
                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num) if i < vars_num - 1 or notSingleLevel else "out")
                wire_list.append("t{}".format(gate_num))
                gate_num += 1                
            elif isinstance(f2m.xs[i], pyeda.boolalg.expr.Complement):
                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num))
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), str(f2m.xs[i].inputs[0]), "t{}".format(gate_num) if i < vars_num - 1 or notSingleLevel else "out")
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
    return gate_str, gate_num, wire_list

if __name__ == '__main__':
    log = loggingSetup()
    # Build the lexer
    if len(sys.argv) < 2:
        print("Please use the command `python main.py <testcase_filename>`, e.g., `python main.py test.v`.")
        exit(1)
    elif not os.path.isfile(sys.argv[1]):
        print("File {} does not exist!".format(sys.argv[1]))
        exit(1)
    else:
        print("Lexing and Parsing expression in file {}.".format(sys.argv[1]))

    test_expr = open(sys.argv[1], "r").read()
    lexer = lex.lex(debug=True, debuglog=log)
    logging.info("------------------")
    logging.info("Lexer Result:")
    test(test_expr)
    logging.info("Lexing Success.")
    logging.info("------------------")

    logging.info("Parsing and generating AST...")

    parser = yacc.yacc(debuglog=log)
    global dg
    global head
    head = [None]
    dg = Digraph("v-expr")
    dg.graph_attr["dpi"] = '200'
    parser.parse(test_expr)
    logging.info("Parsing Success.")
    dg.save()
    logging.info("Drawing AST ...")
    dg.render("v-expr", view=False, format="png")
    
    global logic
    logic = Logic()
    head[0].in_order_traverse(head[0])
    logging.info("\n> Original Logic Expression:\n>>> {}\n>>> {}".format(logic.logic_list, " ".join(logic.logic_list)))
    logic_e_tidy = logic.logic_tidy()
    logging.info("\n> After tidying:\n>>> {}".format(logic_e_tidy))
    
    logging.info("\n------------------\n----------------- Starting Logic Minimization and Code Generation -----------------\n------------------")
    # print(logic.get_vars())
    # a, b, c = map(exprvar, 'abc')
    f1 = expr(logic_e_tidy)
    # print(f1)
    # print(f1.inputs)
    # logging.info(expr2truthtable(f1))
    f2 = f1.to_dnf()
    # print(type(f2))
    
    # [Case 1] Constant 0, e.g., "a & ~a --> 1'b0"
    if f2.is_zero():
        logging.info("Case 1: Value '0' after ESPRESSO logic minimization.")
        # 1. Standard Output Format -> func.v -----------------------------------
        with open("func.v", "w") as out_f:
            out_f.write(
                v_template.format(
                    "",
                    "",
                    "assign out = 1'b0;"
                )
            )
        logging.info("NAND gate number: 0")
        
        # 2. Vivado Verilog Format -> func_vivado.v -----------------------------------
        with open("func_vivado.v", "w") as out_f:
            out_f.write(
                vivado_template.format(
                    "",
                    "",
                    "assign out = 1'b0;"
                )
            )
            
        # 3. Simulation File -> sim_func.v -----------------------------------
        all_vars = sorted(set(re.findall(t_IDENTIFIER, test_expr)))
        l = []
        for _ in all_vars:
            l.append([0, 1])
        l = list(product(*l))
        with open("sim_func.v", "w") as out_sim_f:
            out_sim_f.write(
                sim_v_template.format(
                    "reg {};".format(", ".join([str(_) for _ in all_vars])),
                    1,
                    "",
                    test_expr,
                    "    if (out != out_golden) begin\n        error_count = error_count + 1;\n    end\n"
                )
            )
    # [Case 2] Constant 1, e.g., "a || ~a --> 1'b1"
    elif f2.is_one():
        logging.info("Case 2: Value '1' after ESPRESSO logic minimization.")
        # 1. Standard Output Format -> func.v -----------------------------------
        with open("func.v", "w") as out_f:
            out_f.write(
                v_template.format(
                    "",
                    "",
                    "assign out = 1'b1;"
                )
            )
        logging.info("NAND gate number: 0")
        
        # 2. Vivado Verilog Format -> func_vivado.v -----------------------------------
        with open("func_vivado.v", "w") as out_f:
            out_f.write(
                vivado_template.format(
                    "",
                    "",
                    "assign out = 1'b1;"
                )
            )
            
        # 3. Simulation File -> sim_func.v -----------------------------------
        all_vars = sorted(set(re.findall(t_IDENTIFIER, test_expr)))
        l = []
        for _ in all_vars:
            l.append([0, 1])
        l = list(product(*l))
        with open("sim_func.v", "w") as out_sim_f:
            out_sim_f.write(
                sim_v_template.format(
                    "reg {};".format(", ".join([str(_) for _ in all_vars])),
                    1,
                    "",
                    test_expr,
                    "    if (out != out_golden) begin\n        error_count = error_count + 1;\n    end\n"
                )
            )
    else:
        logging.info("\n> After converting to DNF:\n>>> {}".format(f2))
        # print(type(f2))
        # print(str(f2).find("And"))
        # exit(0)
        logging.info(type(f2))
        f2m, = espresso_exprs(f2)
        logging.info("\n> After logic minimization:\n>>> {}".format(f2m))
        # Convert to OR(ANDs) to NAND using:
        ## https://www.cecs.uci.edu/~gajski/eecs31/slides/Digital_Design_-_Tech_Mapping_yajaCH5w.pdf#page=5
        
        # [Case 3] Single Variable, e.g., `a & (b || ~b) --> a`
        if isinstance(f2m, pyeda.boolalg.expr.Variable):
            logging.info("Case 3: Single Variable")
            # 1. Standard Output Format -> func.v -----------------------------------
            with open("func.v", "w") as out_f:
                out_f.write(
                    v_template.format(
                        "input " + str(f2m.inputs[0]) + ", ", 
                        "",
                        "assign out = {};".format(str(f2m.inputs[0]))
                    )
                )
            logging.info("NAND gate number: 0")
            # 2. Vivado Verilog Format -> func_vivado.v -----------------------------------
            with open("func_vivado.v", "w") as out_f:
                out_f.write(
                    vivado_template.format(
                        "input " + str(f2m.inputs[0]) + ", ", 
                        "",
                        "assign out = {};".format(str(f2m.inputs[0]))
                    )
                )
            # 3. Simulation File -> sim_func.v -----------------------------------
            all_vars = sorted(set(re.findall(t_IDENTIFIER, test_expr)))
            l = []
            for _ in all_vars:
                l.append([0, 1])
            l = list(product(*l))
            sim_str = ""
            for values in l:
                for i in range(len(all_vars)):
                    sim_str += "    {} = {};\n".format(str(all_vars[i]), values[i])
                sim_str += "    #2;"
                sim_str += 'error_count = (out == out_golden) ? error_count : error_count + 1;\n    $display("{}out: %b, out_golden: %b", {}out, out_golden);\n'.format("".join([str(_) + ": %b, " for _ in f2m.inputs]), "".join([str(_) + ", " for _ in f2m.inputs]))
            with open("sim_func.v", "w") as out_sim_f:
                out_sim_f.write(
                    sim_v_template.format(
                        "reg {};".format(", ".join([str(_) for _ in all_vars])),    #! All Original Variables
                        1,
                        "".join([".{}({}), ".format(_, _) for _ in f2m.inputs]),
                        test_expr,
                        sim_str
                    )
                )
        
        # [Case 4] Single Variable, e.g., `~a & (b || ~b) --> ~a`
        elif isinstance(f2m, pyeda.boolalg.expr.Complement):
            logging.info("Case 4: Complement of Single Variable")
            # 1. Standard Output Format -> func.v -----------------------------------
            gate_str = "NAND g0({}, {}, out);\n".format(str(f2m.inputs[0]), str(f2m.inputs[0]))
            with open("func.v", "w") as out_f:
                out_f.write(
                    v_template.format(
                        "input " + str(f2m.inputs[0]) + ", ", 
                        "",
                        gate_str
                    )
                )
            logging.info("NAND gate number: 1")
            # 2. Vivado Verilog Format -> func_vivado.v -----------------------------------
            gate_str = "nand g0(out, {}, {});\n".format(str(f2m.inputs[0]), str(f2m.inputs[0]))
            with open("func_vivado.v", "w") as out_f:
                out_f.write(
                    vivado_template.format(
                        "input " + str(f2m.inputs[0]) + ", ", 
                        "",
                        gate_str
                    )
                )
            # 3. Simulation File -> sim_func.v -----------------------------------
            all_vars = sorted(set(re.findall(t_IDENTIFIER, test_expr)))
            l = []
            for _ in all_vars:
                l.append([0, 1])
            l = list(product(*l))
            sim_str = ""
            for values in l:
                for i in range(len(all_vars)):
                    sim_str += "    {} = {};\n".format(str(all_vars[i]), values[i])
                sim_str += "    #2;"
                sim_str += 'error_count = (out == out_golden) ? error_count : error_count + 1;\n    $display("{}out: %b, out_golden: %b", {}out, out_golden);\n'.format("".join([str(_) + ": %b, " for _ in f2m.inputs]), "".join([str(_) + ", " for _ in f2m.inputs]))
            with open("sim_func.v", "w") as out_sim_f:
                out_sim_f.write(
                    sim_v_template.format(
                        "reg {};".format(", ".join([str(_) for _ in all_vars])),    #! All Original Variables
                        1,
                        "".join([".{}({}), ".format(_, _) for _ in f2m.inputs]),
                        test_expr,
                        sim_str
                    )
                )
            
        # A AND B ->  (A NAND B) NAND (A NAND B)
        #! 3-input NAND: A NAND B NAND C --> 2-input NANDs: ~(A NAND B) NAND C
        # NAND among the variables: N - 1
        # NAND for inverter: 1
        # NAND gate number in total: N
        
        # [Case 5] Single-Level AND(<list of variables>), e.g., (A & B & C)
        #! e.g., ~(~a nor b) nor c -> a & ~b & ~c; if pure nand, we need 5 nands; for mixed nand/nor, we only need 4.
        # use the rule a & b & c equivalent to (a & b) & c
        # greedy leads to the optimal solution
        elif isinstance(f2m, pyeda.boolalg.expr.AndOp):
            logging.info("Case 5: Single-Level AND(<list of variables>)")
            # 1. Standard Output Format -> func.v -----------------------------------
            vars_num = len(f2m.xs)
            gate_num = 0
            gate_str = ""
            wire_list = []
            
            gate_str, gate_num, wire_list = And2NandNor(f2m, gate_str, gate_num, vars_num, wire_list, False)
            
            logging.info("NAND/NOR gate number: {}".format(gate_num))
            with open("func.v", "w") as out_f:
                out_f.write(
                    v_template.format(
                        "".join(["input " + str(_) + ", " for _ in f2m.inputs]),
                        "wire {};".format(", ".join(wire_list)),
                        gate_str
                    )
                )
            # 2. Vivado Verilog Format -> func_vivado.v -----------------------------------
            # "NAND" -> "nand"
            # "_nand_(.in0, .in1, .out)" -> "_nand_(.out, .in0, .in1)"
            gate_str = ""
            with open("func.v", "r") as in_f:
                for line in in_f.readlines():
                    if line.startswith("NAND") or line.startswith("NOR"):
                        paras = line[line.find("(") + 1:line.find(")")].split(", ")
                        gate_str += line[:line.find("(")].lower() + "(" + paras[2] + ", " + paras[0] + ", " + paras[1] + ");\n"
            with open("func_vivado.v", "w") as out_f:
                out_f.write(
                    vivado_template.format(
                        "".join(["input " + str(_) + ", " for _ in f2m.inputs]),
                        "wire {};".format(", ".join(wire_list)),
                        gate_str
                    )
                )
            # 3. Simulation File -> sim_func.v -----------------------------------
            all_vars = sorted(set(re.findall(t_IDENTIFIER, test_expr)))
            l = []
            for _ in all_vars:
                l.append([0, 1])
            l = list(product(*l))
            sim_str = ""
            for values in l:
                for i in range(len(all_vars)):
                    sim_str += "    {} = {};\n".format(str(all_vars[i]), values[i])
                sim_str += "    #2;"
                sim_str += 'error_count = (out == out_golden) ? error_count : error_count + 1;\n    $display("{}out: %b, out_golden: %b", {}out, out_golden);\n'.format("".join([str(_) + ": %b, " for _ in f2m.inputs]), "".join([str(_) + ", " for _ in f2m.inputs]))
            with open("sim_func.v", "w") as out_sim_f:
                out_sim_f.write(
                    sim_v_template.format(
                        "reg {};".format(", ".join([str(_) for _ in all_vars])),    #! All Original Variables
                        int(math.log2(len(l))),
                        "".join([".{}({}), ".format(_, _) for _ in f2m.inputs]),
                        test_expr,
                        sim_str
                    )
                )
                
        # [Case 6] Single-Level OR(<list of variables>), e.g., (A | B | C), a|||b
        elif isinstance(f2m, pyeda.boolalg.expr.OrOp) and str(f2).find("And") == -1:
            logging.info("Case 6: Single-Level OR(<list of variables>)")
            # 1. Standard Output Format -> func.v -----------------------------------
            vars_num = len(f2m.xs)
            gate_num = 0
            gate_str = ""
            wire_list = []
            
            gate_str, gate_num, wire_list = Or2NandNor(f2m, gate_str, gate_num, vars_num, wire_list, False)
            
            logging.info("NAND/NOR gate number: {}".format(gate_num))
            with open("func.v", "w") as out_f:
                out_f.write(
                    v_template.format(
                        "".join(["input " + str(_) + ", " for _ in f2m.inputs]),
                        "wire {};".format(", ".join(wire_list)),
                        gate_str
                    )
                )
            # 2. Vivado Verilog Format -> func_vivado.v -----------------------------------
            # "NAND" -> "nand"
            # "_nand_(.in0, .in1, .out)" -> "_nand_(.out, .in0, .in1)"
            gate_str = ""
            with open("func.v", "r") as in_f:
                for line in in_f.readlines():
                    if line.startswith("NAND") or line.startswith("NOR"):
                        paras = line[line.find("(") + 1:line.find(")")].split(", ")
                        gate_str += line[:line.find("(")].lower() + "(" + paras[2] + ", " + paras[0] + ", " + paras[1] + ");\n"
            with open("func_vivado.v", "w") as out_f:
                out_f.write(
                    vivado_template.format(
                        "".join(["input " + str(_) + ", " for _ in f2m.inputs]),
                        "wire {};".format(", ".join(wire_list)),
                        gate_str
                    )
                )
            # 3. Simulation File -> sim_func.v -----------------------------------
            all_vars = sorted(set(re.findall(t_IDENTIFIER, test_expr)))
            l = []
            for _ in all_vars:
                l.append([0, 1])
            l = list(product(*l))
            sim_str = ""
            for values in l:
                for i in range(len(all_vars)):
                    sim_str += "    {} = {};\n".format(str(all_vars[i]), values[i])
                sim_str += "    #2;"
                sim_str += 'error_count = (out == out_golden) ? error_count : error_count + 1;\n    $display("{}out: %b, out_golden: %b", {}out, out_golden);\n'.format("".join([str(_) + ": %b, " for _ in f2m.inputs]), "".join([str(_) + ", " for _ in f2m.inputs]))
            with open("sim_func.v", "w") as out_sim_f:
                out_sim_f.write(
                    sim_v_template.format(
                        "reg {};".format(", ".join([str(_) for _ in all_vars])),    #! All Original Variables
                        int(math.log2(len(l))),
                        "".join([".{}({}), ".format(_, _) for _ in f2m.inputs]),
                        test_expr,
                        sim_str
                    )
                )
                
        # [Case 7] Canonical DNF Format:
        # # Double-Level OR(AND(<list of variables>),)
        # test 1: ~a & ~b & ~c | ~a & ~b & c | a & ~b & c | a & b & c | a & b & ~c
        # test 2: (!a || (a && b) || (a && c) || (b && !c)) && ~b | | 1'h0 & &c
        # # (~ a && ~ b) || (~ b && c) -> (~ a nand ~ b) nand (~ b nand c)
        # # (~ a || c) && ~ b -> (~ a nor c) nor b
        # test 3: ~a & b & c | ~d | ~b & d | a & d & c
        elif isinstance(f2m, pyeda.boolalg.expr.OrOp):
            logging.info("Case 7: DNF -- `OR(AND(<list of variables>),)`")
            dnf,  = espresso_exprs(f1.to_dnf())
            cnf = dnf.to_cnf()
            logging.info("dnf: {}\ncnf: {}".format(dnf, cnf))
            #! Compare which solution leads to less gate number, between nand solution and nor solution
            
            # 1. Standard Output Format -> func.v -----------------------------------
            # [Case 7.1] NAND implementation of `Or(And,)` from dnf
            gate_num = 0
            gate_str = ""
            wire_list = []
            first_level_var_list = []
            complement_dict = {}
            
            for x in dnf.xs:
                if isinstance(x, pyeda.boolalg.expr.AndOp):
                    temp_var_list = []
                    for xx in x.xs:
                        if isinstance(xx, pyeda.boolalg.expr.Variable):
                            temp_var_list.append(str(xx.inputs[0]))
                        elif isinstance(xx, pyeda.boolalg.expr.Complement):
                            if str(xx.inputs[0]) in complement_dict:
                                temp_var_list.append(complement_dict[str(xx.inputs[0])])
                            else:
                                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, str(xx.inputs[0]), str(xx.inputs[0]), "t{}".format(gate_num))
                                wire_list.append("t{}".format(gate_num))
                                temp_var_list.append("t{}".format(gate_num))
                                complement_dict[str(xx.inputs[0])] = "t{}".format(gate_num)
                                gate_num += 1
                        else:
                            logging.error("Unexpected inner variable!")
                            exit(1)
                    gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, temp_var_list[0], temp_var_list[1], "t{}".format(gate_num))
                    wire_list.append("t{}".format(gate_num))
                    gate_num += 1
                    for index in range(2, len(temp_var_list)):
                        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num))
                        wire_list.append("t{}".format(gate_num))
                        gate_num += 1
                        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), temp_var_list[index], "t{}".format(gate_num))
                        wire_list.append("t{}".format(gate_num))
                        gate_num += 1
                    first_level_var_list.append("t{}".format(gate_num - 1))
                elif isinstance(x, pyeda.boolalg.expr.Variable):
                    if str(x.inputs[0]) in complement_dict:
                        first_level_var_list.append(complement_dict[str(x.inputs[0])])
                    else:
                        gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, str(x.inputs[0]), str(x.inputs[0]), "t{}".format(gate_num))
                        wire_list.append("t{}".format(gate_num))
                        complement_dict[str(x.inputs[0])] = "t{}".format(gate_num)
                        gate_num += 1
                        first_level_var_list.append("t{}".format(gate_num - 1))
                elif isinstance(x, pyeda.boolalg.expr.Complement):
                    first_level_var_list.append(str(x.inputs[0]))
                else:
                    logging.error("Unexpected outer variable!")
                    exit(1)
            assert len(first_level_var_list) >= 2, "variable list in Or(...): {}".format(first_level_var_list)
            if len(first_level_var_list) == 2:
                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, first_level_var_list[0], first_level_var_list[1], "out")
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
            elif len(first_level_var_list) > 2:
                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, first_level_var_list[0], first_level_var_list[1], "t{}".format(gate_num))
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
                for index in range(2, len(first_level_var_list) - 1):
                    #! 3-input NAND: A NAND B NAND C --> 2-input NANDs: ~(A NAND B) NAND C
                    gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num))
                    wire_list.append("t{}".format(gate_num))
                    gate_num += 1
                    gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), first_level_var_list[index], "t{}".format(gate_num))
                    wire_list.append("t{}".format(gate_num))
                    gate_num += 1    
                #! 3-input NAND: A NAND B NAND C --> 2-input NANDs: ~(A NAND B) NAND C
                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num))
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
                gate_str += "NAND g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), first_level_var_list[-1], "out")
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
                
            # [Case 7.2] NOR implementation of `And(Or,)` from cnf
            temp_gate_num = gate_num
            temp_gate_str = gate_str
            temp_wire_list = wire_list
            gate_num = 0    # remember
            gate_str = ""   # remember
            wire_list = []  # remember
            first_level_var_list = []
            complement_dict = {}
            
            for x in cnf.xs:
                if isinstance(x, pyeda.boolalg.expr.OrOp):
                    temp_var_list = []
                    for xx in x.xs:
                        if isinstance(xx, pyeda.boolalg.expr.Variable):
                            temp_var_list.append(str(xx.inputs[0]))
                        elif isinstance(xx, pyeda.boolalg.expr.Complement):
                            if str(xx.inputs[0]) in complement_dict:
                                temp_var_list.append(complement_dict[str(xx.inputs[0])])
                            else:
                                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, str(xx.inputs[0]), str(xx.inputs[0]), "t{}".format(gate_num))
                                wire_list.append("t{}".format(gate_num))
                                temp_var_list.append("t{}".format(gate_num))
                                complement_dict[str(xx.inputs[0])] = "t{}".format(gate_num)
                                gate_num += 1
                        else:
                            logging.error("Unexpected inner variable!")
                            exit(1)
                    gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, temp_var_list[0], temp_var_list[1], "t{}".format(gate_num))
                    wire_list.append("t{}".format(gate_num))
                    gate_num += 1
                    for index in range(2, len(temp_var_list)):
                        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num))
                        wire_list.append("t{}".format(gate_num))
                        gate_num += 1
                        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), temp_var_list[index], "t{}".format(gate_num))
                        wire_list.append("t{}".format(gate_num))
                        gate_num += 1
                    first_level_var_list.append("t{}".format(gate_num - 1))
                elif isinstance(x, pyeda.boolalg.expr.Variable):
                    if str(x.inputs[0]) in complement_dict:
                        first_level_var_list.append(complement_dict[str(x.inputs[0])])
                    else:
                        gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, str(x.inputs[0]), str(x.inputs[0]), "t{}".format(gate_num))
                        wire_list.append("t{}".format(gate_num))
                        complement_dict[str(x.inputs[0])] = "t{}".format(gate_num)
                        gate_num += 1
                        first_level_var_list.append("t{}".format(gate_num - 1))
                elif isinstance(x, pyeda.boolalg.expr.Complement):
                    first_level_var_list.append(str(x.inputs[0]))
                else:
                    logging.error("Unexpected outer variable!")
                    exit(1)
            assert len(first_level_var_list) >= 2, "variable list in Or(...): {}".format(first_level_var_list)
            if len(first_level_var_list) == 2:
                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, first_level_var_list[0], first_level_var_list[1], "out")
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
            elif len(first_level_var_list) > 2:
                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, first_level_var_list[0], first_level_var_list[1], "t{}".format(gate_num))
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
                for index in range(2, len(first_level_var_list) - 1):
                    #! 3-input NOR: A NOR B NOR C --> 2-input NORs: ~(A NOR B) NOR C
                    gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num))
                    wire_list.append("t{}".format(gate_num))
                    gate_num += 1
                    gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), first_level_var_list[index], "t{}".format(gate_num))
                    wire_list.append("t{}".format(gate_num))
                    gate_num += 1    
                #! 3-input NOR: A NOR B NOR C --> 2-input NORs: ~(A NOR B) NOR C
                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), "t{}".format(gate_num - 1), "t{}".format(gate_num))
                wire_list.append("t{}".format(gate_num))
                gate_num += 1
                gate_str += "NOR g{}({}, {}, {});\n".format(gate_num, "t{}".format(gate_num - 1), first_level_var_list[-1], "out")
                wire_list.append("t{}".format(gate_num))
                gate_num += 1            
                    
            if gate_num >= temp_gate_num:
                gate_num = temp_gate_num
                gate_str = temp_gate_str
                wire_list = temp_wire_list
            logging.info("\n> If using NAND, {} gates are needed.\n> If using NOR , {} gates are needed.\n> Prefering {} gates.".format(temp_gate_num, gate_num, "NAND" if gate_num >= temp_gate_num else "NOR"))
                
            # # Results
            logging.info("NAND/NOR gate number: {}".format(gate_num))
            with open("func.v", "w") as out_f:
                out_f.write(
                    v_template.format(
                        "".join(["input " + str(_) + ", " for _ in f2m.inputs]),
                        "wire {};".format(", ".join(wire_list)),
                        gate_str
                    )
                )
            
            # 2. Vivado Verilog Format -> func_vivado.v -----------------------------------
            # "NAND" -> "nand"
            # "_nand_(.in0, .in1, .out)" -> "_nand_(.out, .in0, .in1)"
            gate_str = ""
            with open("func.v", "r") as in_f:
                for line in in_f.readlines():
                    if line.startswith("NAND") or line.startswith("NOR"):
                        paras = line[line.find("(") + 1:line.find(")")].split(", ")
                        gate_str += line[:line.find("(")].lower() + "(" + paras[2] + ", " + paras[0] + ", " + paras[1] + ");\n"
            with open("func_vivado.v", "w") as out_f:
                out_f.write(
                    vivado_template.format(
                        "".join(["input " + str(_) + ", " for _ in f2m.inputs]),
                        "wire {};".format(", ".join(wire_list)),
                        gate_str
                    )
                )
                
            # 3. Simulation File -> sim_func.v -----------------------------------
            all_vars = sorted(set(re.findall(t_IDENTIFIER, test_expr)))
            l = []
            for _ in all_vars:
                l.append([0, 1])
            l = list(product(*l))
            sim_str = ""
            for values in l:
                for i in range(len(all_vars)):
                    sim_str += "    {} = {};\n".format(str(all_vars[i]), values[i])
                sim_str += "    #2;"
                sim_str += 'error_count = (out == out_golden) ? error_count : error_count + 1;\n    $display("{}out: %b, out_golden: %b", {}out, out_golden);\n'.format("".join([str(_) + ": %b, " for _ in f2m.inputs]), "".join([str(_) + ", " for _ in f2m.inputs]))
            with open("sim_func.v", "w") as out_sim_f:
                out_sim_f.write(
                    sim_v_template.format(
                        "reg {};".format(", ".join([str(_) for _ in all_vars])),    #! All Original Variables
                        int(math.log2(len(l))),
                        "".join([".{}({}), ".format(_, _) for _ in f2m.inputs]),
                        test_expr,
                        sim_str
                    )
                )
        else:
            logging.info("Unexpected Case!")
            exit(1)
        
        # Run Simulation with `xsim` from Xilinx Vivado --------------------------------------
        # os.system("./runsim.sh")