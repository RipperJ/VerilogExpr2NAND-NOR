# VerilogExpr2NAND-NOR
Logic Expression Compiler, with Logic Minimization, to NAND/NOR Implementation

## Introduction
This is one of the course project materials for HKUST-gz MICS 6000H Logic Design Automation of Digital Systems. This project is alive, maintained by <linfeng.du@connect.ust.hk>. Any discussion or suggestion would be greatly appreciated!

## Requirements
* Python 3.9
    * ply 3.11
    * graphviz 0.20.1
    * logging 0.5.1.2
    * pyeda 0.28.0
* Vivado 2020.2
    * *GUI is not required. Only using the standalone simulation commands.* Details shown in [runsim.sh](./runsim.sh)
        * `xvlog`
        * `xelab`
        * `xsim`

## How to Run
* Step 1: Make sure you have a valid Verilog expression in [test.v](./test.v)
    * We currently only support the following operators
        * BITWISE_AND:  "&" : bitwise AND (binary) / reduction AND (unary)
        * BITWISE_OR:   "|" : bitwise OR  (binary) / reduction OR  (unary)
        * BITWISE_NEG:  "~" : bitwise NEG (unary)       [returns the complement of a variable]
        * LOGICAL_AND:  "&&": logical AND (binary)
        * LOGICAL_OR:   "||": logical OR  (binary)
        * LOGICAL_NEG:  "!" : logical NEG (unary)       [returns a single bit]
* Step 2: `python main.py test.v`
    * This step generates the following files, including NAND/NOR implementation and the testbench.
        * [func.v](./func.v): self-defined format -- "NAND g0(in1, in2, out);"
        * [func_vivado.v](./func_vivado.v): format accepted by Vivado simulation tools -- "nand g0(out, in1, in2);"
        * [sim_func.v](./sim_func.v): testbench, end-to-end exhaustive comparison between (1) the NAND/NOR impl and (2) the original Verilog expr.
* Step 3: `./runsim.sh`
    * This step triggers the simulation flow and gives standard output in the terminal.

## NAND/NOR 123
* NAND logic:
    * ~/!: NOT(A)   ->  A NAND A
    * &/&&: A AND B ->  (A NAND B) NAND (A NAND B)
    * |/||: A OR B  ->  (A NAND A) NAND (B NAND B)
    * &/|(reduction)->  A [itself]
* NOR logic:
    * ~/!: NOT(A)   ->  A NOR A
    * &/&&: A AND B ->  (A NOR A) NOR (B NOR B)
    * |/||: A OR B  ->  (A NOR B) NOR (A NOR B)
    * &/|(reduction)->  A [itself]

## References and Interesting Links
* [PLY Document](https://www.dabeaz.com/ply/ply.html)
* [Verilog Operators](https://class.ece.uw.edu/cadta/verilog/operators.html)
* [Boolean Expr Calculator (including NAND/NOR)](https://www.dcode.fr/boolean-expressions-calculator)
* [Blog: A Quick Tutorial on Using Vivado Logic Simulation Tools](https://itsembedded.com/dhd/vivado_sim_1/)
* [From 3-input NAND to 2-input NAND gate](https://electronics.stackexchange.com/q/211801)
* [From SOP/POS (DNF/CNF) to NAND/NOR implmentation](https://www.cecs.uci.edu/~gajski/eecs31/slides/Digital_Design_-_Tech_Mapping_yajaCH5w.pdf#page=4)
* [pyeda Formal Equivalence Checking](https://pyeda.readthedocs.io/en/latest/expr.html#formal-equivalence)
* [Draw Logics with Python](https://schemdraw.readthedocs.io/en/latest/elements/logic.html)