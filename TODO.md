# Graph Reduction

# Compiling to Super-combinators

Compiling to Lambda Calculus has disadvantages. 
- May create multiple copies of the graph
- Loss of sharing when copying
- difficult to compile to efficient code

These issues are resolved by compiling to super combinators instead

compare with SSA compilation

http://mlton.org/pipermail/mlton/2003-January/023054.html

# Garbage Collection