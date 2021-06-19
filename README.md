This SAt-solver contains some changes and optimizations deviatig from the original 1960 algorithm. 
The prover works in following steps:
1. makes NNF of the negated original formula
2. performs two optimizations on NNF:
    - relations appearing in one polarization are removed and replaced with T (similar to removal of pure literals)
    - quantifiers whose variables are not used are removed (if there is a free variable in the input formula an E quantifier is added at the front)
3. performs pseudo-skolemization. Full skolem form is not used because A quantifiers are allowed anywhere in the formula (this is safe because of NNF) but E quantifiers are removed and replaced with functions or constants. In this stage new internal representation (where functions and consts and variables are identified by indices) is used.
4. creates initial Herbrand universe with constants only. 
5. converts the pseudo-skolemized form to a propositional formula (A quantifiers instantiated over the whole HU) 
6. converts propositional formula to CNF with Tseytin transformation
7. runs a DPLL sat solver (YES I know the task asks for DP BUT DPLL is a) easier b) more efficient c) I did it last year)
8. if SAT solver returns UNSAT, the formula is proven. If returns SAT and there are no A quantifiers or no functions then the formula is disproven. 
9. grow the HU by applying every function to every possible combination of arguments.
10. go back to step 5. 

