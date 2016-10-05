Analogy, java version

See instructions.pdf for full compilation and operation instructions. Requires installation of Prover9: https://www.cs.unm.edu/~mccune/mace4/download/


Analogy takes groups and other finite algebraic structures as input, and outputs any axioms that apply to that structure. In particular it looks for claims of the form 

	Q1 x Q2 y P(v1, v2, v3)
	
	where: 
	
	the Qs are any of the universal, existential, or "exists uniquely" (∃!) quantifiers

	v1, v2, v3 can be either x or y 

	The predicate P represents claims of the form “v1 * v2 = v3”, where “*” is the operator for the group, or some binary operator for non-groups. 

Also investigated are associativity, commutativity and the existence of identity and inverse elements. 


Example input is included. Either one or two files can be given as input. In the case of two input files, formulas and axioms for both structures will be compared. See instructions and code comments for more details. 
