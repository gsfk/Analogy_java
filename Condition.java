import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap; 

//Class to represent predicates, 
//code for brute force generation of all variable orderings for a predicate, 
//formula generation code, substitution code for uniqueness quantifiers

public class Condition{

	public Predicate predicate;

	public Map<Quantifier, Boolean> values;

	//human readable predicate name
	public String prettyName;

	//name for prover
	public String proverName;

	//relation name, why is this repeated here?
	public String relation;

	//arity = 3 always 
	public int arity = 3; 

	//arity 3 enforced here, should always have size 3	
	public char[] orderedVariables; 


	public Condition (Predicate p, String n, String r, char[] o){
		predicate = p;
		values= new HashMap<Quantifier, Boolean>(); 
		prettyName = n;
		relation = r;
		orderedVariables = o;
	}

	//returns true/false values for a particular domain, predicate and elements
	public boolean checkCondition(AlgebraicStructure g, String x, String y){
		return this.predicate.apply(g,x,y);
	}

	//function-style prover name, assumes arity 3
	public String proverName(){
		String s = "";
		s += '(';
		s += orderedVariables[0];
		s += " ";
		s += relation;
		s += " ";
		s += orderedVariables[1];
		s += " = ";
		s += orderedVariables[2];
		s += ')';
		return s;
	}

	//number of x variables in condition
	public int numberOf_x_Terms(){
		int xCount = 0;
		for (int i = 0; i< arity; i++){
			if (this.orderedVariables[i] == 'x'){
				xCount++;
			}
		}
		return xCount;
	}

	//number of y variables in condition
	public int numberOf_y_Terms(){
		int yCount = 0;
		for (int i = 0; i< arity; i++){
			if (this.orderedVariables[i] == 'y'){
				yCount++;
			}
		}
		return yCount;
	}

	public String getPrettyFormulaName(Quantifier q){
		switch(q){
		case FOR_ALL_X_FOR_ALL_Y:
			return "∀x ∀y " + prettyName;
		case FOR_ALL_X_EXISTS_Y:
			return "∀x ∃y " + prettyName;
		case EXISTS_X_FOR_ALL_Y:
			return "∃x ∀y " + prettyName;
		case EXISTS_X_EXISTS_Y:
			return "∃x ∃y " + prettyName;
		case FOR_ALL_X_EXISTS_UNIQUE_Y:  
			return "∀x ∃!y " + prettyName;
		case EXISTS_X_EXISTS_UNIQUE_Y:
			return "∃x ∃!y " + prettyName;
		case EXISTS_UNIQUE_X_FOR_ALL_Y:
			return "∃!x ∀y " + prettyName;
		case EXISTS_UNIQUE_X_EXISTS_Y:
			return "∃!x ∃y " + prettyName;
		case EXISTS_UNIQUE_X_EXISTS_UNIQUE_Y:
			return "∃!x ∃!y " + prettyName;
		default:
			System.err.println("quantifier read error");
			return "";
		}
	}	


	public String getProverFormulaName(Quantifier q){
		String formulaProverName = "";

		//variables in predicate in they order they appear, 
		//allows us to distinguish between "x * x = y" and "x * y = x".
		// as coded, arity 3 enforced here
		char a = this.orderedVariables[0];
		char b = this.orderedVariables[1];
		char c = this.orderedVariables[2];

		//number of terms bound by uniqueness quantifier
		int numUniqueValues;

		//print counters
		int termsPrinted = 0;
		int conjunctionsToPrint;

		switch(q){
		case FOR_ALL_X_FOR_ALL_Y:
			return "all x all y " + this.proverName();

		case FOR_ALL_X_EXISTS_Y:
			return "all x exists y " + this.proverName();

		case EXISTS_X_FOR_ALL_Y:
			return "exists x all y " + this.proverName();

		case EXISTS_X_EXISTS_Y:
			return "exists x exists y " + this.proverName();

		case FOR_ALL_X_EXISTS_UNIQUE_Y:  
			numUniqueValues = this.numberOf_x_Terms();
			conjunctionsToPrint = numUniqueValues - 1;

			formulaProverName += "all x exists y (";
			formulaProverName += this.proverName();
			formulaProverName += " & all z (";

			//print subterms
			if (a == 'x'){
				formulaProverName += "((z " + this.relation + " " + b + " = " + c + ") -> z = x)";
				termsPrinted++;
			}
			if (termsPrinted > 0 && conjunctionsToPrint > 0){
				formulaProverName += " & ";
				conjunctionsToPrint --;
			}
			if (b == 'x'){
				formulaProverName += "((" + a + " " + this.relation + " z " + " = " + c + ") -> z = x)";
				termsPrinted++;
			}
			if (termsPrinted > 0 && conjunctionsToPrint > 0){
				formulaProverName += " & ";
				conjunctionsToPrint --;
			}
			if (c == 'x'){
				formulaProverName += "((" + a + " " + this.relation + " " + b + " = z) -> z = x)";

			}
			formulaProverName += "))";
			return formulaProverName;


		case EXISTS_X_EXISTS_UNIQUE_Y:
			numUniqueValues = this.numberOf_y_Terms();
			conjunctionsToPrint = numUniqueValues - 1;

			formulaProverName += "exists x exists y (";
			formulaProverName += this.proverName();
			formulaProverName += " & all z (";

			//subterms
			if (a == 'y'){
				formulaProverName += "((z " + this.relation + " " + b + " = " + c + ") -> z = y)";
				termsPrinted++;
			}
			if (termsPrinted > 0 && conjunctionsToPrint > 0){
				formulaProverName += " & ";
				conjunctionsToPrint --;
			}
			if (b == 'y'){
				formulaProverName+= "((" + a + " " + this.relation + " z " + " = " + c + ") -> z = y)";
				termsPrinted++;
			}
			if (termsPrinted > 0 && conjunctionsToPrint > 0){
				formulaProverName += " & ";
				conjunctionsToPrint --;
			}
			if (c == 'y'){
				formulaProverName+= "((" + a + " " + this.relation + " " + b + " = z) -> z = y)";
				termsPrinted++;
			}
			formulaProverName+= "))";
			return formulaProverName;


		case EXISTS_UNIQUE_X_FOR_ALL_Y:
			numUniqueValues = this.numberOf_x_Terms();
			conjunctionsToPrint = numUniqueValues - 1;

			formulaProverName += "exists x all y (";
			formulaProverName += this.proverName();
			formulaProverName += " & all z (";

			//subterms
			if (a == 'x'){
				formulaProverName += "((z " + this.relation + " " + b + " = " + c + ") -> z = x)";
				termsPrinted++;
			}
			if (termsPrinted > 0 && conjunctionsToPrint > 0){
				formulaProverName += " & ";
				conjunctionsToPrint --;
			}
			if (b == 'x'){
				formulaProverName+= "((" + a + " " + this.relation + " z " + " = " + c + ") -> z = x)";
				termsPrinted++;
			}
			if (termsPrinted > 0 && conjunctionsToPrint > 0){
				formulaProverName += " & ";
				conjunctionsToPrint --;
			}			
			if (c == 'x'){
				formulaProverName+= "((" + a + " " + this.relation + " " + b + " = z) -> z = x)";
				termsPrinted++;
			}
			formulaProverName+= "))";
			return formulaProverName;


		case EXISTS_UNIQUE_X_EXISTS_Y:
			numUniqueValues = this.numberOf_x_Terms();
			conjunctionsToPrint = numUniqueValues - 1;

			formulaProverName+=	"exists x exists y (";			
			formulaProverName+=	this.proverName();
			formulaProverName+=	" & all z (";		

			//subterms	
			if (a == 'x'){
				formulaProverName+= "((z " + this.relation + " " + b + " = " + c + ") -> z = x)";
				termsPrinted++;		
			}
			if (termsPrinted > 0 && conjunctionsToPrint > 0){
				formulaProverName += " & ";
				conjunctionsToPrint --;
			}
			if (b == 'x'){
				formulaProverName+= "((" + a + " " + this.relation + " z " + " = " + c + ") -> z = x)";
				termsPrinted++;
			}
			if (termsPrinted > 0 && conjunctionsToPrint > 0){
				formulaProverName += " & ";
				conjunctionsToPrint --;
			}
			if (c == 'x'){
				formulaProverName += "((" + a + " " + this.relation + " " + b + "= z) -> z = x)";
			}
			formulaProverName += "))";
			return formulaProverName;


		case EXISTS_UNIQUE_X_EXISTS_UNIQUE_Y:
			formulaProverName+= "exists x exists y (" + this.proverName();
			formulaProverName+= " & all u all v all w((";
			formulaProverName+= "u " + this.relation + " v = w) -> (u = " + a + " & v = " + b + " & w = " + c + ")))";

			return formulaProverName;

		default:
			System.err.println("quantifier read error");
			return "";
		}
	}	

	//input: array of Conditions, Alg structure g
	//output: all true formulas (quantifier / predicate combinations)

	public static ArrayList<Formula> generateFormulas (ArrayList<Condition> predicates, AlgebraicStructure g){
		ArrayList<Formula> formulas = new ArrayList<Formula>();

		//human readable names
		String prettyFormulaName = "";
		//String prettyQuantifierName = "";

		//names in prover syntax
		String proverFormulaName = "";
		//String proverQuantifierName = "";

		for (Condition p : predicates){

			for (Quantifier q : p.values.keySet()){

				//get formula if true, else skip
				if (p.values.get(q)){

					//get formula strings
					prettyFormulaName = p.getPrettyFormulaName(q);
					proverFormulaName = p.getProverFormulaName(q);		

					//add to array
					Formula f  = new Formula(prettyFormulaName, proverFormulaName);
					formulas.add(f);
				}

			}//end loop through quantifiers

		}//end loop through all conditions 

		//begin extended properties

		for (Properties p : g.extraProperties.keySet()){
			
			//if formula is true, add it to the list
			if (g.extraProperties.get(p)){
				switch(p){
				case ASSOCIATIVITY: 
					prettyFormulaName = "∀x ∀y ∀z ((x " + g.relation + " y) " + g.relation + " z = x " + g.relation + " (y " + g.relation + " z)) (associativity)";
					proverFormulaName = "all x all y all z ((x " + g.relation + " y) " + g.relation + " z = x " + g.relation + " (y " + g.relation + " z))";
					break;
					
				case COMMUTATIVITY:
					prettyFormulaName = "∀x ∀y ((x " + g.relation + " y) = (y " + g.relation + " x)) (commutativity)";
					proverFormulaName = "all x all y ((x " + g.relation + " y) = (y " + g.relation + " x))";
					break;

				case CLOSURE:
					prettyFormulaName = "∀x ∀y ∃z (x " + g.relation + " y = z) (closure)";
					proverFormulaName = "all x all y exists z (x " + g.relation + " y = z)";
					break;

				case LEFT_IDENTITY_LEFT_INVERSE:
					prettyFormulaName = "∃x ∀y ∃z ((x " + g.relation + " y = y) & (z " + g.relation + " y = x)) (left identity, left inverse)";
					proverFormulaName = "exists x all y exists z ((x " + g.relation + " y = y) & (z " + g.relation + " y = x))";
					break;

				case RIGHT_IDENTITY_LEFT_INVERSE:
					prettyFormulaName = "∃x ∀y ∃z ((y " + g.relation + " x = y) & (z " + g.relation + " y = x)) (right identity, left inverse)";
					proverFormulaName = "exists x all y exists z ((y " + g.relation + " x = y) & (z " + g.relation + " y = x))";
					break;

				case LEFT_IDENTITY_RIGHT_INVERSE:
					prettyFormulaName ="∃x ∀y ∃z ((x " + g.relation + " y = y) & (y " + g.relation + " z = x)) (left identity, right inverse)";
					proverFormulaName = "exists x all y exists z ((x " + g.relation + " y = y) & (y " + g.relation + " z = x))";
					break;

				case RIGHT_IDENTITY_RIGHT_INVERSE:
					prettyFormulaName = "∃x ∀y ∃z ((y " + g.relation + " x = y) & (y " + g.relation + " z = x)) (right identity, right inverse)";
					proverFormulaName = "exists x all y exists z ((y " + g.relation + " x = y) & (y " + g.relation + " z = x))";
					break;

					default: 
						;//do nothing
				}//end switch
				
				//create formula and add 
				Formula f  = new Formula(prettyFormulaName, proverFormulaName);
				formulas.add(f);
				
			}//end if
			//else formula is false, skip 

		}//end extended properties

		return formulas;
	}



	//STATIC METHODS

	//brute force generation of all possible predicates
	public static ArrayList<Condition> returnAllPredicates(String relation){
		ArrayList <Condition> allPredicates = new ArrayList<Condition>();
		Condition c;
		Predicate p;
		String readablePredicateName = "";
		char[] orderedVariables;

		//x * x = x
		p = Predicate.P1;
		readablePredicateName += "x ";
		readablePredicateName += relation;
		readablePredicateName += " x = x";
		orderedVariables = new char[]{'x','x','x'};

		//construct new Condition object, add to collection
		c = new Condition (p, readablePredicateName, relation, orderedVariables);
		allPredicates.add(c);

		//blank predicate name for next round
		readablePredicateName = "";


		//x * x = y
		p = Predicate.P2;
		readablePredicateName += "x ";
		readablePredicateName += relation;
		readablePredicateName += " x = y";
		orderedVariables = new char[]{'x','x','y'};

		//construct new, add	
		c = new Condition (p, readablePredicateName, relation, orderedVariables);
		allPredicates.add(c);

		readablePredicateName = "";


		//x * y = x
		p = Predicate.P3;
		readablePredicateName += "x ";
		readablePredicateName += relation;
		readablePredicateName += " y = x";
		orderedVariables = new char[]{'x','y','x'};

		//construct new, add	
		c = new Condition (p, readablePredicateName, relation, orderedVariables);
		allPredicates.add(c);

		readablePredicateName = "";    	


		//x * y = y
		p = Predicate.P4;
		readablePredicateName += "x ";
		readablePredicateName += relation;
		readablePredicateName += " y = y";
		orderedVariables = new char[]{'x','y','y'};

		//construct new, add	
		c = new Condition (p, readablePredicateName, relation, orderedVariables);
		allPredicates.add(c);

		readablePredicateName = "";


		//y * x = x
		p = Predicate.P5;
		readablePredicateName += "y ";
		readablePredicateName += relation;
		readablePredicateName += " x = x";
		orderedVariables = new char[]{'y','x','x'};

		//construct new, add	
		c = new Condition (p, readablePredicateName, relation, orderedVariables);
		allPredicates.add(c);

		readablePredicateName = "";


		//y * x = y
		p = Predicate.P6;
		readablePredicateName += "y ";
		readablePredicateName += relation;
		readablePredicateName += " x = y";
		orderedVariables = new char[]{'y','x','y'};

		//construct new, add	
		c = new Condition (p, readablePredicateName, relation, orderedVariables);
		allPredicates.add(c);

		readablePredicateName = "";


		//y * y = x
		p = Predicate.P7;
		readablePredicateName += "y ";
		readablePredicateName += relation;
		readablePredicateName += " y = x";
		orderedVariables = new char[]{'y','y','x'};

		//construct new, add	
		c = new Condition (p, readablePredicateName, relation, orderedVariables);
		allPredicates.add(c);

		return allPredicates;
	}

}


