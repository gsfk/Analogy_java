import java.io.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

//Class to represent the domain, most of the search code also resides here




public class AlgebraicStructure{

	//domain elements
	private ArrayList<String> elements;

	//number of elements
	private int order;

	//fact table
	private ArrayList<ArrayList<String>> facts;

	//number of facts in table
	private int numFacts;

	//relation name
	public String relation;

	//"extra properties" map
	public Map<Properties, Boolean> extraProperties;

	//constructor
	public AlgebraicStructure(ArrayList<String> e, String r, ArrayList<ArrayList<String>> f){
		elements = e;
		relation = r;
		facts = f;
		order = elements.size();
		numFacts = facts.size();
		extraProperties= new HashMap<Properties, Boolean>(); 
	}


	public String factTableLookup(String a, String b){
		ArrayList<String> currentFact;

		//iterate through fact table
		for (int i=0; i < this.numFacts; i ++){

			//get fact, which is a vector of size arity
			currentFact = this.facts.get(i);

			//pattern match on a fact (a,b,x), return x
			//*** REQUIRES ARITY 3 ***
			if (currentFact.get(0).equals(a) && currentFact.get(1).equals(b)){
				return currentFact.get(2);
			}    		
		} //reached end of fact table here


		//if you made it here, fact not found
		//input domain is required to be complete and fully defined,
		//so as long as we ask about elements of the domain, we should always find facts

		//TODO: exception?
		//System.out.println("fact not found, x = " + a + ", y = " + b);

		return "";	
	}

	//CODE FOR EXHAUSTIVE CHECKING OF QUANTIFICATION FOR A GIVEN PREDICATE

	/* Checks all cases of the form Q1x Q2y: P(v1, v2, v3)
	 where: the Qs are any of the universal, existential or "exists exactly one" quantifiers
	 v1, v2, v3 are either x or y

	 "Algebraic_structure" objects represent the domain
	 "Condition" objects represent the predicate

	 With three quantifiers and two positions, there are nine separate quantification cases.
	 Each case can easily be represented by nested loops; the most straightforward case is
	 "for all x for all y" where we iterate through all possible (x,y) combinations and require
	 the predicate to be true in all cases. Other cases are more detailed.

	 Some of the cases are similar enough that they can be checked simultaneously. So rather than wasteful
	 separate checks for "for all x exists y" and "for all x exists a unique y", we can so some small case
	 analysis inside the loop and cut down on the number of nested loops we need to run.

	 */

	public void twoWaysOfAnalogySearch(Condition c){
		forAll_x_ForAll_y(c);
		forAll_x_Exists_y(c);
		existsUnique_x_Exists_y(c);
		exists_x_ExistsUnique_y(c);
		existsUnique_x_ExistsUnique_y(c);
		exists_x_ForAll_y(c);
		exists_x_Exists_y(c);
	}

	//condition always met
	public void forAll_x_ForAll_y(Condition c){
		
		String x,y;
		for (int i = 0; i< this.order; i++){
			x = this.elements.get(i);
			for (int j = 0; j < this.order; j++){
				y = this.elements.get(j);
				
				//check condition, quit if false
				if (!c.checkCondition(this, x, y)){
					//mark as false on map
					c.values.put(Quantifier.FOR_ALL_X_FOR_ALL_Y, false);
					return;
				}
			}
		}
		//made it all the way without quitting, all conditions true	
		c.values.put(Quantifier.FOR_ALL_X_FOR_ALL_Y, true);
	}



	//condition met at least once for all x values
	//handles both "exists y" and "exists unique y"	
	public void forAll_x_Exists_y(Condition c){
		
		String x,y;
		boolean exists, existsUnique;
		int uniqueCounter = 0;

		//flag to mark if condition is met only once each time through inner loop
		//set to false the first time false, never re-examine
		existsUnique = true;

		//outer loop (x)
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);

			//flag to make sure we satisfy condition at least once in inner loop
			//update to true when it applies
			exists = false;
	        
			//inner loop counter for "exists unique" quantifier
			uniqueCounter = 0;
	        
			//inner loop (y)
			for (int j = 0; j< this.order; j++){
				y = this.elements.get(j);
						
				if (c.checkCondition(this, x, y)){
					exists = true;
					uniqueCounter ++;
				}
			}//end inner loop 

			//condition failed on last inner loop, set values and quit
			if(!exists){
				c.values.put(Quantifier.FOR_ALL_X_EXISTS_Y, false);
				c.values.put(Quantifier.FOR_ALL_X_EXISTS_UNIQUE_Y, false);
				return;
			}

			//update exists_unique status, if it became false, set to false forever
			else if (existsUnique && uniqueCounter != 1){
				existsUnique = false;
			}

		}// end outer loop     	

		//if we made it here, "for all x, exists y" is met for this condition
		c.values.put(Quantifier.FOR_ALL_X_EXISTS_Y, true);

		//and possibly also "for all x, exists unique y"
		if (existsUnique && uniqueCounter == 1) {
			c.values.put(Quantifier.FOR_ALL_X_EXISTS_UNIQUE_Y, true);
		}
	}




	//condition is true for some y values only for a unique x
	public void existsUnique_x_Exists_y(Condition c){
		String x,y;
		boolean xFound, yFound;
		xFound = false;
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			yFound = false;

			for (int j = 0; j< this.order; j++){
				y = this.elements.get(j);
				if (c.checkCondition(this, x, y)){
					yFound = true;
				}

			}//end inner loop

			//if an x already found, no unique x, set to false and exit
			if(yFound){
				if (xFound){
					c.values.put(Quantifier.EXISTS_UNIQUE_X_EXISTS_Y, false);
					return;
				} else {
					xFound = true;
				}
			}
		}// end outer loop

		//if we made it to the end and x only found once, set to true
		if (xFound){
			c.values.put(Quantifier.EXISTS_UNIQUE_X_EXISTS_Y, true);
		} else {
			c.values.put(Quantifier.EXISTS_UNIQUE_X_EXISTS_Y, false);
		}
	}



	//there's some x where the condition is met for a single y
	public void exists_x_ExistsUnique_y(Condition c){
		String x,y;
		int yCount;
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			yCount = 0;
			for (int j = 0; j< this.order; j++){
				y = this.elements.get(j);

				if (c.checkCondition(this, x, y)){
					yCount++;
				}

			}//end inner loop

			//if found a unique y for this x, set value and exit
			if (yCount == 1){
				c.values.put(Quantifier.EXISTS_X_EXISTS_UNIQUE_Y, true);
				return;
			}

		}//end outer loop 

		//made it to the end without finding a unique y for any x
		c.values.put(Quantifier.EXISTS_X_EXISTS_UNIQUE_Y, false);		
	}



	//condition met exactly once
	public void existsUnique_x_ExistsUnique_y(Condition c){
		String x,y;
		boolean foundUnique_xy = false;
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);

			for (int j = 0; j< this.order; j++){
				y = this.elements.get(j);

				if (c.checkCondition(this, x, y)){
					//if already found an xy, there's no unique xy, set false and exit
					if (foundUnique_xy){
						c.values.put(Quantifier.EXISTS_UNIQUE_X_EXISTS_UNIQUE_Y, false);
						return;
					} else {
						foundUnique_xy = true;
					}
				} //end condition check

			}//end inner loop 

		}//end outer loop 

		//made it to the end, xy found either one or zero times
		if (foundUnique_xy) {
			c.values.put(Quantifier.EXISTS_UNIQUE_X_EXISTS_UNIQUE_Y, true);
		} else {
			c.values.put(Quantifier.EXISTS_UNIQUE_X_EXISTS_UNIQUE_Y, false);
		}				
	}

	//handles both "exists x for all y" and "exists unique x for all y"
	public void exists_x_ForAll_y(Condition c){
		String x,y;
		int xCount = 0;
		boolean current_x;

		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			current_x = true;

			for (int j = 0; j< this.order; j++){
				y = this.elements.get(j);

				// if y ever fails, skip to next x value
				if (!c.checkCondition(this, x, y)){
					current_x = false;
					break;
				}

			}//end inner loop 

			//completed inner loop. if all ys true, increment counter
			if (current_x){
				xCount++;
			}

		}//end outer loop 

		//all loops finished, update truth values accordingly
		if (xCount > 0){
			c.values.put(Quantifier.EXISTS_X_FOR_ALL_Y, true);
		}
		if (xCount == 1){
			c.values.put(Quantifier.EXISTS_UNIQUE_X_FOR_ALL_Y, true);
		}
	}


	//condition met at least once
	public void exists_x_Exists_y(Condition c){
		String x,y;
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			for (int j =0; j < this.order; j++){
				y = this.elements.get(j);

				//if condition ever holds, we're done
				if (c.checkCondition(this, x, y)){
					c.values.put(Quantifier.EXISTS_X_EXISTS_Y, true);
					return;
				}	
			}
		}
		//reach here only if false
		c.values.put(Quantifier.EXISTS_X_EXISTS_Y, false);	
	}

	//end of two quantifier cases


	//select properties requiring greater than two quantifiers
	public void extraPropertiesSearch(){
		commutativity();
		associativity();
		closure();
		leftIdentityLeftInverse();
		leftIdentityRightInverse();
		rightIdentityLeftInverse();
		rightIdentityRightInverse();
	}


	public void commutativity(){
		String x,y;
		boolean commutes = false;
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			for (int j =0; j < this.order; j++){
				y = this.elements.get(j);

				//check commutativity, quit if false
				commutes = this.factTableLookup(x, y).equals(this.factTableLookup(y, x));
				if (!commutes){
					this.extraProperties.put(Properties.COMMUTATIVITY, false);
					return;
				}
			} //end inner loop 
		}//end outer loop 

		//else true		
		this.extraProperties.put(Properties.COMMUTATIVITY, true);
	}



	public void associativity(){
		String x,y,z, left, right;
		boolean associative = false;

		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);

			for (int j =0; j< this.order; j++){
				y = this.elements.get(j);

				for (int k =0; k< this.order; k++){
					z = this.elements.get(k);
					left = this.factTableLookup(x, this.factTableLookup(y, z)); 	//x(yz)
					right = this.factTableLookup(this.factTableLookup(x, y), z); 	//(xy)z
					associative = left.equals(right);

					if (!associative){
						this.extraProperties.put(Properties.ASSOCIATIVITY, false);

						return;
					}
				}//end z loop 			
			}//end y loop 
		}// end x loop 

		//else true
		this.extraProperties.put(Properties.ASSOCIATIVITY, true);
	}




	//check that x * y results in one of the member elements
	public void closure(){
		String x,y,z, element;
		boolean foundElement;

		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);

			for (int j =0; j< this.order; j++){
				y = this.elements.get(j);

				//z = x * y
						z = this.factTableLookup(x, y);
						foundElement = false;

						//check membership of z
						for (int k= 0; k < this.order; k++){
							element = this.elements.get(k);
							if (z.equals(element)){
								foundElement = true;
								break;
							}

						}//end z loop 

						//if z not found in elements for this x*y
						if (!foundElement){
							this.extraProperties.put(Properties.CLOSURE, false);

							return;
						}
			}//end y loop 

		}//end x loop 
		//else closed
		this.extraProperties.put(Properties.CLOSURE, true);

	}



	public void leftIdentityLeftInverse(){
		String x,y,z;
		String leftIden = "";
		boolean foundLeftIdentity = false;
		boolean isInverse = false;
		int yCounter = 0;

		//is x an identity element?
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			if (isLeftIdentityElement(x)){
				foundLeftIdentity = true;
				leftIden = x;
				break;
			}
		}

		//quit if you never find an identity element
		if (!foundLeftIdentity){
			this.extraProperties.put(Properties.LEFT_IDENTITY_LEFT_INVERSE, false);
			return;
		}

		//find inverse
		for (int j =0; j< this.order; j++){
			y = this.elements.get(j);

			for (int k =0; k< this.order; k++){
				z = this.elements.get(k);

				isInverse = (this.factTableLookup(z, y).equals(leftIden));

				//if you find an inverse for this y, increment counter and move to the next one
				if (isInverse){
					yCounter++;
					break;
				}

			}//end z

		}//end y

		//true if some inverse found for all y
		if (yCounter == this.order){
			this.extraProperties.put(Properties.LEFT_IDENTITY_LEFT_INVERSE, true);

		} else {
			this.extraProperties.put(Properties.LEFT_IDENTITY_LEFT_INVERSE, false);
		}
	}


	public void leftIdentityRightInverse(){
		String x,y,z;
		String leftIden = "";
		boolean foundLeftIdentity = false;
		boolean isInverse = false;
		int yCounter = 0;

		//is x an identity element?
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			if (isLeftIdentityElement(x)){
				foundLeftIdentity = true;
				leftIden = x;
				break;
			}
		}

		//quit if you never find an identity element
		if (!foundLeftIdentity){
			this.extraProperties.put(Properties.LEFT_IDENTITY_RIGHT_INVERSE, false);
			return;
		}

		//find inverse
		for (int j =0; j< this.order; j++){
			y = this.elements.get(j);

			for (int k =0; k< this.order; k++){
				z = this.elements.get(k);

				isInverse = (this.factTableLookup(y, z).equals(leftIden));

				//if you find an inverse for this y, increment counter and move to the next one
				if (isInverse){
					yCounter++;
					break;
				}

			}//end z

		}//end y

		//true if some inverse found for all y
		if (yCounter == this.order){
			this.extraProperties.put(Properties.LEFT_IDENTITY_RIGHT_INVERSE, true);

		} else {
			this.extraProperties.put(Properties.LEFT_IDENTITY_RIGHT_INVERSE, false);
		}
	}



	public void rightIdentityLeftInverse(){
		String x,y,z;
		String rightIden = "";
		boolean foundRightIdentity = false;
		boolean isInverse = false;
		int yCounter = 0;

		//is x an identity element?
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			if (isRightIdentityElement(x)){
				foundRightIdentity = true;
				rightIden = x;
				break;
			}
		}

		//quit if you never find an identity element
		if (!foundRightIdentity){
			this.extraProperties.put(Properties.RIGHT_IDENTITY_LEFT_INVERSE, false);
			return;
		}


		//find inverse
		for (int j =0; j< this.order; j++){
			y = this.elements.get(j);

			for (int k =0; k< this.order; k++){
				z = this.elements.get(k);

				isInverse = (this.factTableLookup(z, y).equals(rightIden));

				//if you find an inverse for this y, increment counter and move to the next one
				if (isInverse){
					yCounter++;
					break;
				}

			}//end z

		}//end y

		//true if some inverse found for all y
		if (yCounter == this.order){
			this.extraProperties.put(Properties.RIGHT_IDENTITY_LEFT_INVERSE, true);

		} else {
			this.extraProperties.put(Properties.RIGHT_IDENTITY_LEFT_INVERSE, false);
		}
	}





	public void rightIdentityRightInverse(){
		String x,y,z;
		String rightIden = "";
		boolean foundRightIdentity = false;
		boolean isInverse = false;
		int yCounter = 0;

		//is x an identity element?
		for (int i =0; i< this.order; i++){
			x = this.elements.get(i);
			if (isRightIdentityElement(x)){
				foundRightIdentity = true;
				rightIden = x;
				break;
			}
		}

		//quit if you never find an identity element
		if (!foundRightIdentity){
			this.extraProperties.put(Properties.RIGHT_IDENTITY_RIGHT_INVERSE, false);
			return;
		}


		//find inverse
		for (int j =0; j< this.order; j++){
			y = this.elements.get(j);

			for (int k =0; k< this.order; k++){
				z = this.elements.get(k);

				isInverse = (this.factTableLookup(y, z).equals(rightIden));

				//if you find an inverse for this y, increment counter and move to the next one
				if (isInverse){
					yCounter++;
					break;
				}

			}//end z

		}//end y

		//true if some inverse found for all y
		if (yCounter == this.order){
			this.extraProperties.put(Properties.RIGHT_IDENTITY_RIGHT_INVERSE, true);

		} else {
			this.extraProperties.put(Properties.RIGHT_IDENTITY_RIGHT_INVERSE, false);
		}
	}

	
	
	
	
	

	//helper functions

	public boolean isLeftIdentityElement(String iden){
		String y;
		for (int i = 0; i< this.order; i++){
			y = this.elements.get(i);

			//check identity
			if (!this.factTableLookup(iden, y).equals(y)){
				return false;
			}
		}
		//else true
		return true;
	}



	public boolean isRightIdentityElement(String iden){
		String y;
		for (int i = 0; i< this.order; i++){
			y = this.elements.get(i);

			//check identity
			if (!this.factTableLookup(y, iden).equals(y)){
				return false;
			}
		}
		//else true
		return true;
	}




	
	
}