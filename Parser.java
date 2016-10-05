import java.io.*;
import java.util.Scanner;
import java.util.ArrayList;


public class Parser {

	public static AlgebraicStructure parse(String filename){

		//domain elements
		ArrayList<String> elements = new ArrayList<String>();

		//number of elements
		int order;

		//fact table
		ArrayList<ArrayList<String>> facts = new ArrayList<ArrayList<String>>();

		//current fact
		ArrayList<String> currentFact;

		//relation name
		String relation = "";

		String factTuple;
		int leftParen, rightParen;


		try{
			Scanner infile = new Scanner(new FileReader(filename));
			String word;

			//main parse loop 
			while (infile.hasNext()){
				word = infile.next();
				if (word.equals("%")){continue;}

				//if first word is Elements, parse elements
				if (word.equals("Elements:")){

					infile.useDelimiter("[\\s,\t\r\n]+");
					word = infile.next();
					while (!(word.equals("Relation:"))){

						elements.add(word);
						word = infile.next();

						//handle comments
					}

				} //end Elements loop 


				// if "Relation" parse relation
				if (word.equals("Relation:")){

					infile.useDelimiter("[\\s,\t\r\n]+");  //needed?
					word = infile.next();

					relation = word;
				} //end Relation loop 


				//if "Facts" parse facts, quit when you reach "end"
				if (word.equals("Facts:")){

					while (!word.equals("end")){
						infile.useDelimiter("[\t\r\n]+");
						word = infile.next();

						//remove parens and anything before and after
						leftParen = word.lastIndexOf('(');
						rightParen = word.lastIndexOf(')');

						//skip this line if no parens
						if (leftParen == -1 || rightParen == -1) {continue;}

						//remove parens 
						factTuple = word.substring(word.lastIndexOf('(')+1, word.lastIndexOf(')'));

						//remove whitespace
						factTuple = factTuple.replaceAll("\\s+","");

						String[] fact = factTuple.split(",");

						//new object for each current fact, avoids overwriting facts
						currentFact = new ArrayList<String>();

						for (int i = 0; i< fact.length; i++){
							currentFact.add(fact[i]);
						}

						facts.add(currentFact);

						//if fact length 0, this is whitespace, discard

						//expect tuples of 3 items, reject anything else. 
					}

				} // end Facts loop 



				if (word.equals("end")){
					infile.close();
					return new AlgebraicStructure(elements, relation, facts);
				}
			}// end main parse loop 
			
			infile.close();
		
		} //end try

		//any exceptions, whine to user and quit 
		catch(Exception e){
			System.err.println("error, closing\n" + e);
			return null;
		}

		//reached EOF without finding "end"
		//TODO: throw error
		return null;

	} //end parser

}


