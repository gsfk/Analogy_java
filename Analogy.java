import java.io.*;
import java.util.ArrayList;

public class Analogy {

	public static void main (String[] args){
		boolean useProver = true;
		boolean secondFile = false;
		boolean sharedFormulas = false;
		boolean sharedAxioms = false;
		boolean thisFormulaShared = false;
		String filename1, filename2;
		filename1 = filename2 = "";
		int numArguments = args.length;
		int formulaCount;


		//declare vector of all predicates (for both files)
		ArrayList<Condition> predicates = new ArrayList<Condition>();
		ArrayList<Condition> predicates2 = new ArrayList<Condition>();


		//declare (blank) vector of all predicates found true (1 and 2)
		ArrayList<Formula> formulas = new ArrayList<Formula>();
		ArrayList<Formula> formulas2 = new ArrayList<Formula>();


		//if no arguments, help
		if (numArguments == 0){
			userHelp();
			return; 
		}

		//if one argument, it's a file name
		if (numArguments == 1){
			filename1 = args[0];
		}

		//two args: either two files, or one file and "-noprover" tag
		if (numArguments == 2){
			filename1 = args[0];
			if (args[1].equals("-noprover")){
				useProver = false;
			} else {
				filename2 = args[1];
				secondFile = true;
			}
		}

		//three args: must be two files and "-noprover"
		if (numArguments == 3){
			if (!args[2].equals("-noprover")){
				//throw error
			}
			filename1 = args[0];
			filename2 = args[1];
			useProver = false;
			secondFile = true;
		}//end argument handling

		//check prover connection
		if (useProver && ProverPath.FullPath.equals("/your/path/to/prover9")){
			System.err.println("*no path to prover*");
			System.err.println("Change the prover path information in ProverPath.java. See instructions.pdf for more details");
			return;
		}

		//-- operations for first file -- //

		//generate domain from input
		AlgebraicStructure g = Parser.parse(filename1);

		//create all predicates and store in a vector
		predicates = Condition.returnAllPredicates(g.relation);

		//search all quantifier / predicate combinations, saving truth values as you go
		for (int i = 0; i< predicates.size(); i++){
			g.twoWaysOfAnalogySearch(predicates.get(i));
		}

		//explore select properties not expressible with only 2 quantifiers (commutativity, associativity, etc)
		g.extraPropertiesSearch();

		//generate set of all true formulas for this structure
		formulas = Condition.generateFormulas(predicates, g);


		//call prover
		if (useProver){
			try{
				Prover.invokeProver(formulas, filename1);
			} catch (IOException e){
				System.err.println("file error");
			}
		}//end prover call


		//output for a single file only
		if (!secondFile){
			System.out.println("\nFull set for "+ filename1 + "\n");
			formulaCount = 1;
			for (Formula f: formulas){
				System.out.println(formulaCount + ": " + f.prettyName);
				formulaCount++;
			}
			if(useProver){
				System.out.println("\nMinimal set for "+ filename1 + "\n");
				formulaCount = 1;
				for (Formula f: formulas){
					if (f.includeInMinimalSet){
						System.out.println(formulaCount + ": " + f.prettyName);
						formulaCount++;
					}
				}
			}
		}		


		// -- operations for two files --//
		if(secondFile){

			//repeat search code above for second file

			AlgebraicStructure g2 = Parser.parse(filename2);
			predicates2 = Condition.returnAllPredicates(g2.relation);

			for (int i = 0; i< predicates.size(); i++){
				g2.twoWaysOfAnalogySearch(predicates2.get(i));
			}

			g2.extraPropertiesSearch();
			formulas2 = Condition.generateFormulas(predicates2, g2);

			//file2 prover call
			if (useProver){
				try{
					Prover.invokeProver(formulas2, filename2);
				} catch (IOException e){
					System.err.println("file error");
				}
			}




			//show formulas unique to file 1
			System.out.println("\nFormulas unique to " + filename1);
			formulaCount = 1;
			for (Formula f1 : formulas){
				for (Formula f2 : formulas2){
					if (f1.prettyName.equals(f2.prettyName)){
						thisFormulaShared = true;
					}
				}
				if (!thisFormulaShared){
					System.out.println(formulaCount + ": " + f1.prettyName);
					formulaCount ++;
				}
			}
			if (formulaCount == 1){
				System.out.println("(none)");
			}	


			//show formulas unique to file 2
			System.out.println("\nFormulas unique to " + filename2);
			formulaCount = 1;
			for (Formula f2 : formulas2){
				thisFormulaShared = false;
				for (Formula f1 : formulas){
					if (f1.prettyName.equals(f2.prettyName)){
						thisFormulaShared = true;
					}
				}
				if (!thisFormulaShared){
					System.out.println(formulaCount + ": " + f2.prettyName);
					formulaCount ++;
				}

			}
			if (formulaCount == 1){
				System.out.println("(none)");
			}	



			//shared formulas
			sharedFormulas = false;
			System.out.println("\nFormulas shared between " + filename1 + ", " + filename2 + ":");
			formulaCount = 1;
			for (Formula f1 : formulas){
				for (Formula f2 : formulas2){
					if (f1.prettyName.equals(f2.prettyName)){
						sharedFormulas = true;
						System.out.println(formulaCount + ": " + f1.prettyName);
						formulaCount++;
						continue;
					}
				}
			}
			if (!sharedFormulas){
				System.out.println("(none)");
			} 


			//show minimal sets if prover attached
			if (useProver){

				//file 1 minimal set
				System.out.println("\nMinimal set for " + filename1 + ":");
				formulaCount = 1;
				for (Formula f : formulas){
					if (f.includeInMinimalSet){
						System.out.println(formulaCount + ": " + f.prettyName);
						formulaCount++;
					}
				}


				//file 2 minimal set
				System.out.println("\nMinimal set for " + filename2 + ":");
				formulaCount = 1;
				for (Formula f2 : formulas2){
					if (f2.includeInMinimalSet){
						System.out.println(formulaCount + ": " + f2.prettyName);
						formulaCount++;
					}
				}

				//show shared axioms (overlap between minimal sets)
				System.out.println("\nFormulas shared between minimal sets:");
				formulaCount = 1;
				for (Formula f1 : formulas){
					for (Formula f2 : formulas2){
						if (f1.includeInMinimalSet && f2.includeInMinimalSet && f1.prettyName.equals(f2.prettyName)){
							sharedAxioms = true;
							System.out.println(formulaCount + ": " + f1.prettyName);
							formulaCount++;
						}
					}
				}
				if (!sharedAxioms){
					System.out.println("none");
				}
			} 

		}//end 2 file output

		if (!useProver){
			noProverWarning();
		}
		System.out.println("\n(done)");

	} //end of main






	public static void userHelp(){
		System.out.println("\nUsage: name any input files in command line arguments:");
		System.out.println("To find axioms for a single file: ./analogy yourfilename.txt");
		System.out.println("To compare axioms for two structures, enter two file names: ./analogy file1 file2");
		System.out.println("Requires Prover9 installation: https://www.cs.unm.edu/~mccune/mace4/download/");
		System.out.println("To use without a prover add \"-noprover\" as a final argument, but it won't look nearly as cool.");
		System.out.println("See README for more details.");
	}

	public static void noProverWarning(){
		System.out.println("\nProver disconnected, expect redundant formulas."); 
	}




}
