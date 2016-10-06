import java.io.*;
import java.util.ArrayList;


/*
 * Class to interact with an external prover. This implementation uses Prover9, https://www.cs.unm.edu/~mccune/mace4/
 * 
 */

/* Prover9 return values:
 *    0      proof found
 *    1      fatal error
 *    2      no proof found, premises exhausted
 *    3      max memory hit
 *    4      max time hit
 *    5      max given hit
 *    6      max kept hit
 *    7      Prover9 terminated
 *  101      Prover9 crashed
 * 
 * 
*/



public class Prover {

	public static int callProver(){
		
		String ProverCall = ProverPath.FullPath;
		ProverCall += " -f analogy_prover_file.in";
		
		//launch external prover, get return value
		Runtime r = Runtime.getRuntime();
		Process p = null;  

		try {
			p = r.exec(ProverCall);
			p.waitFor();  
			
		} catch (IOException e){
			System.err.println("error launching prover");
			System.err.println(e);
			return -1;
		} catch (Exception e){
			System.err.println(e);
			return -2;
		}
		return p.exitValue();
	}



	public static void invokeProver(ArrayList<Formula> formulas, String filename) throws IOException {
		//prover return value
		int outcome; 
		int numProverTimeouts = 0;
		int numFormulas = formulas.size();
		Formula currentFormula = null;
		Formula formulaToProve = null;

		System.out.println("sending " + numFormulas + " formulas to prover (" + filename + ")");

		//main loop: for each formula in the set, try to prove it from the others
		for (int i = 0; i < numFormulas; i++){

			formulaToProve = formulas.get(i);

			//create a new prover input file, or overwrite an old one
			File outfile = new File("analogy_prover_file.in");
			outfile.createNewFile();

			// --- build prover input file ---- //
			
			FileWriter fileOutput = new FileWriter(outfile); 

			//stop after finding one proof (starts counting from zero)
			fileOutput.write("assign(max_proofs, 0).\n");

			//prover time limit
			fileOutput.write("assign(max_seconds, 1).\n\n");

			//suppress console output
			fileOutput.write("set(quiet).\n");
			fileOutput.write("clear(echo_input).\n");
			fileOutput.write("clear(print_initial_clauses).\n");
			fileOutput.write("clear(print_given).\n");
			fileOutput.write("clear(print_proofs).\n");

			//start list of premises
			fileOutput.write("formulas(sos).\n\n");

			for (int j = 0; j<numFormulas; j++ ){

				//skip formula we're trying to prove
				if (j == i){continue;}

				//output any other true formula
				currentFormula = formulas.get(j);
				if (currentFormula.includeInMinimalSet){
					fileOutput.write(currentFormula.proverName + ".\n");
				}
			}

			//done printing premises
			fileOutput.write("\nend_of_list.\n\n");

			//try to prove formula i
			fileOutput.write("formulas(goals).\n\n" + formulaToProve.proverName + ".\n\n" + "end_of_list.\n");

			fileOutput.close();
			
			//invoke prover, try to prove f
			outcome = callProver();
			//if proof found, remove from set 
			if (outcome == 0){
				formulas.get(i).setIncludeValue(false);
			}
			if (outcome == 4){
				numProverTimeouts++;
			}
			if (outcome == 127){
				System.err.println("No prover found");
			}

		}// end main loop 


	}

}
