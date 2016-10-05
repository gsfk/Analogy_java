
//class to represent formulas passed to the prover

public class Formula {

	public String prettyName;
	public String proverName;
	public boolean includeInMinimalSet;
	
	
	public Formula(String n1, String n2){
		prettyName = n1;
		proverName = n2;
		includeInMinimalSet = true;
	}
	
	public void setIncludeValue(boolean v){
		this.includeInMinimalSet = v;
	}
	
}
