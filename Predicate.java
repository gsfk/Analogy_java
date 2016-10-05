

public enum Predicate {
	 // x * x = x
    P1 {                 
        @Override
	    public boolean apply(AlgebraicStructure a, String x, String y) {
            return x.equals(a.factTableLookup(x,x));
        }
    }, 

	//x * x = y
    P2 {
        @Override
	    public boolean apply(AlgebraicStructure a, String x, String y) {
            return y.equals(a.factTableLookup(x,x));
        }
    },
	//x * y = x
    P3 {
        @Override
	    public boolean apply(AlgebraicStructure a, String x, String y) {
            return x.equals(a.factTableLookup(x,y));
        }
    },
	//x * y = y
    P4 {
        @Override
	    public boolean apply(AlgebraicStructure a, String x, String y) {
            return y.equals(a.factTableLookup(x,y));
        }
    },
	//y * x = x
    P5 {
        @Override
	    public boolean apply(AlgebraicStructure a, String x, String y) {
            return x.equals(a.factTableLookup(y,x));
        }
    },
	//y * x = y
    P6 {
        @Override
	public boolean apply(AlgebraicStructure a, String x, String y) 
	    {return y.equals(a.factTableLookup(y,x));}},

	//y * y = x
    P7 {
        @Override
	public boolean apply(AlgebraicStructure a, String x, String y)
	    {return x.equals(a.factTableLookup(y,y));}};

    public abstract boolean apply(AlgebraicStructure a, String x, String y);

}
