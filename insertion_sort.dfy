datatype StateSpace = StateSpace(a:array<int>,n:int)

predicate sorted(a: array?<int>, l: int, u:int)
reads a
requires a != null
{
    forall i,j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
}

function method rho(a:array<int>): StateSpace
{
	StateSpace(a,a.Length)
}

function method pi(state:StateSpace): array<int>
{
	state.a
}

method is_sort(a:array<int>) returns (n:int)
{
	var i := 0;
	while i < a.Length - 1
	decreases a.Length - i - 1
	{
		if a[i] > a[i + 1]
		{
			return 0;
		}
		print a[i],"\n";
		i := i + 1;
	}
	return 1;
}

method InsertionSortTransition(initState:StateSpace) returns (finalState:StateSpace)
modifies initState.a
requires initState.n > 0
ensures finalState.n == 0
ensures finalState.a != null
{
	var a: array<int> := initState.a;
	var l: int := a.Length;
	var i := 1;
	var j := 0;
	var t := 0;
	var k := 0;
	var loc := 0;

	while i < l
	invariant 0 < i
	decreases l - i
	{
		k := 0;
		t := a[i];
		j := i - 1;
		while j >= 0
		invariant j < l
		decreases j
		{
			if t < a[j]
			{
				a[j + 1] := a[j];
			}
			else
			{
				if k == 0
				{
					k := j + 1;
					print "loc:",k,"\n";
				}
			}
			j := j - 1;
		}
		if k < i
		{
			if k >= 0 
			{
				if k < i
				{
					loc := k;
					a[loc] := t;
				}
			}
		}

		i := i + 1;
	}
	return StateSpace(a,0);
}

method Main()
{
		var k := 0;
        var a := new int[5];
        a[0],a[1],a[2],a[3],a[4] := 9,4,6,3,8;
        var initState := rho(a);
        var terminalState := InsertionSortTransition(initState);
        var output := pi(terminalState);
		while(k < 5) { print a[k], "\n"; k := k+1;}
}