method InsertionSort'(a: array<int>)
	ensures Sorted(a)
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	ghost var A := multiset(a[..]);
	var i := 0;
	while i != a.Length
		invariant Inv(a[..], i, A)
	{
		var j := i;
		while j > 0 && a[j-1] > a[j]
			invariant Inv2(a[..], i, j, A)
		{
			a[j-1], a[j] := a[j], a[j-1];
			j := j-1;
		}
		i := i+1;
	}
}

predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

predicate SortedSequenceExceptAt(q: seq<int>, j: nat)
{
	forall i,k :: 0 <= i <= k < |q| && i != j && k != j ==> q[i] <= q[k]
}

method {:verify true} InsertionSort(a: array<int>)
	ensures Sorted(a)
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	// introduce logical constant + introduce local variable + strengthen postcondition
	ghost var A := multiset(a[..]);
	var i: nat;
	i := InsertionSort1(a, A);
	LemmaPostconditionStronger(a, i, A);
}

predicate Inv(q: seq<int>, i: nat, A: multiset<int>)
{
	i <= |q| && SortedSequence(q[..i]) && multiset(q) == A
}

lemma LemmaPostconditionStronger(a: array<int>, i: nat, A: multiset<int>)
	requires Inv(a[..], i, A) && i == a.Length
	ensures Sorted(a)
	ensures multiset(a[..]) == A
{}

method {:verify true} InsertionSort1(a: array<int>, ghost A: multiset<int>) returns (i: nat)
	requires A == multiset(a[..])
	ensures Inv(a[..], i, A) && i == a.Length
	modifies a
{
	// sequential composition + contract frame
	i := InsertionSort2a(a, A);
	i := InsertionSort2b(a, i, A);
}

method {:verify true} InsertionSort2a(a: array<int>, ghost A: multiset<int>) returns (i: nat)
	requires A == multiset(a[..])
	ensures Inv(a[..], i, A)
{
	// assignment
	Lemma2a(a, A);
	i := 0;
}

lemma Lemma2a(a: array<int>, A: multiset<int>)
	requires A == multiset(a[..])
	ensures Inv(a[..], 0, A)
{}

method {:verify true} InsertionSort2b(a: array<int>, i0: nat, ghost A: multiset<int>) returns (i: nat)
	requires Inv(a[..], i0, A)
	ensures Inv(a[..], i, A) && i == a.Length
	modifies a
{
	i := i0;
	// iteration
	while i != a.Length
		invariant Inv(a[..], i, A)
		decreases a.Length-i
	{
		i := InsertionSort3(a, i, A);
	}
}

method {:verify true} InsertionSort3(a: array<int>, i0: nat, ghost A: multiset<int>) returns (i: nat)
	requires Inv(a[..], i0, A) && i0 != a.Length
	ensures Inv(a[..], i, A) && 0 <= a.Length-i < a.Length-i0
	modifies a
{
	i := i0;
	// following assignment + contract frame
	Insert(a, i, A);
	i := i+1;
}

method {:verify true} Insert(a: array<int>, i: nat, ghost A: multiset<int>)
	requires Inv(a[..], i, A) && i != a.Length
	ensures Inv(a[..], i+1, A) // && 0 <= a.Length-i-1 < a.Length-i
	modifies a
{
	// introduce local variable + strengthen postcondition
	var j: nat;
	j := Insert1(a, i, A);
	LemmaPost2(a, i, j, A);
}

lemma {:verify true} LemmaPost2(a: array<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2(a[..], i, j, A) && !UnacceptablyInefficientGuard(a, i, j, A)
	ensures Inv(a[..], i+1, A)
{}

//predicate method UnacceptablyInefficientGuard(a: array<int>, ghost i: nat, j: nat, ghost A: multiset<int>)
predicate UnacceptablyInefficientGuard(a: array<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2(a[..], i, j, A)
	reads a
{
	exists l :: 0 <= l < j && a[l] > a[j]
}

predicate method EfficientGuard(a: array<int>, ghost i: nat, j: nat, ghost A: multiset<int>)
	requires Inv2(a[..], i, j, A)
	reads a
{
	j > 0 && a[j-1] > a[j]
}

predicate Inv2(q: seq<int>, i: nat, j: nat, A: multiset<int>)
{
	j <= i < |q| && SortedSequenceExceptAt(q[..i+1], j) && multiset(q) == A &&
	forall k :: j < k <= i ==> q[j] < q[k]
}

method {:verify true} Insert1(a: array<int>, i: nat, ghost A: multiset<int>) returns (j: nat)
	requires Inv(a[..], i, A) && i != a.Length
	ensures Inv2(a[..], i, j, A) && !UnacceptablyInefficientGuard(a, i, j, A)
	modifies a
{
	// sequential composition + contract frame
	j := Insert2a(a, i, A);
	j := Insert2b(a, i, j, A);
}

method {:verify true} Insert2a(a: array<int>, i: nat, ghost A: multiset<int>) returns (j: nat)
	requires Inv(a[..], i, A) && i != a.Length
	ensures Inv2(a[..], i, j, A)
{
	// assignment
	LemmaInsert2a(a, i, A);
	j := i;
}

lemma LemmaInsert2a(a: array<int>, i: nat, A: multiset<int>)
	requires Inv(a[..], i, A) && i != a.Length
	ensures Inv2(a[..], i, i, A)
{}

method {:verify true} Insert2b(a: array<int>, i: nat, j0: nat, ghost A: multiset<int>) returns (j: nat)
	requires Inv2(a[..], i, j0, A)
	ensures Inv2(a[..], i, j, A) && !UnacceptablyInefficientGuard(a, i, j, A)
	modifies a
{
	j := j0;
	// iteration
	while EfficientGuard(a, i, j, A) // UnacceptablyInefficientGuard(a, i, j, A)
		invariant Inv2(a[..], i, j, A)
		decreases j
	{
		assert UnacceptablyInefficientGuard(a, i, j, A) by {
			assert EfficientGuard(a, i, j, A); // the efficient guard holds here
			EquivalentGuards(a, i, j, A); // so the guard we used in the initial development holds too
		}
		j := Insert3(a, i, j, A);
	}
	assert !UnacceptablyInefficientGuard(a, i, j, A) by {
		assert !EfficientGuard(a, i, j, A); // negation of the efficient guard
		EquivalentGuards(a, i, j, A);
	}
}

method {:verify true} Insert3(a: array<int>, i: nat, j0: nat, ghost A: multiset<int>) returns (j: nat)
	requires Inv2(a[..], i, j0, A) && UnacceptablyInefficientGuard(a, i, j0, A)
	ensures Inv2(a[..], i, j, A) && j < j0
	modifies a
{
	j := j0;
	// following assignment + contract frame
	Swap(a, i, j, A);
	j := j-1;
}

method {:verify true} Swap(a: array<int>, ghost i: nat, j: nat, ghost A: multiset<int>)
	requires Inv2(a[..], i, j, A) && UnacceptablyInefficientGuard(a, i, j, A)
	ensures Inv2(a[..], i, j-1, A) // && j-1 < j
	modifies a
{
	// assignment
	LemmaSwap(a, i, j, A);
	a[j-1], a[j] := a[j], a[j-1];
}

lemma LemmaSwap(a: array<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2(a[..], i, j, A) && UnacceptablyInefficientGuard(a, i, j, A)
	ensures Inv2(a[..][j-1 := a[j]][j := a[j-1]], i, j-1, A) // sequence assignment
{}

// this helps in justifying the move from the initial guard to the efficient one,
// with no need to change anything in the initial development:
// the (LHS ==> RHS) helps in the loop body,
// and (LHS <== RHS) helps upon termination of the loop
lemma EquivalentGuards(a: array<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2(a[..], i, j, A)
	ensures EfficientGuard(a, i, j, A) <==> UnacceptablyInefficientGuard(a, i, j, A)
{}

method Main() {
	var a: array<int> := new int[4];
	a[0],a[1],a[2],a[3] := 3,8,5,-1;
	print "Before sorting: ";
	print a[..];
	InsertionSort(a);
	assert Sorted(a);
	print "\n After sorting: ";
	print a[..];
}
