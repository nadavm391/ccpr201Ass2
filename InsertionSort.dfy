
method PairInsertionSort(a: array<int>)
	ensures Sorted1(a,0,a.Length-1)
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	//introdue local variable + introduce logical constant + weaken precondition
	ghost var A := multiset(old(a[..]));
	PairInsertionSort1(a,A);
}
method PairInsertionSort1(a: array<int>, ghost A: multiset<int>) 	
	requires multiset(a[..])==A
	ensures Sorted1(a,0,a.Length-1)
	ensures multiset(a[..]) == A
	modifies a
{
	//introduce local variables+sequential composition
	var i:nat;
	var j,x,y;
	j,i:=initIJ(a,j,i,A);
	j,i,x,y:=PairInsertionSort2(a,j,i,x,y,A);
}
method initIJ(ghost a: array<int>, j0: int,i0:nat, ghost A: multiset<int>) returns (j: int,i:nat)
	requires multiset(a[..])==A
	ensures InvPair(a[..],j,i,A)
	modifies a
	{
		j,i:=j0,i0;
		//assignment
		LemmainitIJ(a,j,i,A);
		j,i:=-1,0;
	}
lemma LemmainitIJ( a: array<int>, j: int,i:nat,  A: multiset<int>)
	requires multiset(a[..])==A
	ensures InvPair(a[..],-1,0,A)
{}

method PairInsertionSort2(a: array<int>, j0: int,i0:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j: int,i:nat,x:int,y:int)
	requires InvPair(a[..],j0,i0,A)
	ensures Sorted1(a,0,a.Length-1)
	ensures multiset(a[..]) == A
	modifies a
{
	//sequential composition
	j,i,x,y:=j0,i0,x0,y0;
	j,i,x,y:=MainLoop(a,j,i,x,y,A);
	if i==a.Length-1{
		j,y := i-1,a[i];
		while j>=0 && a[j] >y
			invariant Inv4Pair(a[..],j,i,x,y,A)
			decreases j
		{
			SwapPair(a,j+1,j,A);
			j:=j-1;
		}
	}
	else {

	}	

}

method MainLoop(a: array<int>, j0: int,i0:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j: int,i:nat,x:int,y:int)
	requires InvPair(a[..],j0,i0,A)
	ensures InvPair(a[..],j,i,A) && !GuardMainLoop(a,i)
	modifies a

{
	//iteration
	j,i,x,y:=j0,i0,x0,y0;
	while GuardMainLoop(a,i)
		decreases a.Length - i
		invariant InvPair(a[..],j,i,A)
	{
		j,i,x,y:=MainLoopBody(a,j,i,x,y,A);
	}
}

method MainLoopBody(a: array<int>, j0: int,i0:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j: int,i:nat,x:int,y:int)
	requires InvPair(a[..],j0,i0,A) && GuardMainLoop(a,i0)
	ensures InvPair(a[..],j,i,A) && (a.Length-i)< (a.Length-i0)
	modifies a
{
	//sequential composition+contract frame
	j,i,x,y:=j0,i0,x0,y0;
	j,x,y:=preFirstInnerLoop(a,j,i,x,y,A);
	j,i,x,y:=MainLoopBody2(a,j,i,x,y,A);
}

method preFirstInnerLoop(a: array<int>, j0: int,i:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j:int,x:int,y:int)
	requires InvPair(a[..],j0,i,A) && GuardMainLoop(a,i)
	ensures Inv2Pair(a[..],j,i,x,y,A)
	{
		j,x,y:=j0,x0,y0;
		//leading assignemnt+following assignment+contract frame+weaken precondition
		x,y:=a[i],a[i+1];
		x,y:=adjustXY(a,j,i,x,y,A);
		j:= i-1;
	}
method adjustXY(a: array<int>, j: int,i:nat,x0:int, y0:int, ghost A: multiset<int>) returns (x:int,y:int)
	requires InvPair(a[..],j,i,A) && GuardMainLoop(a,i) && x0==a[i]&&y0==a[i+1]
	ensures Inv2Pair(a[..],i-1,i,x,y,A)
	{
		x,y:=x0,y0;
		//alternaion
		if x<y {
			x,y:=xSmaller(a,j,i,x,y,A);
		}
		else{
			LemmaxGreaterOrEqual(a,j,i,x,y,A);
		} 
	}
method xSmaller (a: array<int>, j: int,i:nat,x0:int, y0:int, ghost A: multiset<int>) returns (x:int,y:int)
	requires InvPair(a[..],j,i,A) && GuardMainLoop(a,i) && x0==a[i]&&y0==a[i+1] && x0<y0
	ensures Inv2Pair(a[..],i-1,i,x,y,A)

	{
		x,y:=x0,y0;
		//assignment
		x,y:=y,x;
	}

lemma LemmaxSmaller (a: array<int>, j: int,i:nat,x:int, y:int,  A: multiset<int>)
	requires InvPair(a[..],j,i,A) && GuardMainLoop(a,i) && x==a[i]&&y==a[i+1] && x<y
	ensures Inv2Pair(a[..],i-1,i,y,x,A)

lemma LemmaxGreaterOrEqual (a: array<int>, j: int,i:nat,x:int, y:int,  A: multiset<int>)
	requires InvPair(a[..],j,i,A) && GuardMainLoop(a,i) && x==a[i]&&y==a[i+1] && x>=y
	ensures Inv2Pair(a[..],i-1,i,x,y,A)

method MainLoopBody2(a: array<int>, j0: int,i0:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j: int,i:nat,x:int,y:int)
	requires Inv2Pair(a[..],j0,i0,x0,y0,A)
	ensures InvPair(a[..],j,i,A) && (a.Length-i)< (a.Length-i0)
	modifies a
{
	//sequential composition+contract frame
	j,i,x,y:=j0,i0,x0,y0;
	j:=firstInnerLoop(a,j,i,x,y,A);
	j,i,x,y:=MainLoopBody3(a,j,i,x,y,A);
}

method firstInnerLoop(a: array<int>, j0: int,i:nat,x:int, y:int, ghost A: multiset<int>) returns (j: int)
	requires Inv2Pair(a[..],j0,i,x,y,A)
	ensures Inv2Pair(a[..],j,i,x,y,A) && !GuardSecondLoop(a,j,x)
	modifies a
	{
		j:=j0;
		//iteration
		while GuardSecondLoop(a,j,x)
		invariant Inv2Pair(a[..],j,i,x,y,A)
		decreases j
		{
			j:=firstInnerLoopBody(a,j,i,x,y,A);
		}
	}

method firstInnerLoopBody(a: array<int>, j0: int,i:nat,x:int, y:int, ghost A: multiset<int>) returns (j: int)
	requires Inv2Pair(a[..],j0,i,x,y,A) && GuardSecondLoop(a,j0,x)
	ensures Inv2Pair(a[..],j,i,x,y,A) && j<j0
	modifies a

	{
		j:=j0;
		//following assignment+contract frame
		SwapFirstInner(a,j,i,x,y,A);
		j:=j-1;
	}
method {:verify true} SwapFirstInner(a: array<int>, j:int, i: nat,x:int,y:int ,ghost A: multiset<int>) 
	requires Inv2Pair(a[..], j, i,x, y, A) && GuardSecondLoop(a,j,x)
	ensures Inv2Pair(a[..], j-1, i,x, y, A) // && j-1 < j
	modifies a
{
	// assignment
	LemmaSwapFirstInner(a, j, i, x, y, A);
	a[j+2], a[j] := a[j], a[j+2];
}

lemma LemmaSwapFirstInner(a: array<int>, j: int, i: nat,x:int,y:int, A: multiset<int>)
	requires Inv2Pair(a[..], j, i, x, y, A) && GuardSecondLoop(a,j,x)
	ensures Inv2Pair(a[..][j := a[j+2]][j+2 := a[j]], j-1, i, x, y, A) 
{}

method MainLoopBody3(a: array<int>, j0: int,i0:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j: int,i:nat,x:int,y:int)
	requires Inv2Pair(a[..],j0,i0,x0,y0,A) && !GuardSecondLoop(a,j0,x0)
	ensures InvPair(a[..],j,i,A) && (a.Length-i)< (a.Length-i0)
	modifies a
	{
		j,i,x,y:=j0,i0,x0,y0;
		if a[j+2]!=x{
		SwapPair(a,j+2,j+1,A);
	}	
	else{
		LemmaMidNoswap(a[..],j,i,x,y,A);
	}
	
	
	while j>=0 && a[j] > y
		invariant Inv3Pair(a[..],j,i,x,y,A)
		decreases j
		{
			SwapPair(a,j+1,j,A);
			j:=j-1;
		}
	
	i:=i+2;	
	}
predicate method GuardMainLoop(a: array<int>,i:nat)
{
	i < a.Length-1	
}

predicate method GuardSecondLoop(a: array<int>,j:int,x:int)
	requires -1<=j<=a.Length-3
	reads a
{
	 j>=0 && a[j]>x	
}


lemma LemmaMidswap(a: seq<int>,j:int,i:nat,x:int,y:int, A: multiset<int>)
	requires Inv2Pair(a,j,i,x,y,A)
	requires j<0 || a[j]<=x
	requires a[j+2]!=x
	ensures Inv3Pair(a[j+1:=a[j+2]][j+2:=a[j+1]],j,i,x,y,A)
{
}

lemma LemmaMidNoswap(a: seq<int>,j:int,i:nat,x:int,y:int, A: multiset<int>)
	requires Inv2Pair(a,j,i,x,y,A)
	requires j<0 || a[j]<=x
	requires a[j+2]==x
	ensures Inv3Pair(a,j,i,x,y,A)
{
}
predicate InvPair(a: seq<int>, j: int, i:nat, A: multiset<int>)
{
	0<=i<=|a| &&
	(|a|>1 ==> (-1<=j<=|a|-3)) &&
	SortedSequence1(a,0,i-1) &&
	multiset(a)==A
}
predicate Inv2Pair(a: seq<int>, j: int,i:nat,x:int, y:int, A: multiset<int>)
{
	0<=i<=|a|-2 &&
	-1<=j<=|a|-3 &&
	SortedSequence1(a,0,j)&&
	SortedSequence1(a,j+2,i+1)&&
	(0<=j<i-1 ==> a[j+3]>=a[j]) &&
	(j<i-1  ==> a[j+3]>x) &&
	((x==a[j+1]&&y==a[j+2]) || (x==a[j+2]&&y==a[j+1])) && x>=y &&
	multiset(a)==A
}

predicate Inv3Pair(a: seq<int>, j: int,i:nat,x:int, y:int, A: multiset<int>)
{
	0<=i<=|a|-2 &&
	-1<=j<=|a|-3 &&
	SortedSequence1(a,0,j)&&
	SortedSequence1(a,j+1,i+1)&&
	a[j+2]>=y &&
	(j>=0 ==> a[j+2]>=a[j]) &&
	a[j+1]==y &&
	multiset(a)==A
}

predicate Inv4Pair(a: seq<int>, j: int,i:nat,x:int, y:int, A: multiset<int>)
{
	-1<=j<=|a|-2&&
	SortedSequence1(a,0,j)&&
	SortedSequence1(a,j+1,|a|-1)&&
	a[j+1]==y && 
	(j<=|a|-3 ==> a[j+2]>y) &&
	(0<=j<=|a|-3 ==> a[j+2]>=a[j]) &&
	multiset(a)==A
}



predicate Sorted1(a: array<int>, i:nat, j:int)
	requires i<=j ==> (0<=i<a.Length && 0<=j<a.Length)
	reads a
{
	 (forall k :: i <= k < j-1 ==> a[k] <= a[k+1]) 
}

predicate SortedSequence1(a: seq<int>, i:nat, h:int)
	requires i<=h ==> (0<=i <|a| && 0<=h<|a|)
{
	(forall k :: i <=  k <= h-1 ==> a[k] <= a[k+1])
}

method {:verify true} SwapPair(a: array<int>, x:nat,y:nat,ghost A: multiset<int>)
	requires multiset(a[..]) == A
	requires 0<=x<a.Length && 0<=y<a.Length
	requires x!=y
	ensures multiset(a[..]) == A
	ensures a[x] == old(a[y])
	ensures a[y] == old(a[x])
	ensures forall i :: 0<=i<a.Length ==> ((i!=x && i!=y) ==> a[i]==old(a[i]))
	modifies a
{
	// assignment
	LemmaSwapPair(a[..],old(a[..]), x, y, A);
	a[x], a[y] := a[y], a[x];
}

lemma LemmaSwapPair(a: seq<int>,oldA :seq <int>, x: nat, y: nat, A: multiset<int>)
	requires a==oldA
	requires multiset(a[..]) == A
	requires 0<=x<|a| && 0<=y<|a|
	requires x!=y
	ensures multiset(a[x:= oldA[y]][y:=oldA[x]]) == A
	ensures a[x:= oldA[y]][y:=oldA[x]][x] == oldA[y]
	ensures  a[x:= oldA[y]][y:=oldA[x]][y] == oldA[x]
	ensures forall i :: 0<=i<|a| ==> ((i!=x && i!=y) ==> a[x:= oldA[y]][y:=oldA[x]][i]==oldA[i])
{}

/*method {:verify true} SwapPair1(a: array<int>, x:nat,y:nat,i:nat,ghost A: multiset<int>)
	requires multiset(a[..]) == A
	requires 0<=x<a.Length && 0<=y<a.Length
	requires 0<=i<=a.Length-2
	requires SortedSequence1(a[..],0,x)&& SortedSequence1(a[..],y,i)
	ensures multiset(a[..]) == A
	ensures SortedSequence1(a[..],0,x) && SortedSequence1(a[..],y,i)
	ensures 0<=i<=a.Length-2
	modifies a
{
	// assignment
	//LemmaSwapPair1(a[..],old(a[..]), x, y, A);
	a[x], a[y] := a[y], a[x];
}

lemma LemmaSwapPair1(a: seq<int>,oldA :seq <int>, x: nat, y: nat, A: multiset<int>)
	requires a==oldA
	requires multiset(a[..]) == A
	requires 0<=x<|a| && 0<=y<|a|
	requires x!=y
	ensures multiset(a[x:= oldA[y]][y:=oldA[x]]) == A
	ensures a[x:= oldA[y]][y:=oldA[x]][x] == oldA[y]
	ensures  a[x:= oldA[y]][y:=oldA[x]][y] == oldA[x]
	ensures forall i :: 0<=i<|a| ==> ((i!=x && i!=y) ==> a[x:= oldA[y]][y:=oldA[x]][i]==oldA[i])
{}

*/