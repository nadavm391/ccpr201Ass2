
method PairInsertionSort(a: array<int>)
	ensures Sorted1(a,0,a.Length-1)
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	//introdue local variable + leading assignemnt + weaken precondition
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
		//assignment
		LemmainitIJ(a,j,i,A);
		j,i:=j0,i0;
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
	j,i,x,y:=j0,i0,x0,y0;
	x,y:=a[i],a[i+1];
		if x<y {
			x,y:=y,x;
		}
		else{

		} 
		j:= i-1;
		while j>=0 && a[j]>x
			invariant Inv2Pair(a[..],j,i,x,y,A)
			decreases j
			{
				SwapPair(a,j+2,j,A);
				j:=j-1;
			}
		if a[j+2]!=x{
			LemmaMidswap(a[..],j,i,x,y,A);
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

lemma firstLoop(a: seq<int>,j:int,i:nat,x:int,y:int, A: multiset<int>)
	requires Inv2Pair(a,j,i,x,y,A) && j>=0 && a[j] > x
	ensures Inv2Pair(a[j:=a[j+2]][j+2:=a[j]],j-1,i,x,y,A)
{}
lemma secondLoop(a: seq<int>,j:int,i:nat,x:int,y:int, A: multiset<int>)
	requires Inv3Pair(a[..],j,i,x,y,A) && j>=0 && a[j] > y
	ensures Inv3Pair(a[j:=a[j+1]][j+1:=a[j]],j-1,i,x,y,A)
{}

lemma fourthLoop(a: seq<int>,j:int,i:nat,x:int,y:int, A: multiset<int>)
	requires Inv4Pair(a[..],j,i,x,y,A) && j>=0 && a[j] > y
	ensures Inv4Pair(a[j:=a[j+1]][j+1:=a[j]],j-1,i,x,y,A)
{
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
	SortedSequence1(a,j+2,|a|-1)&&
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
