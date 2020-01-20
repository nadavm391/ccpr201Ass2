method PairInsertionSort(a: array<int>)
	requires a.Length>1
	ensures Sorted(a,0,a.Length-1)
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	ghost var A := multiset(a[..]);
	var i,j,x,y;
	i:=0;
	j:=i-1;
	while i < a.Length-1
		decreases (a.Length-1) - i
		invariant Inv(a[..],i,j,A)
	{
		x,y:=a[i],a[i+1];
		if x<y {
			x,y:=y,x;
		}
		j:= i-1;
		while j>=0 && a[j]>x
			invariant Inv2(a[..],j,i,x,y,A)
			decreases j
			{
				Swap(a,j+2,j,A);
				j:=j-1;
			}
		if a[j+2]!=x{
			Swap(a,j+2,j+1,A);
		}	
		else{

		}

		while j>=0 && a[j] > y
			invariant Inv3(a[..],j,i,x,y,A)
			decreases j
			{
				Swap(a,j+1,j,A);
				j:=j-1;
			}
		
		i:=i+2;	
	}

	if i==a.Length-1{
		j,y := i-1,a[i];
		while j>=0 && a[j] >y
			invariant Inv4(a[..],j,i,x,y,A)
			decreases j
		{
			Swap(a,j+1,j,A);
			j:=j-1;
		}
	}
	else {

	}	

}
predicate Inv2(a: seq<int>, j: int,i:nat,x:int, y:int, A: multiset<int>)
{
	0<=i<=|a|-1 &&
	0<=j<=|a|-3&&
	SortedSequence(a,0,j-1)&&
	SortedSequence(a,j+2,i+1)&& 
	(j>0 ==> a[j+2]>=a[j-1]) &&
	a[j+2]>x &&
	multiset(a) == A&&
	((a[j] == x && a[j+1] == y) || (a[j]==y && a[j+1] == x))
}

predicate Sorted(a: array<int>, i:nat, j:int)
	requires j>0 
	requires i<=j ==> (0<=i<a.Length && 0<=j<a.Length)
	reads a
{
	 (forall k :: i <= k < j-1 ==> a[k] <= a[k+1]) || a.Length<=1
}

predicate SortedSequence(a: seq<int>, i:nat, h:int)
	requires h>-2
	requires i<=h ==> (0<=i< |a| && 0<=h<=|a|)
{
	(forall k :: i <= k <= h-2 ==> a[k] <= a[k+1]) || |a|<=1
}
predicate Inv(a: seq<int>, i: nat, j:int, A: multiset<int>)
{
	0<=i<=|a|+1 &&
	(-1<=j<=|a|-3) && 
	multiset(a) == A &&
	SortedSequence(a,0,i-1) 
}

predicate Inv3(a: seq<int>, j: int,i:nat,x:int, y:int, A: multiset<int>)
{
	0<=i<=|a|-1 &&
	0<=j<=|a|-3&&
	SortedSequence(a,0,j-1)&&
	SortedSequence(a,j+1,i+1)&& 
	(j>0 ==> a[j+1]>=a[j-1]) &&
	a[j+1]>y &&
	multiset(a) == A&&
	a[j] == y 
}

predicate Inv4(a: seq<int>, j: int,i:nat,x:int, y:int, A: multiset<int>)
{
	0<=j<=|a|-2&&
	SortedSequence(a,0,j-1)&&
	SortedSequence(a,j+1,|a|-1)&& 
	(j>0 ==> a[j+1]>=a[j-1]) &&
	a[j+1]>y &&
	multiset(a) == A&&
	a[j] == y 
}





method {:verify true} Swap(a: array<int>, x:nat,y:nat,ghost A: multiset<int>)
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
	LemmaSwap(a[..],old(a[..]), x, y, A);
	a[x], a[y] := a[y], a[x];
}

lemma LemmaSwap(a: seq<int>,oldA :seq <int>, x: nat, y: nat, A: multiset<int>)
	requires |a|==|oldA|
	requires forall i:: 0<=i<|a| ==> a[i]==oldA[i]
	requires 0<=x<|a| && 0<=y<|a|
	requires x!=y
	ensures a[x:= oldA[y]][y:=oldA[x]][x] == oldA[y]
	ensures  a[x:= oldA[y]][y:=oldA[x]][y] == oldA[x]
	ensures forall i :: 0<=i<|a| ==> ((i!=x && i!=y) ==> a[x:= oldA[y]][y:=oldA[x]][i]==oldA[i])
{}

// this helps in justifying the move from the initial guard to the efficient one,
// with no need to change anything in the initial development:
// the (LHS ==> RHS) helps in the loop body,
// and (LHS <== RHS) helps upon termination of the loop
