
method PairInsertionSort(a: array<int>)
	ensures Sorted(a,0,a.Length-1)
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	//introduce logical constant + weaken precondition
	ghost var A := multiset(old(a[..]));
	PairInsertionSort1(a,A);
}
method PairInsertionSort1(a: array<int>, ghost A: multiset<int>) 	
	requires multiset(a[..])==A
	ensures Sorted(a,0,a.Length-1)
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
	ensures MainLoopInv(a[..],j,i,A)
	{
		j,i:=j0,i0;
		//assignment
		LemmainitIJ(a,j,i,A);
		j,i:=-1,0;
	}
lemma LemmainitIJ( a: array<int>, j: int,i:nat,  A: multiset<int>)
	requires multiset(a[..])==A
	ensures MainLoopInv(a[..],-1,0,A)
{}

method PairInsertionSort2(a: array<int>, j0: int,i0:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j: int,i:nat,x:int,y:int)
	requires MainLoopInv(a[..],j0,i0,A)
	ensures Sorted(a,0,a.Length-1)
	ensures multiset(a[..]) == A
	modifies a
{
	//sequential composition + contract frame
	j,i,x,y:=j0,i0,x0,y0;
	j,i,x,y:=MainLoop(a,j,i,x,y,A);
	j,y:=PairInsertionSort3(a,j,i,y,A);	

}

method MainLoop(a: array<int>, j0: int,i0:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j: int,i:nat,x:int,y:int)
	requires MainLoopInv(a[..],j0,i0,A)
	ensures MainLoopInv(a[..],j,i,A) && !GuardMainLoop(a,i)
	modifies a

{
	//iteration
	j,i,x,y:=j0,i0,x0,y0;
	while GuardMainLoop(a,i)
		decreases a.Length - i
		invariant MainLoopInv(a[..],j,i,A)
	{
		j,i,x,y:=MainLoopBody(a,j,i,x,y,A);
	}
}

method MainLoopBody(a: array<int>, j0: int,i0:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j: int,i:nat,x:int,y:int)
	requires MainLoopInv(a[..],j0,i0,A) && GuardMainLoop(a,i0)
	ensures MainLoopInv(a[..],j,i,A) && (a.Length-i)< (a.Length-i0)
	modifies a
{
	//sequential composition+contract frame
	j,i,x,y:=j0,i0,x0,y0;
	j,x,y:=preFirstInnerLoop(a,j,i,x,y,A);
	j,i:=MainLoopBody2(a,j,i,x,y,A);
}

method preFirstInnerLoop(a: array<int>, j0: int,i:nat,x0:int, y0:int, ghost A: multiset<int>) returns (j:int,x:int,y:int)
	requires MainLoopInv(a[..],j0,i,A) && GuardMainLoop(a,i)
	ensures FirstInnerLoopInv(a[..],j,i,x,y,A)
	{
		j,x,y:=j0,x0,y0;
		//leading assignemnt+following assignment+contract frame+weaken precondition
		x,y:=a[i],a[i+1];
		x,y:=adjustXY(a,j,i,x,y,A);
		j:= i-1;
	}
method adjustXY(a: array<int>, ghost j: int,ghost i:nat,x0:int, y0:int, ghost A: multiset<int>) returns (x:int,y:int)
	requires MainLoopInv(a[..],j,i,A) && GuardMainLoop(a,i) && x0==a[i]&&y0==a[i+1]
	ensures FirstInnerLoopInv(a[..],i-1,i,x,y,A)
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
method xSmaller (a: array<int>,ghost j: int,ghost i:nat,x0:int, y0:int, ghost A: multiset<int>) returns (x:int,y:int)
	requires MainLoopInv(a[..],j,i,A) && GuardMainLoop(a,i) && x0==a[i]&&y0==a[i+1] && x0<y0
	ensures FirstInnerLoopInv(a[..],i-1,i,x,y,A)

	{
		x,y:=x0,y0;
		//assignment
		x,y:=y,x;
	}

lemma LemmaxSmaller (a: array<int>, j: int,i:nat,x:int, y:int,  A: multiset<int>)
	requires MainLoopInv(a[..],j,i,A) && GuardMainLoop(a,i) && x==a[i]&&y==a[i+1] && x<y
	ensures FirstInnerLoopInv(a[..],i-1,i,y,x,A)

lemma LemmaxGreaterOrEqual (a: array<int>, j: int,i:nat,x:int, y:int,  A: multiset<int>)
	requires MainLoopInv(a[..],j,i,A) && GuardMainLoop(a,i) && x==a[i]&&y==a[i+1] && x>=y
	ensures FirstInnerLoopInv(a[..],i-1,i,x,y,A)

method MainLoopBody2(a: array<int>, j0: int,i0:nat,x:int, y:int, ghost A: multiset<int>) returns (j: int,i:nat)
	requires FirstInnerLoopInv(a[..],j0,i0,x,y,A)
	ensures MainLoopInv(a[..],j,i,A) && (a.Length-i)< (a.Length-i0)
	modifies a
{
	//sequential composition+contract frame
	j,i:=j0,i0;
	j:=firstInnerLoop(a,j,i,x,y,A);
	j,i:=MainLoopBody3(a,j,i,x,y,A);
}

method firstInnerLoop(a: array<int>, j0: int,ghost i:nat,x:int,ghost y:int, ghost A: multiset<int>) returns (j: int)
	requires FirstInnerLoopInv(a[..],j0,i,x,y,A)
	ensures FirstInnerLoopInv(a[..],j,i,x,y,A) && !GuardFirstInnerLoop(a,j,x)
	modifies a
	{
		j:=j0;
		//iteration
		while GuardFirstInnerLoop(a,j,x)
		invariant FirstInnerLoopInv(a[..],j,i,x,y,A)
		decreases j
		{
			j:=firstInnerLoopBody(a,j,i,x,y,A);
		}
	}

method firstInnerLoopBody(a: array<int>, j0: int,ghost i:nat,ghost x:int,ghost y:int, ghost A: multiset<int>) returns (j: int)
	requires FirstInnerLoopInv(a[..],j0,i,x,y,A) && GuardFirstInnerLoop(a,j0,x)
	ensures FirstInnerLoopInv(a[..],j,i,x,y,A) && j<j0
	modifies a

	{
		j:=j0;
		//following assignment+contract frame
		SwapFirstInner(a,j,i,x,y,A);
		j:=j-1;
	}
method {:verify true} SwapFirstInner(a: array<int>, j:int,ghost i: nat,ghost x:int,ghost y:int ,ghost A: multiset<int>) 
	requires FirstInnerLoopInv(a[..], j, i,x, y, A) && GuardFirstInnerLoop(a,j,x)
	ensures FirstInnerLoopInv(a[..], j-1, i,x, y, A) && j-1 < j
	modifies a
{
	// assignment
	LemmaSwapFirstInner(a, j, i, x, y, A);
	a[j+2], a[j] := a[j], a[j+2];
}

lemma LemmaSwapFirstInner(a: array<int>, j: int, i: nat,x:int,y:int, A: multiset<int>)
	requires FirstInnerLoopInv(a[..], j, i, x, y, A) && GuardFirstInnerLoop(a,j,x)
	ensures FirstInnerLoopInv(a[..][j := a[j+2]][j+2 := a[j]], j-1, i, x, y, A) 
{}

method MainLoopBody3(a: array<int>, j0: int,i0:nat,x:int, y:int, ghost A: multiset<int>) returns (j: int,i:nat)
	requires FirstInnerLoopInv(a[..],j0,i0,x,y,A) && !GuardFirstInnerLoop(a,j0,x)
	ensures MainLoopInv(a[..],j,i,A) && (a.Length-i)< (a.Length-i0)
	modifies a
{
	//sequential composition+contract frame 
	j,i:=j0,i0;
	preSecondInnerLoop(a,j,i,x,y,A);
	j,i:=MainLoopBody4(a,j,i,y,A);
}

method preSecondInnerLoop(a: array<int>, j: int,ghost i:nat,x:int, ghost y:int, ghost A: multiset<int>)
	requires FirstInnerLoopInv(a[..],j,i,x,y,A) && !GuardFirstInnerLoop(a,j,x)
	ensures SecondInnerLoopInv(a[..],j,i,y,A)
	modifies a
{
	//alternation
	if a[j+2]!=x{
		SwapPreSecondInner(a,j,i,x,y,A);
	}	
	else{
		LemmaPreSecondInnerNoswap(a,j,i,x,y,A);
	}
}

method {:verify true} SwapPreSecondInner(a: array<int>, j:int,ghost i: nat,ghost x:int,ghost y:int ,ghost A: multiset<int>) 
	requires FirstInnerLoopInv(a[..],j,i,x,y,A) && !GuardFirstInnerLoop(a,j,x) && a[j+2]!=x
	ensures SecondInnerLoopInv(a[..],j,i,y,A)
	modifies a
{
	// assignment
	LemmaSwapPreSecondInner(a, j, i, x, y, A);
	a[j+2], a[j+1] := a[j+1], a[j+2];
}

lemma LemmaSwapPreSecondInner(a: array<int>, j: int, i: nat,x:int,y:int, A: multiset<int>)
	requires FirstInnerLoopInv(a[..],j,i,x,y,A) && !GuardFirstInnerLoop(a,j,x) && a[j+2]!=x
	ensures SecondInnerLoopInv(a[..][j+1 := a[j+2]][j+2 := a[j+1]], j, i, y, A) 
{}

lemma LemmaPreSecondInnerNoswap(a: array<int>,j:int,i:nat,x:int,y:int, A: multiset<int>)
	requires FirstInnerLoopInv(a[..],j,i,x,y,A) && !GuardFirstInnerLoop(a,j,x) && a[j+2]==x
	ensures SecondInnerLoopInv(a[..],j,i,y,A)
{
}

method MainLoopBody4(a: array<int>, j0: int,i0:nat, y:int, ghost A: multiset<int>) returns (j: int,i:nat)
	requires SecondInnerLoopInv(a[..],j0,i0,y,A)
	ensures MainLoopInv(a[..],j,i,A) && (a.Length-i)< (a.Length-i0)
	modifies a
{
	//sequential composition + contract frame
	j,i:=j0,i0;
	j:=SecondInnerLoop(a,j,i,y,A);
	i:=MainLoopBody5(a,j,i,y,A);	
}
method SecondInnerLoop(a: array<int>, j0: int,ghost i:nat,y:int, ghost A: multiset<int>) returns (j: int)
	requires SecondInnerLoopInv(a[..],j0,i,y,A)
	ensures SecondInnerLoopInv(a[..],j,i,y,A) && !GuardSecondInnerLoop(a,j,y)
	modifies a
{
	//iteration
	j:=j0;
	while GuardSecondInnerLoop(a,j,y)
		invariant SecondInnerLoopInv(a[..],j,i,y,A)
		decreases j
		{
			j:=SecondInnerLoopBody(a,j,i,y,A);
		}
}
method SecondInnerLoopBody(a: array<int>, j0: int,ghost i:nat,y:int, ghost A: multiset<int>) returns (j: int)
	requires SecondInnerLoopInv(a[..],j0,i,y,A) && GuardSecondInnerLoop(a,j0,y)
	ensures SecondInnerLoopInv(a[..],j,i,y,A) && j<j0
	modifies a
{
	j:=j0;
	//contract frame+ following assignment
	SwapSecondInner(a,j,i,y,A);
	j:=j-1;
}

method {:verify true} SwapSecondInner(a: array<int>, j:int,ghost i: nat,ghost y:int ,ghost A: multiset<int>) 
	requires SecondInnerLoopInv(a[..],j,i,y,A) && GuardSecondInnerLoop(a,j,y)
	ensures SecondInnerLoopInv(a[..],j-1,i,y,A) && j-1<j
	modifies a
{
	// assignment
	LemmaSwapSecondInner(a, j, i, y, A);
	a[j+1], a[j] := a[j], a[j+1];
}

lemma LemmaSwapSecondInner(a: array<int>, j: int, i: nat,y:int, A: multiset<int>)
	requires SecondInnerLoopInv(a[..],j,i,y,A) && GuardSecondInnerLoop(a,j,y)
	ensures SecondInnerLoopInv(a[..][j := a[j+1]][j+1 := a[j]], j-1, i, y, A) && j-1<j
{}

method MainLoopBody5(a: array<int>, j: int,i0:nat, ghost y:int, ghost A: multiset<int>) returns (i:nat)
	requires SecondInnerLoopInv(a[..],j,i0,y,A) && !GuardSecondInnerLoop(a,j,y)
	ensures MainLoopInv(a[..],j,i,A) && (a.Length-i)< (a.Length-i0)
{
	i:=i0;
	//assignment
	LemmaMainLoopBody5(a,j,i,y,A);
	i:=i+2;
}

lemma LemmaMainLoopBody5(a: array<int>, j: int,i:nat,  y:int,  A: multiset<int>) 
	requires SecondInnerLoopInv(a[..],j,i,y,A) && !GuardSecondInnerLoop(a,j,y)
	ensures MainLoopInv(a[..],j,i+2,A) && (a.Length-(i+2))< (a.Length-i)
	{}


method PairInsertionSort3(a: array<int>, j0: int,i:nat, y0:int, ghost A: multiset<int>) returns (j: int,y:int)
	requires  MainLoopInv(a[..],j0,i,A) && !GuardMainLoop(a,i)
	ensures Sorted(a,0,a.Length-1)
	ensures multiset(a[..]) == A
	modifies a
{
	j,y:=j0,y0;
	//alternation
	if i==a.Length-1{
		j,y:=iEqualsLastPlace(a,j,i,y,A);
	}
	else {
		LemmaINotEqualsLastPlace(a,j,i,y,A);
	}	
}
lemma LemmaINotEqualsLastPlace(a: array<int>, j: int,i:nat, y:int,  A: multiset<int>)
	requires MainLoopInv(a[..],j,i,A) && !GuardMainLoop(a,i) && i!=a.Length-1
	ensures Sorted(a,0,a.Length-1)
	ensures multiset(a[..]) == A
	{}
	
method iEqualsLastPlace(a: array<int>, j0: int,i:nat, y0:int, ghost A: multiset<int>) returns (j: int,y:int)
	requires MainLoopInv(a[..],j0,i,A) && !GuardMainLoop(a,i) && i==a.Length-1
	ensures Sorted(a,0,a.Length-1)
	ensures multiset(a[..]) == A
	modifies a
{
	j,y:=j0,y0;
	//sequential composition + strengthen postcondition+contract frame
	j,y := initJI(a,j,i,y,A);
	j:=postLoop(a,j,i,y,A);
	LemmaStrenghtenPostLoop(a,j,i,y,A);
}
lemma LemmaStrenghtenPostLoop(a: array<int>, j: int,i:nat, y:int,  A: multiset<int>) 
	requires PostLoopInv(a[..],j,i,y,A)&& !GuardPostLoop(a,j,y)
	ensures Sorted(a,0,a.Length-1)
	ensures multiset(a[..]) == A

method initJI(a: array<int>, j0: int,i:nat, y0:int, ghost A: multiset<int>) returns (j: int,y:int)
	requires MainLoopInv(a[..],j0,i,A) && !GuardMainLoop(a,i) && i==a.Length-1
	ensures PostLoopInv(a[..],j,i,y,A)
{
	j,y:=j0,y0;
	//assignment
	j,y := i-1,a[i];
}

lemma LemmainitJI(a: array<int>, j0: int,i:nat, y0:int,  A: multiset<int>) 
	requires MainLoopInv(a[..],j0,i,A) && !GuardMainLoop(a,i) && i==a.Length-1
	ensures PostLoopInv(a[..],i-1,i,a[i],A)
	{}

method postLoop(a: array<int>, j0: int,i:nat, y:int, ghost A: multiset<int>) returns (j: int)
	requires PostLoopInv(a[..],j0,i,y,A)
	ensures PostLoopInv(a[..],j,i,y,A)&& !GuardPostLoop(a,j,y)
	modifies a
{
	j:=j0;
	//iteration
	while GuardPostLoop(a,j,y)
		invariant PostLoopInv(a[..],j,i,y,A)
		decreases j
	{
		j:=postLoopBody(a,j,i,y,A);
	}
}

method postLoopBody(a: array<int>, j0: int,i:nat, y:int, ghost A: multiset<int>) returns (j: int)
	requires PostLoopInv(a[..],j0,i,y,A) && GuardPostLoop(a,j0,y)
	ensures PostLoopInv(a[..],j,i,y,A)&& j<j0
	modifies a
{
	j:=j0;
	//following assignment+contract frame
	SwapPost(a,j,i,y,A);
	j:=j-1;
}

method {:verify true} SwapPost(a: array<int>, j:int,ghost i: nat,ghost y:int ,ghost A: multiset<int>) 
	requires PostLoopInv(a[..],j,i,y,A) && GuardPostLoop(a,j,y)
	ensures PostLoopInv(a[..],j-1,i,y,A)&& j-1<j
	modifies a
{
	// assignment
	LemmaSwapPost(a, j, i, y, A);
	a[j+1], a[j] := a[j], a[j+1];
}

lemma LemmaSwapPost(a: array<int>, j: int, i: nat,y:int, A: multiset<int>)
	requires PostLoopInv(a[..],j,i,y,A) && GuardPostLoop(a,j,y)
	ensures PostLoopInv(a[..][j := a[j+1]][j+1 := a[j]], j-1, i, y, A) && j-1<j
{}
predicate method GuardMainLoop(a: array<int>,i:nat)
{
	i < a.Length-1	
}

predicate method GuardFirstInnerLoop(a: array<int>,j:int,x:int)
	requires -1<=j<=a.Length-3
	reads a
{
	 j>=0 && a[j]>x	
}

predicate method GuardSecondInnerLoop(a: array<int>,j:int,y:int)
	requires -1<=j<=a.Length-3
	reads a
{
	 j>=0 && a[j] > y
}

predicate method GuardPostLoop(a: array<int>,j:int,y:int)
	requires -1<=j<=a.Length-2
	reads a
{
	 j>=0 && a[j] > y
}



predicate MainLoopInv(a: seq<int>, j: int, i:nat, A: multiset<int>)
{
	0<=i<=|a| &&
	(|a|>1 ==> (-1<=j<=|a|-3)) &&
	SortedSequence(a,0,i-1) &&
	multiset(a)==A
}
predicate FirstInnerLoopInv(a: seq<int>, j: int,i:nat,x:int, y:int, A: multiset<int>)
{
	0<=i<=|a|-2 &&
	-1<=j<=|a|-3 &&
	SortedSequence(a,0,j)&&
	SortedSequence(a,j+2,i+1)&&
	(0<=j<i-1 ==> a[j+3]>=a[j]) &&
	(j<i-1  ==> a[j+3]>x) &&
	((x==a[j+1]&&y==a[j+2]) || (x==a[j+2]&&y==a[j+1])) && x>=y &&
	multiset(a)==A
}

predicate SecondInnerLoopInv(a: seq<int>, j: int,i:nat, y:int, A: multiset<int>)
{
	0<=i<=|a|-2 &&
	-1<=j<=|a|-3 &&
	SortedSequence(a,0,j)&&
	SortedSequence(a,j+1,i+1)&&
	a[j+2]>=y &&
	(j>=0 ==> a[j+2]>=a[j]) &&
	a[j+1]==y &&
	multiset(a)==A
}

predicate PostLoopInv(a: seq<int>, j: int,i:nat, y:int, A: multiset<int>)
{
	-1<=j<=|a|-2&&
	SortedSequence(a,0,j)&&
	SortedSequence(a,j+1,|a|-1)&&
	a[j+1]==y && 
	(j<=|a|-3 ==> a[j+2]>y) &&
	(0<=j<=|a|-3 ==> a[j+2]>=a[j]) &&
	multiset(a)==A
}



predicate Sorted(a: array<int>, i:nat, j:int)
	requires i<=j ==> (0<=i<a.Length && 0<=j<a.Length)
	reads a
{
	 (forall k :: i <= k < j-1 ==> a[k] <= a[k+1]) 
}

predicate SortedSequence(a: seq<int>, i:nat, h:int)
	requires i<=h ==> (0<=i <|a| && 0<=h<|a|)
{
	(forall k :: i <=  k <= h-1 ==> a[k] <= a[k+1])
}