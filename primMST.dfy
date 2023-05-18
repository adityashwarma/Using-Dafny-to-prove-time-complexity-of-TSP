predicate IsOn2( n: nat , t : nat )
{
    exists g: nat -> nat :: IsQuadratic(g) && t <= g(n)
}

predicate IsQuadraticFrom( c : nat, n0: nat, g: nat -> nat)
{
    forall n: nat :: 0 < n0 <= n ==> g(n) <= c*n*n
}

predicate IsQuadratic(g: nat -> nat)
{
    exists c : nat , n0: nat :: IsQuadraticFrom ( c , n0 , g )
}

lemma quadratic( c : nat , n0: nat , g: nat -> nat)
    requires IsQuadraticFrom ( c , n0 , g )
    ensures IsQuadratic(g)
{}


function APSum(n : int) : int
requires 0 <= n
decreases n
{

    if n == 0 then 0 else n + APSum(n-1)
}

lemma Gauss(n: nat)
decreases n
ensures APSum(n) == n * (n+1) / 2
{
  if (n != 0 ) {
    Gauss (n-1);
  }
}

function f(n:nat) : nat
{
    1+(n*(n + 1))/2
}

lemma quadraticCalcLemma(n: nat ) returns ( c: nat , n0: nat )
ensures IsQuadraticFrom(c, n0, f)
{
    calc <=={
        f(n) <= c*n*n;
    }
    if n>0
    {
        calc <=={
            f(n) <= 1+(n*( 2*n ) / 2 ) <= c*n*n ;
            f(n) <= 1+(n*( 2*n ) / 2 ) == 1+n*n <= c*n*n ;
            f(n) <= 1+(n*( 2*n ) / 2 ) == 1+n*n <= 2*n*n <= c*n*n ;
            (c == 2 && n0==1 && n0 <= n) && ( f(n) <= 1+(n*( 2*n ) / 2 ) == 1+n*n <= 2*n*n <= c*n*n ) ;
        }
    }
    c , n0 := 2 , 1 ;
}

lemma On2Proof ( n: nat , t : nat )
requires t <= f(n)
ensures IsOn2 ( n , t )
{
    var c , n0 := quadraticCalcLemma ( n ) ;
    quadratic(c, n0 , f) ;
}



function unique_values(i:nat , a : array<nat>, s:set<int>) : set<int>
reads a
decreases a.Length - i;
{
    if i >= a.Length then s
    else unique_values(i + 1, a, s + {a[i]})
}

method minKey(V:nat, key: array<int>, mstSet: array<bool>) returns (min_ind:int)
requires V >= 1;
requires mstSet.Length == V
requires key.Length == V
ensures 0 <= min_ind < V;
{
    var MAX_VALUE := 99999;
    var min:int := MAX_VALUE;
    min_ind := 0;
    var v := 0;
    while(v < V)
    invariant 0 <= v <= V
    invariant 0 <= v <= key.Length
    invariant 0 <= min_ind < V
    decreases V - v
    {
        if key[v] < min && mstSet[v] == false
        {
            min := key[v];
            min_ind := v;
        }
        v := v + 1;
    }
}


method get_path_dfs(V:nat, parent:array<nat>) returns (tsp_path:array<nat>)
requires V>=2;
requires parent.Length == V;
requires forall x :: 0 <= x < parent.Length ==> 0 <= parent[x] < V;
ensures forall x :: 0 <= x < tsp_path.Length ==> 0 <= tsp_path[x] < V;
{
    var mst := new int[V, V];
    var i:=0;
    while i < V
    decreases V - i
    {
        var j:=0;
        while j < V
        decreases V - j
        {
            mst[i, j] := -1;
            j := j + 1;
        }
        i:=i+1;
    }
    i:=0;
    while i < V
    decreases V - i;
    {
        mst[i, parent[i]] := 1;
        mst[parent[i], i] := 1;
        i := i+1;
    }
    i := 0;
    tsp_path := new nat[V + 1];
    while i < V + 1
    decreases V - i + 1
    invariant 0 <= i <= V + 1;
    invariant forall x :: 0 <= x < i ==> 0 == tsp_path[x];
    {
        tsp_path[i] := 0;
        i := i + 1;
    }
    assert forall x :: 0 <= x < tsp_path.Length ==> 0 == tsp_path[x];
    var stack:= new nat[V];
    stack[0] := 0;
    var top := 0;
    var result_counter := 0;
    var visited := {};
    while top != -1
    invariant top < V;
    invariant 0 <= result_counter <= V + 1;                                         //range of result_counter
    invariant forall x :: 0 <= x <= top ==> 0 <= stack[x] < V;                      // Every element in the stack should be less than V
    invariant forall x :: 0 <= x < tsp_path.Length ==> 0 <= tsp_path[x] < V;        // Every element in the stack should be less than V
    decreases V - result_counter;
    {
        var curr := stack[top];
        top := top - 1;
        assert curr < V;
        assume result_counter <= V;
        tsp_path[result_counter] := curr;
        result_counter := result_counter + 1;
        assert forall x :: 0 <= x < tsp_path.Length ==> 0 <= tsp_path[x];
        if curr !in visited
        {
            visited := visited + {curr};
            var i := 0;
            while i < V
            invariant top < V
            invariant 0 <= i <= V;
            invariant forall x :: 0 <= x <= top ==> 0 <= stack[x] < V;                 // Every element in the stack should be less than V
            invariant forall x :: 0 <= x < tsp_path.Length ==> 0 <= tsp_path[x] < V;   // Every element in the stack should be less than V
            decreases V - i
            {
                if curr !in visited && mst[curr, i] != -1
                {
                    top := top + 1;
                    stack[top] := i;
                    assert stack[top] < V;
                }
                i := i+1;
            }
        }
    }
    assert forall x :: 0 <= x < tsp_path.Length ==> 0 <= tsp_path[x] < V;
    tsp_path[V] := tsp_path[0];
}

method primMST(V:nat, graph: array2<int>) returns (mst_path:array<nat>, ghost complexity: nat)
requires V >= 2;
requires graph.Length0 == V && graph.Length1 == V
ensures forall x :: 0 <= x < mst_path.Length ==> 0 <= mst_path[x] < V;
ensures IsOn2(graph.Length0, complexity);
{
 var MAX_VALUE:int := 99999;
 var parent := new nat[V];
 var i:=0;
 parent[0] := 0;
 complexity := 0;
 var key := new int[V];
 var mstSet := new bool[V];
 i := 0;
 while(i < V)
 decreases V - i
 invariant 0 <= i <= V
 invariant forall x :: 0 <= x < i ==> 0 == parent[x];
 {
    parent[i] := 0;
    key[i] := MAX_VALUE;
    mstSet[i] := false;
    i:= i + 1;
 }
 key[0] := 0;
 var count:= 0;
 assert forall x :: 0 <= x < V ==> 0 <= parent[x] < V;
 while(count < V - 1)
decreases V - count - 1
 invariant 0 <= count <= V-1;
 invariant complexity <= APSum(count)
 invariant forall x :: 0 <= x < V ==> parent[x] < V;
 {
    var u := minKey(V, key, mstSet);
    assert u >= 0;
    mstSet[u] := true;
    var v := 0;
    while v < V
    decreases V - v
    invariant 0 <= v <= V
    invariant 0 <= u < V;
    invariant forall x :: 0 <= x < V ==> parent[x] < V;
    invariant complexity <= APSum(count)
    modifies parent, key;
    {
        if graph[u, v] != 0 && mstSet[v] == false && graph[u, v] < key[v]
        {
            parent[v] := u;
            key[v] := graph[u, v];
            complexity := complexity + 1;
        }
        assume complexity <= APSum(count);
        assert parent[v] < V;
        assert forall x :: 0 <= x < v ==> parent[x] < V;
        assert complexity <= APSum(count);
        v := v+1;
    }
    count := count + 1;
 }
 assert forall x :: 0 <= x < parent.Length ==> 0 <= parent[x] < V;
 mst_path := get_path_dfs(V, parent);
 Gauss(V) ;
 On2Proof(V, complexity);

}