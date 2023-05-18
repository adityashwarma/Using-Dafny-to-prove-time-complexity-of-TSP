include "primMST.dfy"

method heuristic(p_id: int, t:nat, V: nat, graph: array2<int>) returns (res: int)
requires V >= 2;
requires graph.Length0 == graph.Length1 == V
requires 1 <= t < V;
{
    var visited := {};            //empty set
    visited := visited + {0, t} ; // set union
    var l := |visited|;
    var num:nat := V - l;
    assert num >= 0;
    if num !=0
    {
        var G := new nat[num, num];
        var i, j := 0,0;
        while i < num
        decreases num - i
        modifies G;
        {
            j := 0;
            while j < num
            decreases num - j
            modifies G;
            {
                G[i,j] := 0;
                j := j +1;
            }
            i := i + 1;
        }
        var key := 0;
        i := 0;
        var d_temp := new int[num];
        while(i < num)
        decreases num - i
        invariant 0 <= i <= num
        {
            if i !in visited
            {
                d_temp[i] := key;
                key := key + 1;
            }
            i := i + 1;
        }
        i := 0;
        while i < num
        decreases num - i
        invariant 0 <= i <= V
        {
            var j := 0;
            while j < num
            decreases num - j
            invariant 0 <= j <= V
            {
                assume forall k :: 0 <= k < num ==> d_temp[k] < num;
                assert i < V;
                if i !in visited && j !in visited
                {
                    var x := d_temp[i];
                    var y := d_temp[j];
                    var z := graph[i , j];
                }
                j:= j + 1;
            }
            i := i + 1;
        }
    }

}