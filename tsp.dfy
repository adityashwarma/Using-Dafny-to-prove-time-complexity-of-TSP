include "primMST.dfy"

method tsp() returns (cost:int)
{
    var V:nat := 5;
    var graph := new int[V, V];
    graph[0,0]:= -1; graph[0, 1] := 169; graph[0, 2] := 36; graph[0, 3] := 121; graph[0, 4] := 169;
    graph[1,0]:= 169; graph[1, 1] := -1; graph[1, 2] := 143; graph[1, 3] := 107; graph[1, 4] := 146;
    graph[2,0]:= 36; graph[2, 1] := 143; graph[2, 2] := -1; graph[2, 3] := 99; graph[2, 4] := 49;
    graph[3,0]:= 121; graph[3, 1] := 107; graph[3, 2] := 99; graph[3, 3] := -1; graph[3, 4] := 77;
    graph[4,0]:= 73; graph[4, 1] := 146; graph[4, 2] := 49; graph[4, 3] := 77; graph[4, 4] := -1;

    var path, complexity := primMST(V, graph);
    assert path.Length >= 0;
    assert forall x :: 0 <= x < path.Length ==> 0 <= path[x] < V;
    var i := 0;
    cost := 0;
    while i < path.Length - 1
    decreases path.Length - i -1
    {
        var from := path[i];
        var to := path[i + 1];
        cost := graph[from, to];
        i := i + 1;
    }
}