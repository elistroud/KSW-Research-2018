(* Wolfram Language package *)
maximalQ[mat1_] :=
  Module[{t, mat2},
   t = True;
   Do[
    If[i != j && mat1[[i, j]] == 0,
     mat2 = mat1;
     mat2[[i, j]] = 1;
     mat2[[j, i]] = 1;
     If[MemberQ[primegraphs, mat2],
      t = False;
      Break[]
      ]
     ],
    {i, Length[mat1]}, {j, i, Length[mat1]}
    ];
   Return[t(*{t,AdjacencyGraph[mat2],MatrixForm[mat2-mat1]}*)];
   ];
primeGraphQ[mat1_] :=
  Module[{t, mat2},
   t = False;
   mat2 = MatrixPower[mat1, 3];
   If[ContainsOnly[Table[mat2[[k, k]], {k, Length[mat1]}], {0}],
    If[ChromaticPolynomial[AdjacencyGraph[mat1], 3] != 0,
     t = True;
     ]];
   Return[t];
   ];
findAllGraphs[mat1_, starti_, startj_] :=
  Module[{mat2, i, j},
   i = starti;
   j = startj;
   If[i == Length[mat1] && j > Length[mat1],
    If[primeGraphQ[mat1],
     Sow[mat1];],
    If[j > Length[mat1],
     i = i + 1;
     j = i;];
    findAllGraphs[mat1, i, j + 1];
    If[i != j,
     mat2 = mat1;
     mat2[[i, j]] = 1;
     mat2[[j, i]] = 1;
     (*Echo[mat2];*)
     findAllGraphs[mat2, i, j + 1];];
    ]
   ];
$RecursionLimit = 10000
(*Get["7primegraphs.m"]*)
graphs = Reap[findAllGraphs[ConstantArray[0, {6, 6}], 1, 1]][[2, 1]];
(*primegraphs = Parallelize[Select[graphs, primeGraphQ]];*)
maximalprimegraphs = Parallelize[Select[primegraphs, maximalQ]];
isomaxprimegraphs = AdjacencyGraph /@ maximalprimegraphs;
isomaxprimegraphs = Tuples[{isomaxprimegraphs, isomaxprimegraphs}];
isomaxprimegraphsbool = 
 Reap[Do[Sow[
     IsomorphicGraphQ[isomaxprimegraphs[[i, 1]], 
      isomaxprimegraphs[[i, 2]]]], {i, Length[isomaxprimegraphs]}]][[
  2, 1]];
isomaxgraphs = Reap[Do[
     If[
      Apply[BooleanCountingFunction[1, i], 
       isomaxprimegraphsbool[[
        i ;; ((i - 1)*Length[maximalprimegraphs] + i) ;; 
         Length[maximalprimegraphs]]]],
      Sow[maximalprimegraphs[[i]]]
      ],
     {i, Length[maximalprimegraphs]}
     ]][[2, 1]];
minimalPrimeGraphs = 
 GraphComplement /@ 
  AdjacencyGraph /@ 
   Select[isomaxgraphs, 
    ConnectedGraphQ[GraphComplement[AdjacencyGraph[#]]] &]
MinimalPrimeGraphs