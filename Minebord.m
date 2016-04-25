(* ::Package:: *)

(*
 * Copyright (C) 2013 Jose Madrigal Cardenas. All rights reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 *)

MakeBoard[n_]:=Block[{nr,nc,rangeR,rangeC,linesh,linesv,lines={},i,j},
	nr = n[[1]] + 1;
	nc = n[[2]] + 1;
	rangeR = Range[nr] - 1;
	rangeC = Range[nc] - 1;
	linesh = Map[Function[i, Line[{{i, 0}, {i, nr-1}}]], rangeC];
    linesv = Map[Function[i, Line[{{0, i}, {nc-1, i}}]], rangeR];
	lines = Join[linesh, linesv];
	lines
];

NumMines[b_]:=Block[{i,j,nos={},n},
	n=Dimensions[b];
    For[i=1, i<=n[[1]], i++,
        For[j=1, j<=n[[2]], j++,
			If[NRMine[b[[i,j]]],nos=Prepend[nos, Disk[{j-0.5, n[[1]]-i+0.5},0.25]];
            ,nos=Prepend[nos, Text[NNumber[b[[i,j]]],{j-0.5, n[[1]]-i+0.5}]];
			]
        ]
    ];
    nos
];

HiddenBoard[b_]:=Block[{i,j,nos={},n},
	n=Dimensions[b];
    For[i=1, i<=n[[1]], i++,
        For[j=1, j<=n[[2]], j++,
			If[NHidden[b[[i,j]]],nos=Join[nos,{Gray,EdgeForm[Thick],Rectangle[{j-1,n[[1]]-i}]}];
			If[NMine[b[[i,j]]], nos = Join[nos,{Red,Disk[{j-0.5, n[[1]]-i+0.5},0.25]}]]
            ,If[NFree[b[[i,j]]]=== -1 ,nos = Join[nos,{Black,Disk[{j-0.5, n[[1]]-i+0.5},0.25]}] ,nos=Join[nos, {Black,Text[NNumber[b[[i,j]]],{j-0.5, n[[1]]-i+0.5}]}]]
			]
        ]
    ];
    nos
];

DrawBoard[b_] := 
Block[{n, bl, q, all,nos},
        n=Dimensions[b];
        bl=MakeBoard[n];
        nos=NumMines[b];
        all=Join[bl, nos];
        Deploy[Graphics[all, ImageSize -> 20 n]]];

DrawBoardH[b_] := 
Block[{n, bl, q, all,nos},
        n=Dimensions[b];
        bl=MakeBoard[n];
		nos = HiddenBoard[b];
        all=Join[bl, nos];
        Deploy[Graphics[all, ImageSize -> 20 n]]];


(*Build Minesweeper Board with random Mines*)
BuildBoard[r_,c_]:=Block[{M,col,ren,Nmines,minas,i,j,coutmines=1},
	
	(*initializes the board*)
	M = Table[MakeNode[Null,True,False,0,False],{i,r},{j,c}];
	
	(*Level of mines*)
	If[r == 8 && c == 8, Nmines = 10,
		If[r == 16 && c == 16, Nmines = 40,
			If[r==16 && c == 30, Nmines = 99, Nmines = 40]]];
	
	(*Produces Random N number of Mines*)
	minas = RandomSample[Range[r*c],Nmines];
	minas = Sort[minas];
	For[i=1, i<= r, i++,
		For[j=1, j<= c, j++,
			If[Nmines >= 1 && coutmines == minas[[1]],
				M[[i,j]] = MakeNode[Null,True,False,0,True];
				minas = minas[[2;;]];
				Nmines -= 1;							
			];
			coutmines += 1;
		]
	];

	(*Produces Number in the squares*)
	For[i=1, i<= r, i++,
		For[j=1, j<= c, j++,
			(*Check limit from left adjacent*)
			If[NRMine[M[[i,j]]],		
				If[(i-1 >= 1), M[[i-1,j]] = MakeNode[Null,True,False,NNumber[M[[i-1,j]]]+1,NRMine[M[[i-1,j]]]]];
				If[(j-1 >= 1), M[[i,j-1]] = MakeNode[Null,True,False,NNumber[M[[i,j-1]]]+1,NRMine[M[[i,j-1]]]]];
				If[(i+1 <= r), M[[i+1,j]] = MakeNode[Null,True,False,NNumber[M[[i+1,j]]]+1,NRMine[M[[i+1,j]]]]];
				If[(j+1 <= c), M[[i,j+1]] = MakeNode[Null,True,False,NNumber[M[[i,j+1]]]+1,NRMine[M[[i,j+1]]]]];
				If[(i+1 <= r) && (j+1 <= c), M[[i+1,j+1]] = MakeNode[Null,True,False,NNumber[M[[i+1,j+1]]]+1,NRMine[M[[i+1,j+1]]]]];
				If[(i+1 <= r) && (j-1 >= 1), M[[i+1,j-1]] = MakeNode[Null,True,False,NNumber[M[[i+1,j-1]]]+1,NRMine[M[[i+1,j-1]]]]];
				If[(i-1 >= 1) && (j+1 <= c), M[[i-1,j+1]] = MakeNode[Null,True,False,NNumber[M[[i-1,j+1]]]+1,NRMine[M[[i-1,j+1]]]]];
				If[(i-1 >= 1) && (j-1 >= 1), M[[i-1,j-1]] = MakeNode[Null,True,False,NNumber[M[[i-1,j-1]]]+1,NRMine[M[[i-1,j-1]]]]];
			];
		]
	];
	M (*Return Matrix*)
];
