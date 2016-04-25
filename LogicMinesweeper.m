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

(*Check if the number of the box is equal to the number of adjacent mines covered if these are met are marked as mines*)
RuleOne[board_,r_,c_,d_,UnS_,UnL_,E_,C_,MM_]:=Block[{adyMines=0,b = {board,UnS,UnL,E,C,MM},marked={},i,sizemk},
	If[CornerLU[r,c,d] && NHidden[b[[1]][[r-1,c-1]]], adyMines+=1; AppendTo[marked,{r-1,c-1}]];
	If[CornerLD[r,c,d] && NHidden[b[[1]][[r+1,c-1]]], adyMines+=1; AppendTo[marked,{r+1,c-1}]];
	If[CornerRU[r,c,d] && NHidden[b[[1]][[r-1,c+1]]], adyMines+=1; AppendTo[marked,{r-1,c+1}]];
	If[CornerRD[r,c,d] && NHidden[b[[1]][[r+1,c+1]]], adyMines+=1; AppendTo[marked,{r+1,c+1}]];
	If[CheckR[r,c,d] && NHidden[b[[1]][[r,c+1]]], adyMines+=1; AppendTo[marked,{r,c+1}]];
	If[CheckL[r,c,d] && NHidden[b[[1]][[r,c-1]]], adyMines+=1; AppendTo[marked,{r,c-1}]];
	If[CheckU[r,c,d] && NHidden[b[[1]][[r-1,c]]], adyMines+=1; AppendTo[marked,{r-1,c}]];
	If[CheckD[r,c,d] && NHidden[b[[1]][[r+1,c]]], adyMines+=1; AppendTo[marked,{r+1,c}]];
	If[adyMines == NFree[b[[1]][[r,c]]],
		sizemk = Length[marked];
		For[i=1, i <= sizemk, i++,
			If[!NMine[b[[1]][[marked[[i,1]],marked[[i,2]]]]], b[[1]][[marked[[i,1]],marked[[i,2]]]] = MakeNode[Null,True,True,0,True]; b[[4]] = True; b[[5]] = True; b[[6]]-= 1;];
		 ]		
	];
	b (*Return board*)		
];
(*Check whether the adjacent boxes marked mine is equal to the number of the box, if it is true, then the other boxes are not mine and discovered*)
RuleTwo[board_,r_,c_,d_,UnS_,UnL_,E_,C_]:=Block[{adyMines = 0, b = {board,UnS,UnL,E,C}, marked={},sizemk,i},
	If[CornerLU[r,c,d] && NMine[b[[1]][[r-1,c-1]]], adyMines+=1,  If[CornerLU[r,c,d],AppendTo[marked,{r-1,c-1}]]];
	If[CornerLD[r,c,d] && NMine[b[[1]][[r+1,c-1]]], adyMines+=1,  If[CornerLD[r,c,d],AppendTo[marked,{r+1,c-1}]]];
	If[CornerRU[r,c,d] && NMine[b[[1]][[r-1,c+1]]], adyMines+=1,  If[CornerRU[r,c,d],AppendTo[marked,{r-1,c+1}]]];
	If[CornerRD[r,c,d] && NMine[b[[1]][[r+1,c+1]]], adyMines+=1,  If[CornerRD[r,c,d],AppendTo[marked,{r+1,c+1}]]];
	If[CheckR[r,c,d] && NMine[b[[1]][[r,c+1]]], adyMines+=1, If[CheckR[r,c,d],AppendTo[marked,{r,c+1}]]];
	If[CheckL[r,c,d] && NMine[b[[1]][[r,c-1]]], adyMines+=1, If[CheckL[r,c,d],AppendTo[marked,{r,c-1}]]];
	If[CheckU[r,c,d] && NMine[b[[1]][[r-1,c]]], adyMines+=1, If[CheckU[r,c,d],AppendTo[marked,{r-1,c}]]];
	If[CheckD[r,c,d] && NMine[b[[1]][[r+1,c]]], adyMines+=1, If[CheckD[r,c,d],AppendTo[marked,{r+1,c}]]];
	
	If[adyMines == NFree[b[[1]][[r,c]]],
		sizemk = Length[marked];
		For[i=1, i <= sizemk, i++,
			If[NHidden[b[[1]][[marked[[i,1]],marked[[i,2]]]]], b = Discover[b[[1]],marked[[i,1]],marked[[i,2]],d,b[[2]],b[[3]],b[[4]],b[[5]]],Continue[]];
		 ]
	]; 
	b (*Return board*)
];

(*See the box at the receiving position, if the box is zero performs expansion*)
Discover[board_,r_,c_,d_,UnS_,UnL_,E_,C_]:=Block[{b = {board,UnS,UnL,E,C}},
	(*In Free put the number and update the Hidden*)
	If[NRMine[b[[1]][[r,c]]], b[[1]][[r,c]] = MakeNode[-1,False,False,NNumber[b[[1]][[r,c]]],NRMine[b[[1]][[r,c]]]]; Return[{b[[1]],b[[2]],b[[3]],Lost,b[[5]]}],
	b[[1]][[r,c]] = MakeNode[NNumber[b[[1]][[r,c]]],False,False,NNumber[b[[1]][[r,c]]],NRMine[b[[1]][[r,c]]]];
	b[[2]] = b[[2]] - 1; (*Minus 1 to the total of hidden squares*)
	AppendTo[b[[3]],{r,c}]; (*Save to free list*)
	b[[4]] = True;
	b[[5]] = True;	 

	If[NNumber[board[[r,c]]] == 0,
		If[CornerLU[r,c,d] && NHidden[b[[1]][[r-1,c-1]]],b = Discover[b[[1]],r-1,c-1,d,b[[2]],b[[3]],b[[4]],b[[5]]]];
		If[CornerLD[r,c,d] && NHidden[b[[1]][[r+1,c-1]]],b = Discover[b[[1]],r+1,c-1,d,b[[2]],b[[3]],b[[4]],b[[5]]]];
		If[CornerRU[r,c,d] && NHidden[b[[1]][[r-1,c+1]]],b = Discover[b[[1]],r-1,c+1,d,b[[2]],b[[3]],b[[4]],b[[5]]]];
		If[CornerRD[r,c,d] && NHidden[b[[1]][[r+1,c+1]]],b = Discover[b[[1]],r+1,c+1,d,b[[2]],b[[3]],b[[4]],b[[5]]]];
		If[CheckR[r,c,d] && NHidden[b[[1]][[r,c+1]]],b = Discover[b[[1]],r,c+1,d,b[[2]],b[[3]],b[[4]],b[[5]]]];
		If[CheckL[r,c,d] && NHidden[b[[1]][[r,c-1]]],b = Discover[b[[1]],r,c-1,d,b[[2]],b[[3]],b[[4]],b[[5]]]];
		If[CheckU[r,c,d] && NHidden[b[[1]][[r-1,c]]],b = Discover[b[[1]],r-1,c,d,b[[2]],b[[3]],b[[4]],b[[5]]]];
		If[CheckD[r,c,d] && NHidden[b[[1]][[r+1,c]]],b = Discover[b[[1]],r+1,c,d,b[[2]],b[[3]],b[[4]],b[[5]]]];
	];
	b (*Return Board*)
	]
];
