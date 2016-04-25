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

Clear[Lost];
Clear[MakeNode,NFree,NHidden,NMine,NNumber,NRMine];
(**************************************
Node states: 
(THE AGENT CAN SEE THE FOLLOW STATES)
-free (free, It contains a number from zero to eight)
-hidden (hidden square)
-mine (marked as a mine)

(THE AGENT CAN NOT SEE THE FOLLOW FIELDS)
-Numero (Real number under the cover locality)
-RealMina (Mine under the cover locality)
**************************************)
MakeNode[free_,hidden_,mine_,number_,Rmine_]:=Block[{}, 
Nodo[Fr[free],Hi[hidden],Mi[mine],Num[number],RMi[Rmine]]];

NFree[Nodo[Fr[f_],h_,m_,n_,rm_]]:=f;
NHidden[Nodo[f_,Hi[h_],m_,n_,rm_]]:=h;
NMine[Nodo[f_,h_,Mi[m_],n_,rm_]]:=m;
NNumber[Nodo[f_,h_,m_,Num[n_],rm_]]:=n;
NRMine[Nodo[f_,h_,m_,n_,RMi[rm_]]]:=rm;

(*
IMPORTAT VARIABLES
Board - Matrix representing the board
UncoverSquares - Number of squares that are not undiscovered mines (used for termination condition)
UncoverList - Queue to add the boxes discovered to explore them
Events - It indicates whether some event happens so explore and not to pick a random box
Changes - Indicates whether the board change (Used for graphic representation of the board)
MarkMines - Number of squares are mines that are not marked (used for termination condition)
*)

LogicAgent[r_,c_,NoAnim_:False]:=Block[{Board,Events=False,Free = {},sizeL,ren,col,dimensions = {r,c},
						UncoverList={},UncoverSquares,Changes = False,MarkMines,k,display={},sttt=1,realb,gameover=0},
	Board = BuildBoard[r,c];
	realb = DrawBoard[Board];
	If[!NoAnim,display={realb};
	AppendTo[display,DrawBoardH[Board]]];
	{UncoverSquares,MarkMines} = GetSquaresHidden[r,c]; (*Number of squares to be discovered and mines to be marked*)
	While[UncoverSquares !=  0 || MarkMines != 0,
		If[!Events,{ren,col} = ChooseRandom[Board,r,c];
					{Board,UncoverSquares,UncoverList,Events,Changes} = Discover[Board,ren,col,dimensions,UncoverSquares,UncoverList,Events,Changes];
					If[Changes === True && !NoAnim,AppendTo[display,DrawBoardH[Board]]];
			, Events = False;
			For[k=1,k<= Length[UncoverList], k++,
				If[Events
					,{Board,UncoverSquares,UncoverList,Events,Changes,MarkMines} = RuleOne[Board,UncoverList[[k,1]],UncoverList[[k,2]],dimensions,UncoverSquares,UncoverList,True,False,MarkMines]
					,{Board,UncoverSquares,UncoverList,Events,Changes,MarkMines} = RuleOne[Board,UncoverList[[k,1]],UncoverList[[k,2]],dimensions,UncoverSquares,UncoverList,False,False,MarkMines]];
			{Board,UncoverSquares,UncoverList,Events,Changes} = RuleTwo[Board,UncoverList[[k,1]],UncoverList[[k,2]],dimensions,UncoverSquares,UncoverList,Events,Changes];
			If[Changes === True && !NoAnim,AppendTo[display,DrawBoardH[Board]]];
			]
		];
		If[Events === Lost,If[!NoAnim, AppendTo[display,DrawBoardH[Board]]; Print["Game Over"]]; gameover=1; Break[]];
	];
	If[!NoAnim, Return[ListAnimate[display,AnimationRunning->False,Deployed->True]],If[gameover == 1,Return["Lost"],Return["Win"]] ]
	
];

GetSquaresHidden[r_,c_]:=Block[{i,j,unMinesquares,Markmines},
	If[r == 8 && c == 8, unMinesquares = r*c - 10; Markmines = 10,
		If[r == 16 && c == 16, unMinesquares = r*c - 40; Markmines = 40,
			If[r==16 && c == 30, unMinesquares = r*c - 99; Markmines = 99, unMinesquares = r*c - 40; Markmines = 40]]];
	{unMinesquares,Markmines}
];

ChooseRandom[board_,r_,c_]:=Block[{Col,Ren,flag = True},
	While[flag,
		Ren = RandomInteger[{1,r}];
		Col = RandomInteger[{1,c}];
		If[NHidden[board[[Ren,Col]]] && !NMine[board[[Ren,Col]]], flag = False];
	];
	{Ren,Col}
];

(*Functions that check the limit of the board*)
CornerLU[r_,c_,d_]:=If[r-1 >= 1 && c-1>= 1,True,False];
CornerLD[r_,c_,d_]:=If[(r+1 <= d[[1]]) && (c-1>= 1) ,True,False];
CornerRU[r_,c_,d_]:=If[(r-1 >= 1) && (c+1 <= d[[2]]) ,True,False];
CornerRD[r_,c_,d_]:=If[(r+1 <=  d[[1]]) && (c+1 <= d[[2]]) ,True,False];
CheckR[r_,c_,d_]:= If[c+1 <=  d[[2]] ,True,False];
CheckL[r_,c_,d_]:= If[c-1 >= 1,True,False];
CheckU[r_,c_,d_]:= If[r-1 >= 1,True,False];
CheckD[r_,c_,d_]:= If[r+1 <=  d[[1]],True,False];
