module TEST-SYNTAX

  syntax Citire ::= Int Int Int
				> Citire Citire	[right]	
endmodule

module TEST
  imports TEST-SYNTAX
  
  syntax Function ::= Bool
				| "returnAdevar"
				| "returnFals"
				| "PRINT" Exp													[strict]
				| "Declare" Exp Exp  											[strict]
				| "Modify" Exp Exp												[strict]
				| "Init" Exp
				| "Restore"
				| "BKT" Exp Exp													[strict]
				| "notUsedInBox" Exp Exp Exp Exp Exp							[strict]
				| "notUsedInLine" Exp Exp Exp									[strict]
				| "notUsedInRow" Exp Exp Exp 									[strict]
				| "isValid" Exp Exp Exp											[strict]
				| "tryValues" Exp Exp Exp										[strict]
				| "SET"
				| "Solutie" Exp													[strict]
				|	"AFISARE"	Exp	[strict]
  
  syntax Exp ::= Int | Bool | String | Id 
				| "a[" Exp "]"		 	 										[strict]
				| "Compare" Exp Exp												[strict]
				| "(" Exp ")"            										[bracket]
               > "-" Exp                 										[strict]
               > left:
			     Exp "*" Exp             										[strict, left]
               | Exp "/" Exp             										[strict, left]
               | Exp "%" Exp             										[strict, left]
               > left:
                 Exp "+" Exp             										[strict, left]
               | Exp "-" Exp            										[strict, left]
			   > Exp "=" Exp             										[strict(2), right]
			   > non-assoc:	
                 Exp "<" Exp             										[strict, non-assoc]
               | Exp "<=" Exp            										[strict, non-assoc]
               | Exp ">" Exp            										[strict, non-assoc]
               | Exp ">=" Exp            										[strict, non-assoc]
               | Exp "==" Exp          	 										[strict, non-assoc]
               | Exp "!=" Exp            										[strict, non-assoc]
               > "!" Exp                 										[strict]
               > left:
                 Exp "&&" Exp            										[strict(1), left]
               | Exp "||" Exp            										[strict(1), left]							
			
  syntax Block ::= "{""}"
                | "{" Stmts "}"

  syntax Stmt ::= Block
				| Function
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
				| "if" "(" Function ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Function ")" Block
				
  syntax Stmts ::= Stmt
                 | Stmts Stmts                          			[right]

  syntax Val ::= Int | Bool | String
				| array(Int,Int)
  
  syntax Exp ::= Val
  
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  
  rule V1:Exp == V2:Exp => V1 ==K V2
  rule V1:Exp != V2:Exp => V1 =/=K V2
  
  rule ! T => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E
			   
  rule I1 + I2 => I1 +Int I2
  rule I1 - I2 => I1 -Int I2
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 requires I2 =/=K 0
  rule I1 % I2 => I1 %Int I2 requires I2 =/=K 0
  rule - I => 0 -Int I
  
  rule if (true) {S} else _ => S
  rule if (false) _ else {S} => S
  rule if (E:Exp) S => if (E) S else {{}}                                 [macro]
  rule if (E:Function) S => if (E) S else {{}}                            [macro]
  rule {} => .		
  syntax KResult ::= Val
  
				
  configuration <T>
					<k> $PGM:Citire </k>
					<queue> .List </queue>
					<store> .Map </store>
					<out stream="stdout"> .List </out>
					<nextLoc> 0 </nextLoc>
					<vectorcreat> 0 </vectorcreat>
					<gasit> 0 </gasit>
			</T>

  rule S1:Stmts S2:Stmts => S1 ~> S2  [structural]
  rule N1:Citire N2:Citire => N1 ~> N2  [structural]
  
  // Modifica valoarea elementului la pozitia L
  rule <k> Modify L:Exp V:Exp => . ...</k>
       <store>... L |-> (_ => V) ...</store>
	   
  // Initializarea elementelor si a indexului
  rule <k> Declare L:Exp V:Exp => . ...</k>
       <store>... L |-> (_ => V) ...</store>
	   <nextLoc> N => N +Int 1 </nextLoc>
	   
  // Creearea vectorului initial
  rule <k> Init N:Int=> . ...</k>
       <store>... .Map => L |-> array(L +Int 1, N)
                          (L +Int 1) ... (L +Int N) |-> -1 ...</store>
       <nextLoc> L => L +Int 1 +Int N </nextLoc>

  // Returneaza valoarea de la indexul L din vector
  rule <k> (a[L:Exp] =>V) ...</k>
       <store>... L |-> V:Val ...</store>

  // Reinitializarea nextLoc pentru citirea valorilor
  rule <k> (Restore => .) ... </k>
  <nextLoc> L => L -Int 82 </nextLoc>
  <vectorcreat> Ok => 1 </vectorcreat>
	   
  rule <k> (returnAdevar => true ) ... </k>
  
  rule <k> (returnFals => false ) ... </k>
  
  rule <k> (Compare A:Exp B:Exp => if(A==B) {returnAdevar} else {returnFals}) ... </k>
 
  
  
  
  
  
  //FUNCTII PRINCIPALE
  
  
  // Read the input
  rule <k> (V1:Int V2:Int V3:Int => if(Ok==0) {Init 81 Restore} Declare (L+1) V1 Declare (L+2) V2 Declare (L+3) V3 if(L==78) {BKT 1 1}) ... </k>
  <nextLoc> L </nextLoc>
  <vectorcreat> Ok </vectorcreat>
  <gasit> Sudoku </gasit>
  
  //verifica o bucata 3x3
  rule <k> (notUsedInBox I:Exp J:Exp V:Exp C1:Exp C2:Exp => if(C1==4) {returnAdevar} else { if(C2==4) { notUsedInBox I J V C1+1 1 } else { if(Compare a[(((I+C1-1)*9)+J+C2)] V ) {returnFals} else { notUsedInBox I J V C1 C2+1 } } } ) ... </k>
  
  //verifica o linie sa nu aiba valoarea V
  rule <k> (notUsedInLine L:Exp C:Exp V:Exp => if(Compare C 10) {returnAdevar} else {if(Compare a[(((L-1)*9)+C)] V ) {returnFals} else { notUsedInLine L C+1 V } } ) ... </k>
  
  //verifica o coloana sa nu aiba valoarea V
  rule <k> (notUsedInRow L:Exp C:Exp V:Exp => if(Compare L 10) {returnAdevar} else {if(Compare a[(((L-1)*9)+C)] V ) {returnFals} else { notUsedInRow L+1 C V } } ) ... </k>
  
  //Verifica daca toate liniile au fost completate
  rule <k> (Solutie L:Exp => if(L==10){returnAdevar} else {if(notUsedInLine L 1 0) {Solutie L+1} else {returnFals} }  ) ... </k>
  
  //am gasit rezolvarea
  rule <k> (SET => .) ... </k>
  <gasit> Sudoku => 1 </gasit>
  
  //Verifica daca poate pune numarul V la coord a[I][J]
  rule <k> (isValid I:Exp J:Exp V:Exp => if(notUsedInRow 1 J V) { if(notUsedInLine I 1 V ) { if(notUsedInBox ((I-1) - ((I-1)%3)) ((J-1) - ((J-1)%3)) V 1 1) {returnAdevar} else {returnFals} } else {returnFals} } else {returnFals} ) ... </k>
  
  //incearca valori pt a[i][j]
  rule <k> (tryValues I:Exp J:Exp V:Exp =>if(Compare V 10) {{}} else {if(isValid I J V) {Modify (((I-1)*9)+J) V  BKT I J+1  Modify (((I-1)*9)+J) 0} tryValues I J V+1} ) ... </k>
  
  //BKT
  rule <k> (BKT I:Exp J:Exp =>PRINT "SUNTEM PE POZITIA " PRINT I PRINT " " PRINT J PRINT "\n" if(Compare Sudoku 0) { if(Solutie 1) {SET AFISARE 1} else {if(Compare J 10) {BKT I+1 1} else {if(Compare a[(((I-1)*9)+J)] 0) {tryValues I J 1} else {BKT I J+1}   }  }   } ) ... </k>
  <gasit> Sudoku </gasit>
  
  
  rule <k> (AFISARE N:Exp =>if(1==(N%9)){PRINT "\n"}PRINT a[N] PRINT " " if(N<81) {AFISARE N+1}  ) ... </k>
  
  
  
  // Initializarea unei secvente cu aceeasi valoare
   syntax Map ::= Int "..." Int "|->" K
    [function, latex({#1}\ldots{#2}\mapsto{#3})]
  rule N...M |-> _ => .Map  requires N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  requires N <=Int M
  
  syntax Printable ::= Int | String
  syntax Exp ::= Printable
  // Print
  rule <k> (PRINT V:Printable => .) ...</k>
       <out>...(.List => ListItem(V)) </out>


endmodule








