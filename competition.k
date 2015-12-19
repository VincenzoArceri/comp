/*
  Sintassi di Competition
*/
module COMPETITION-SYN
	
	syntax Decl ::= "var" Ids ";" | "semaphore" Ids ";"

  syntax Exp ::= Int | Bool | Id | String
               | "(" Exp ")"             [bracket]				    
               > "-" Exp                 [strict]				
               | "read" "(" ")"									
               > left:											
                 Exp "*" Exp             [strict, left]			
               | Exp "/" Exp             [strict, left]		
               | Exp "%" Exp             [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "not" Exp               [strict]
               > left:
                 Exp "and" Exp           [strict(1), left]
               | Exp "or" Exp            [strict(1), left]
               > "spawn" Block							

  syntax Ids  ::= List{Id,","}
  syntax Exps ::= List{Exp,","}          [strict]  // automatically hybrid now
  syntax Ints ::= List{Int, ","}
  syntax Strings ::= List{String, ","}

  syntax Block ::= "{" "}"								
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                                         [strict]
                | Id "=" Exp ";"             			                [strict(2)]
                | "if" "(" Exp ")" Block "else" Block             [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
                | "return" Exp ";"                                [strict]
                | "print" "(" Exp ")" ";"              	          [strict]
                | "lock" Id ";"                       	          
                | "unlock" Id ";"
                
  syntax Stmts ::= Stmt
                 | Stmts Stmts                                    [right]

  rule if (E) S => if (E) S else {}                               [macro]

endmodule

/*
  Semantica di Competition
*/
module COMPETITION
	imports COMPETITION-SYN
	imports SUBSTITUTION
	imports BUILTIN-SYNTAX-HOOKS

  syntax Val ::= Int | Bool | String
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> $PGM:Stmts </k>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Set </holds>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>

                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  
                  <streams>
                 	<in color="magenta" stream="stdin"> .List </in>
                  	<out color="brown" stream="stdout"> .List </out>
                  </streams>

                  <busy> .Map </busy>
                </T>

  rule  not T:Bool => notBool(T)
  rule  true and E => E
  rule  false and _ => false
  rule  true  or _ => true
  rule  false or E => E

  rule  I1:Int + I2:Int => I1 +Int I2
  rule  I1:Int - I2:Int => I1 -Int I2
  rule  I1:Int * I2:Int => I1 *Int I2
  rule  I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0
  rule  I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0
  rule  - I:Int => 0 -Int I
  rule  I1:Int < I2:Int => I1 <Int I2
  rule  I1:Int <= I2:Int => I1 <=Int I2
  rule  I1:Int > I2:Int => I1 >Int I2
  rule  I1:Int >= I2:Int => I1 >=Int I2

  rule  V1:Val == V2:Val => V1 ==K V2
  rule  V1:Val != V2:Val => V1 =/=K V2


  rule  if (true) S else _ => S
  rule  if (false) _ else S => S

  rule  while (E) S => if (E) {S while(E)S}  	   [structural]

  rule 	<k> read() => I ...</k> 
  		  <in> ListItem(I:Int) => .List ...</in>   [read]

  rule 	<k> print(V:Val) ; => V ;... </k> 
  		  <out>... .List => ListItem(V) </out> 	   [print]

  rule  _:Val; => .K

  rule  <k> lock P:Id; => 0 ; ... </k>
        <holds> Holds:Set => Holds SetItem(P) </holds>
  		  <busy> ... P |-> (L:Int => L -Int 1) </busy>  when ((L =/=Int 0) andBool notBool(P in Holds))

  rule  <k> unlock P:Id ; => 1 ; ... </k>
        <holds> Holds:Set => Holds -Set SetItem(P) </holds>
        <busy> ... P |-> (L:Int => L:Int +Int 1)... </busy> when ((P in Holds) andBool (L ==Int 0)) 


  rule  <k> X:Id => I:Int ...</k>
        <env>... X |-> L:Int ...</env>
        <store>... L |-> I:Int ...</store>  [lookup]

  rule  <k> X:Id => I:Int ...</k>
        <busy>... X |-> I ...</busy>

  rule  <thread>...
          <k> spawn S:Block => T:Int ...</k>
          <env> Env:Map </env>
       ...</thread>
       (. => <thread>...
               <k> S </k>
               <env> Env:Map </env>
               <id> T </id>
         ... </thread>) when fresh(T:Int)

  rule  <k> var (X:Id,X1:Ids => X1) ; ... </k>
		    <env> Rho:Map => Rho[L:Int/X] </env>
	     	<store> Delta:Map => Delta[0 /L] </store> when fresh(L:Int)  [assignment]

  rule  var .Ids ; => .K      [structural]

  rule  <k> semaphore (X:Id,X1:Ids => X1) ; ... </k>
        <busy> Mutex:Map => Mutex[1/X] </busy>
  rule semaphore .Ids ; => .K

	rule  <k> X:Id = I:Int ; => I; ... </k>
		    <env> ... X |-> N:Int ... </env>
		    <store> ... N |-> (_ => I) </store> 

	rule  V:Val ; => .K				[structural]

  rule  S1:Stmts S2:Stmts => S1 ~> S2  [structural]


  rule  { S:Stmts } => S
  rule { } => .K 

endmodule