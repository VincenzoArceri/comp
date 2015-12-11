module COMP-SYTNAX

	syntax Ids ::= List{Id, ","}
	
	syntax Decl ::= "var" Exps ";"
				|	"function" Id "(" Ids ")" Block

	syntax Exp ::= Int | Bool | String | Id
				| "(" Exp ")"								[bracket]
				| "++"Exp
				| Exp[Exps]									[strict]
				| "-" Exp 									[strict]
				| "sizeOf" "(" Exp ")"						[strict]
				| "read" "(" ")"
				| Exp "*" Exp 								[strict]
				| Exp "/" Exp 								[strict]
				| Exp "%" Exp 								[strict]
				| Exp "+" Exp 								[strict]
				| Exp "-" Exp 								[strict]
				| Exp "<" Exp 								[strict]
				| Exp "<=" Exp 								[strict]
				| Exp ">" Exp 								[strict]	
				| Exp ">=" Exp 								[strict]	
				| Exp "==" Exp 								[strict]
				| Exp "!=" Exp 								[strict]	
				| "!" Exp 									[strict]
				| Exp "&&" Exp 								[strict]
				| Exp "||" Exp 								[strict]
				| "spawn" Block
				| Exp "=" Exp 								[strict(2)]

	syntax Exps ::= List{Exp, ","}							[strict]

	syntax Block ::= "{" "}" | "{" Stmts"}"

	syntax Stmt ::= Decl | Block
				| Exp ";" 									[strict]
				| "if" "(" Exp ")" Block "else" Block		[avoid, strict(1)]
				| "if" "(" Exp ")" Block					[strict(1)]
				| "while" "(" Exp ")"
endmodule 


module COMP
	import COMP-SYNTAX

endmodule