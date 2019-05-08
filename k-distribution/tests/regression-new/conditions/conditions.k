// Copyright (c) 2019 Martin. All Rights Reserved.

module CONDITIONS-SYNTAX
    imports INT
    imports K-EQUAL

    syntax Pgm ::= Instr
    syntax Instr ::= "CHECK" Int
                  | Instr "~>" Instr

    syntax IntList ::= List{Int, ","}

    syntax Bool ::= #rangeSInt ( Int , Int )

    syntax Int ::=  "minSInt256"
                 |  "maxSInt256"

endmodule

module CONDITIONS
    imports CONDITIONS-SYNTAX

    configuration
      <k> $PGM:Pgm </k>
      <jumps> 0 </jumps>

    rule <k> CHECK COND => . ... </k>
         <jumps> A => A +Int 1 </jumps>
      requires COND ==Int 0

    rule <k> CHECK COND => . ... </k>
      requires COND =/=Int 0

    rule _ *Int 0 => 0
    rule 0 *Int _ => 0 
    
    rule #rangeSInt(256, X) => true
         requires X ==Int 0

    rule #rangeSInt(256, X ) => minSInt256 <=Int X andBool X <=Int maxSInt256

    rule minSInt256      => -57896044618658097711785492504343953926634992332820282019728792003956564819968  [macro]  /*  -2^255      */
    rule maxSInt256      =>  57896044618658097711785492504343953926634992332820282019728792003956564819967  [macro]  /*   2^255 - 1  */


endmodule
