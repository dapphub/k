module PASSING-SPEC
    imports CONDITIONS
    rule <k> CHECK X ~> CHECK Y => . </k>
         <jumps> 0 => A </jumps>
    requires
    notBool (X ==Int 0 andBool X *Int Y ==Int 0)
    ensures A <Int 2
endmodule
