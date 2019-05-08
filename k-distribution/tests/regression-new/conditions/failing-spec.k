module FAILING-SPEC
    imports CONDITIONS
    rule <k> CHECK X ~> CHECK Y => . </k>
         <jumps> 0 => A </jumps>
    requires
    notBool (#rangeSInt(256, X) andBool #rangeSInt(256, X *Int Y))
    ensures A <Int 2
endmodule
