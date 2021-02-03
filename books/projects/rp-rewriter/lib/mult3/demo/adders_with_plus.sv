// Note: The license below is based on the template at:
// http://opensource.org/licenses/BSD-3-Clause
// Copyright (C) 2020 Regents of the University of Texas
// All rights reserved.

// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:

// o Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.

// o Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the distribution.

// o Neither the name of the copyright holders nor the names of its
//   contributors may be used to endorse or promote products derived
//   from this software without specific prior written permission.

// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

// Original Author(s):
// Mertcan Temel         <mert@utexas.edu>



// Redefined     adder      modules     with     "+"      operator     from
// DT_SB4_HC_64_64_multgen.sv and integrated_multipliers.sv.  In demo 3, we
// show how defsvtv (flattened designs) can be used for our method. This is
// done  by  overwritting  the  adder  modules with  the  modules  in  this
// file. Then our  multiplier verification tool will be able  to detect the
// adder modules in the candidate  multiplier design even though the design
// is  flattened.  This  is because  SVEX representation  has a  designated
// function for "+" operator.

module ha (
        input logic a,
        input logic b,
        output logic s,
        output logic c);
    // this extra  zero can make a  lot of difference because  it turns the
    //  pattern  (the one  recognized  by  the  rewriter)  into that  of  a
    // full-adder. This prevents a very weird problem from occuring. 
    assign {c,s} = a + b + 0;
endmodule // ha

module fa (
        input logic x, y, z,
        output logic s, c);
    assign {c,s} = x + y + z;
endmodule // fa


module HC_128 ( 
        input logic [127:0] IN1,
        input logic [127:0] IN2,
        output logic [128:0] OUT);
   assign OUT = IN1 + IN2;
   
endmodule // HC_128


module LF_131 ( 
        input logic [130:0] IN1,
        input logic [130:0] IN2,
        output logic [131:0] OUT);
   assign OUT = IN1 + IN2;
endmodule // LF_131
