// VL Verilog Toolkit
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

function my_or (logic [3:0] a) ;
  return |a;
endfunction

// export "DPI" task my_or;   -- VCS rejects this since my_or is a function instead of a task

export "DPI" function my_or;
export "DPI" function my_or; // VCS warns about the duplicate export

// VCS rejects this, says my_or was previously declared as a function:
// import "DPI" function my_or;

// BOZO VCS accepts these, but they don't seem OK per the grammar: the
// data_type_or_void is required in a function prototype.
// import "DPI" function my_and1 (logic [3:0] a);
// import "DPI" pure function my_and2 (logic [3:0] a);
// import "DPI" context function my_and3 (logic [3:0] a);

import "DPI" function logic my_and1 (logic [3:0] a);
import "DPI-C" pure function logic my_and2 (logic [3:0] a);
import "DPI" context function logic my_and3 (logic [3:0] a);

import "DPI" task my_and4 (logic [3:0] a);

// BOZO VCS accepts this, but it doesn't seem OK per the grammar: the
// only allowed dpi_task_import_property is context, not pure.
// import "DPI" pure task my_and5 (logic [3:0] a);

import "DPI-C" context task my_and6 (logic [3:0] a);

// VCS warns that this is the same name used for the earlier declaration but
// doesn't cause an error.
import "DPI" function shortint my_and5 (logic [3:0] a, logic [3:0] b);

// VCS warns that this is the same name used for the earlier declaration but
// doesn't cause an error.
import "DPI-C" function int my_and5 (logic [3:0] a, logic [3:0] b);

export "DPI" function my_or;

module top ;

  reg [3:0] w1;
  wire 	     w2;
  assign w2 = my_or(w1);

  wire 	     w3 = my_and1(w1);

/*
  initial begin
    w1 = 2;
    #10
    $display("w2 = %b, w3 = %b", w2, w3);
  end
*/
endmodule
