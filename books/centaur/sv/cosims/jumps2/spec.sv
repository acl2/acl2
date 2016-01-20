// SV - Symbolic Vector Hardware Analysis Framework
// Copyright (C) 2014-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Sol Swords <sswords@centtech.com>

module spec (input logic [127:0] in,
	     output [127:0] out);

  typedef logic [3:0] four_t;

   function automatic four_t fn0 (input four_t a, input four_t b);
     // Basic break statement
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (a[i] & ~b[i])
	 break;
       count++;
     end
     return count;
   endfunction

   function automatic four_t fn1 (input four_t a, input four_t b);
     // Basic continue statement
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (a[i] & ~b[i])
	 continue;
       count++;
     end
     return count;
   endfunction

   function automatic four_t fn2 (input four_t a, input four_t b);
     // Continue statement and early return, inside IFs
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (a[i] & ~b[i]) continue;
       else if (a[i]) return 0;
       else count++;
     end
     return count;
   endfunction

   function automatic four_t fn3 (input four_t a, input four_t b);
     // Continue statement and early return, independent IFs
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (a[i] & ~b[i]) continue;
       if (a[i]) return 0;
       count++;
     end
     return count;
   endfunction

   function automatic four_t fn4 (input four_t a, input four_t b);
     // Continue statement and break, inside IFs
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (a[i] & ~b[i]) continue;
       else if (a[i]) break;
       else count++;
     end
     return count;
   endfunction

   function automatic four_t fn5 (input four_t a, input four_t b);
     // Continue statement and break, independent IFs
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (a[i] & ~b[i]) continue;
       if (a[i]) break;
       count++;
     end
     return count;
   endfunction

   function automatic four_t fn6 (input four_t a, input four_t b);
     // Independent continue statements
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (b[i]) begin
	 count++;
	 continue;
       end
       if (a[i]) begin
	 count--;
	 continue;
       end
       count++;
     end
     return count;
   endfunction

   function automatic four_t fn7 (input four_t a, input four_t b);
     // Independent continue statements
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (b[i]) begin
	 count++;
	 continue;
       end
       if (a[i]) begin
	 count--;
	 continue;
       end
       count++;
     end
     return count;
   endfunction

   function automatic four_t fn8 (input four_t a, input four_t b);
     // Just generally nasty
     integer count = 0;
     for(integer i = 0; i < 4;++i) begin
       if (b[i]) begin
	 count++;
	 if (a[i])
	   break;
       end
       if (a[i]) begin
	 count--;
	 if (~b[i])
	   return ~count;
	 continue;
       end
       count++;
     end
     return count;
   endfunction

   four_t a, b;
   assign {b, a} = in;

   assign out = { fn8(a, b), fn7(a, b), fn6(a, b), fn5(a, b), fn4(a, b), fn3(a, b), fn2(a, b), fn1(a, b), fn0(a, b) };
			      
endmodule // spec

