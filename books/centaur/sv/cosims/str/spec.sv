// String escaping cosim test
// Copyright (C) 2016 Apple, Inc.
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
// Original author: Jared Davis

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   // This is a test to see how stray escaping characters in strings works
   // on commercial tools.

   wire [7:0]
	     a1 = "a", a2 = "\a",
	     b1 = "b", b2 = "\b",
	     c1 = "c", c2 = "\c",
	     d1 = "d", d2 = "\d",
	     e1 = "e", e2 = "\e",
	     f1 = "f", f2 = "\f",
	     g1 = "g", g2 = "\g",
	     h1 = "h", h2 = "\h",
	     i1 = "i", i2 = "\i",
	     j1 = "j", j2 = "\j",
	     k1 = "k", k2 = "\k",
	     l1 = "l", l2 = "\l",
	     m1 = "m", m2 = "\m",
	     n1 = "n", n2 = "\n",
	     o1 = "o", o2 = "\o",
	     p1 = "p", p2 = "\p",
	     q1 = "q", q2 = "\q",
	     r1 = "r", r2 = "\r",
	     s1 = "s", s2 = "\s",
	     t1 = "t", t2 = "\t",
	     u1 = "u", u2 = "\u",
	     v1 = "v", v2 = "\v",
	     w1 = "w", w2 = "\w",
	     // This is actually a parse error in VL because \x should have hex digits after it.
	     //x1 = "x", x2 = "\x",
	     y1 = "y", y2 = "\y",
	     z1 = "z", z2 = "\z",
	     A1 = "A", A2 = "\A",
	     B1 = "B", B2 = "\B",
	     C1 = "C", C2 = "\C",
	     D1 = "D", D2 = "\D",
	     E1 = "E", E2 = "\E",
	     F1 = "F", F2 = "\F",
	     G1 = "G", G2 = "\G",
	     H1 = "H", H2 = "\H",
	     I1 = "I", I2 = "\I",
	     J1 = "J", J2 = "\J",
	     K1 = "K", K2 = "\K",
	     L1 = "L", L2 = "\L",
	     M1 = "M", M2 = "\M",
	     N1 = "N", N2 = "\N",
	     O1 = "O", O2 = "\O",
	     P1 = "P", P2 = "\P",
	     Q1 = "Q", Q2 = "\Q",
	     R1 = "R", R2 = "\R",
	     S1 = "S", S2 = "\S",
	     T1 = "T", T2 = "\T",
	     U1 = "U", U2 = "\U",
	     V1 = "V", V2 = "\V",
	     W1 = "W", W2 = "\W",
	     X1 = "X", X2 = "\X",
	     Y1 = "Y", Y2 = "\Y",
	     Z1 = "Z", Z2 = "\Z";

   wire [25:0] lowercase = { 1'b1, // a1 == a2 -- suppress this check because other tools don't implement the standard
			     b1 == b2,
			     c1 == c2,
			     d1 == d2,
			     e1 == e2,
			     1'b1, //f1 == f2  -- suppress this check because other tools don't implement the standard
			     g1 == g2,
			     h1 == h2,
			     i1 == i2,
			     j1 == j2,
			     k1 == k2,
			     l1 == l2,
			     m1 == m2,
			     n1 == n2,
			     o1 == o2,
			     p1 == p2,
			     q1 == q2,
			     r1 == r2,
			     s1 == s2,
			     t1 == t2,
			     u1 == u2,
			     1'b1, //v1 == v2  -- suppress this check because other tools don't implement the standard
			     w1 == w2,
			     1'b1, //x1 == x2  -- suppress this check because other tools don't implement the standard
			     y1 == y2,
			     z1 == z2 };

   wire [25:0] uppercase = { A1 == A2,
			     B1 == B2,
			     C1 == C2,
			     D1 == D2,
			     E1 == E2,
			     F1 == F2,
			     G1 == G2,
			     H1 == H2,
			     I1 == I2,
			     J1 == J2,
			     K1 == K2,
			     L1 == L2,
			     M1 == M2,
			     N1 == N2,
			     O1 == O2,
			     P1 == P2,
			     Q1 == Q2,
			     R1 == R2,
			     S1 == S2,
			     T1 == T2,
			     U1 == U2,
			     V1 == V2,
			     W1 == W2,
			     X1 == X2,
			     Y1 == Y2,
			     Z1 == Z2 };

   wire [7:0]
	     dig0a = "0", dig0b = "\0",
	     dig1a = "1", dig1b = "\1",
	     dig2a = "2", dig2b = "\2",
	     dig3a = "3", dig3b = "\3",
	     dig4a = "4", dig4b = "\4",
	     dig5a = "5", dig5b = "\5",
	     dig6a = "6", dig6b = "\6",
	     dig7a = "7", dig7b = "\7",
	     dig8a = "8", dig8b = "\8",
	     dig9a = "9", dig9b = "\9";

   wire[9:0] digits = { dig0a == dig0b,
			dig1a == dig1b,
			dig2a == dig2b,
			dig3a == dig3b,
			dig4a == dig4b,
			dig5a == dig5b,
			dig6a == dig6b,
			dig7a == dig7b,
			dig8a == dig8b,
			dig9a == dig9b };

   wire [7:0]
	     misc0a = "~", misc0b = "\~",
	     misc1a = "!", misc1b = "\!",
	     misc2a = "@", misc2b = "\@",
	     misc3a = "#", misc3b = "\#",
	     misc4a = "$", misc4b = "\$",
	     misc5a = "%", misc5b = "\%",
	     misc6a = "^", misc6b = "\^",
	     misc7a = "&", misc7b = "\&",
	     misc8a = "*", misc8b = "\*",
	     misc9a = "(", misc9b = "\(",
	     misc10a = ")", misc10b = "\)",
	     misc11a = "_", misc11b = "\_",
	     misc12a = "-", misc12b = "\-",
	     misc13a = "+", misc13b = "\+",
	     misc14a = "=", misc14b = "\=",
	     misc15a = "[", misc15b = "\[",
	     misc16a = "]", misc16b = "\]",
	     misc17a = "{", misc17b = "\{",
	     misc18a = "}", misc18b = "\}",
	     misc19a = "|", misc19b = "\|",
	     misc20a = ";", misc20b = "\;",
	     misc21a = ":", misc21b = "\:",
	     misc22a = "<", misc22b = "\<",
	     misc23a = ">", misc23b = "\>",
	     misc24a = ",", misc24b = "\,",
	     misc25a = ".", misc25b = "\.",
	     misc26a = "?", misc26b = "\?",
	     misc27a = "/", misc27b = "\/",
	     misc28a = "`", misc28b = "\`",
	     misc29a = " ", misc29b = "\ ";

   wire [29:0] misc = { misc29a == misc29b,
			misc28a == misc28b,
			misc27a == misc27b,
			misc26a == misc26b,
			misc25a == misc25b,
			misc24a == misc24b,
			misc23a == misc23b,
			misc22a == misc22b,
			misc21a == misc21b,
			misc20a == misc20b,
			misc19a == misc19b,
			misc18a == misc18b,
			misc17a == misc17b,
			misc16a == misc16b,
			misc15a == misc15b,
			misc14a == misc14b,
			misc13a == misc13b,
			misc12a == misc12b,
			misc11a == misc11b,
			misc10a == misc10b,
			misc9a == misc9b,
			misc8a == misc8b,
			misc7a == misc7b,
			misc6a == misc6b,
			misc5a == misc5b,
			misc4a == misc4b,
			misc3a == misc3b,
			misc2a == misc2b,
			misc1a == misc1b,
  		        misc0a == misc0b };

   assign out = { uppercase, 2'bxx, lowercase, 2'bxx, digits, 2'bxx, misc };

/*
   initial begin
      #10
	$display("a1 = %s, a2 = %s, a1 == a2 = %b", a1, a2, a1 == a2);
	$display("b1 = %s, b2 = %s, b1 == b2 = %b", b1, b2, b1 == b2);
	$display("c1 = %s, c2 = %s, c1 == c2 = %b", c1, c2, c1 == c2);
	$display("d1 = %s, d2 = %s, d1 == d2 = %b", d1, d2, d1 == d2);
	$display("e1 = %s, e2 = %s, e1 == e2 = %b", e1, e2, e1 == e2);
	$display("f1 = %s, f2 = %s, f1 == f2 = %b", f1, f2, f1 == f2);
	$display("g1 = %s, g2 = %s, g1 == g2 = %b", g1, g2, g1 == g2);
	$display("h1 = %s, h2 = %s, h1 == h2 = %b", h1, h2, h1 == h2);
	$display("i1 = %s, i2 = %s, i1 == i2 = %b", i1, i2, i1 == i2);
	$display("j1 = %s, j2 = %s, j1 == j2 = %b", j1, j2, j1 == j2);
	$display("k1 = %s, k2 = %s, k1 == k2 = %b", k1, k2, k1 == k2);
	$display("l1 = %s, l2 = %s, l1 == l2 = %b", l1, l2, l1 == l2);
	$display("m1 = %s, m2 = %s, m1 == m2 = %b", m1, m2, m1 == m2);
	$display("n1 = %s, n2 = %s, n1 == n2 = %b", n1, n2, n1 == n2);
	$display("o1 = %s, o2 = %s, o1 == o2 = %b", o1, o2, o1 == o2);
	$display("p1 = %s, p2 = %s, p1 == p2 = %b", p1, p2, p1 == p2);
	$display("q1 = %s, q2 = %s, q1 == q2 = %b", q1, q2, q1 == q2);
	$display("r1 = %s, r2 = %s, r1 == r2 = %b", r1, r2, r1 == r2);
	$display("s1 = %s, s2 = %s, s1 == s2 = %b", s1, s2, s1 == s2);
	$display("t1 = %s, t2 = %s, t1 == t2 = %b", t1, t2, t1 == t2);
	$display("u1 = %s, u2 = %s, u1 == u2 = %b", u1, u2, u1 == u2);
	$display("v1 = %s, v2 = %s, v1 == v2 = %b", v1, v2, v1 == v2);
	$display("w1 = %s, w2 = %s, w1 == w2 = %b", w1, w2, w1 == w2);
      //$display("x1 = %s, x2 = %s, x1 == x2 = %b", x1, x2, x1 == x2);
	$display("y1 = %s, y2 = %s, y1 == y2 = %b", y1, y2, y1 == y2);
	$display("z1 = %s, z2 = %s, z1 == z2 = %b", z1, z2, z1 == z2);

	$display("A1 = %S, A2 = %S, A1 == A2 = %b", A1, A2, A1 == A2);
	$display("B1 = %S, B2 = %S, B1 == B2 = %b", B1, B2, B1 == B2);
	$display("C1 = %S, C2 = %S, C1 == C2 = %b", C1, C2, C1 == C2);
	$display("D1 = %S, D2 = %S, D1 == D2 = %b", D1, D2, D1 == D2);
	$display("E1 = %S, E2 = %S, E1 == E2 = %b", E1, E2, E1 == E2);
	$display("F1 = %S, F2 = %S, F1 == F2 = %b", F1, F2, F1 == F2);
	$display("G1 = %S, G2 = %S, G1 == G2 = %b", G1, G2, G1 == G2);
	$display("H1 = %S, H2 = %S, H1 == H2 = %b", H1, H2, H1 == H2);
	$display("I1 = %S, I2 = %S, I1 == I2 = %b", I1, I2, I1 == I2);
	$display("J1 = %S, J2 = %S, J1 == J2 = %b", J1, J2, J1 == J2);
	$display("K1 = %S, K2 = %S, K1 == K2 = %b", K1, K2, K1 == K2);
	$display("L1 = %S, L2 = %S, L1 == L2 = %b", L1, L2, L1 == L2);
	$display("M1 = %S, M2 = %S, M1 == M2 = %b", M1, M2, M1 == M2);
	$display("N1 = %S, N2 = %S, N1 == N2 = %b", N1, N2, N1 == N2);
	$display("O1 = %S, O2 = %S, O1 == O2 = %b", O1, O2, O1 == O2);
	$display("P1 = %S, P2 = %S, P1 == P2 = %b", P1, P2, P1 == P2);
	$display("Q1 = %S, Q2 = %S, Q1 == Q2 = %b", Q1, Q2, Q1 == Q2);
	$display("R1 = %S, R2 = %S, R1 == R2 = %b", R1, R2, R1 == R2);
	$display("S1 = %S, S2 = %S, S1 == S2 = %b", S1, S2, S1 == S2);
	$display("T1 = %S, T2 = %S, T1 == T2 = %b", T1, T2, T1 == T2);
	$display("U1 = %S, U2 = %S, U1 == U2 = %b", U1, U2, U1 == U2);
	$display("V1 = %S, V2 = %S, V1 == V2 = %b", V1, V2, V1 == V2);
	$display("W1 = %S, W2 = %S, W1 == W2 = %b", W1, W2, W1 == W2);
	$display("X1 = %S, X2 = %S, X1 == X2 = %b", X1, X2, X1 == X2);
	$display("Y1 = %S, Y2 = %S, Y1 == Y2 = %b", Y1, Y2, Y1 == Y2);
	$display("Z1 = %S, Z2 = %S, Z1 == Z2 = %b", Z1, Z2, Z1 == Z2);

        $display("dig0a = %S, dig0b = %S, dig0a == dig0b = %b", dig0a, dig0b, dig0a == dig0b);
        $display("dig1a = %S, dig1b = %S, dig1a == dig1b = %b", dig1a, dig1b, dig1a == dig1b);
        $display("dig2a = %S, dig2b = %S, dig2a == dig2b = %b", dig2a, dig2b, dig2a == dig2b);
        $display("dig3a = %S, dig3b = %S, dig3a == dig3b = %b", dig3a, dig3b, dig3a == dig3b);
        $display("dig4a = %S, dig4b = %S, dig4a == dig4b = %b", dig4a, dig4b, dig4a == dig4b);
        $display("dig5a = %S, dig5b = %S, dig5a == dig5b = %b", dig5a, dig5b, dig5a == dig5b);
        $display("dig6a = %S, dig6b = %S, dig6a == dig6b = %b", dig6a, dig6b, dig6a == dig6b);
        $display("dig7a = %S, dig7b = %S, dig7a == dig7b = %b", dig7a, dig7b, dig7a == dig7b);
        $display("dig8a = %S, dig8b = %S, dig8a == dig8b = %b", dig8a, dig8b, dig8a == dig8b);
        $display("dig9a = %S, dig9b = %S, dig9a == dig9b = %b", dig9a, dig9b, dig9a == dig9b);

        $display("misc0a = %S, misc0b = %S, misc0a == misc0b = %b", misc0a, misc0b, misc0a == misc0b);
        $display("misc1a = %S, misc1b = %S, misc1a == misc1b = %b", misc1a, misc1b, misc1a == misc1b);
        $display("misc2a = %S, misc2b = %S, misc2a == misc2b = %b", misc2a, misc2b, misc2a == misc2b);
        $display("misc3a = %S, misc3b = %S, misc3a == misc3b = %b", misc3a, misc3b, misc3a == misc3b);
        $display("misc4a = %S, misc4b = %S, misc4a == misc4b = %b", misc4a, misc4b, misc4a == misc4b);
        $display("misc5a = %S, misc5b = %S, misc5a == misc5b = %b", misc5a, misc5b, misc5a == misc5b);
        $display("misc6a = %S, misc6b = %S, misc6a == misc6b = %b", misc6a, misc6b, misc6a == misc6b);
        $display("misc7a = %S, misc7b = %S, misc7a == misc7b = %b", misc7a, misc7b, misc7a == misc7b);
        $display("misc8a = %S, misc8b = %S, misc8a == misc8b = %b", misc8a, misc8b, misc8a == misc8b);
        $display("misc9a = %S, misc9b = %S, misc9a == misc9b = %b", misc9a, misc9b, misc9a == misc9b);

        $display("misc10a = %S, misc10b = %S, misc10a == misc10b = %b", misc10a, misc10b, misc10a == misc10b);
        $display("misc11a = %S, misc11b = %S, misc11a == misc11b = %b", misc11a, misc11b, misc11a == misc11b);
        $display("misc12a = %S, misc12b = %S, misc12a == misc12b = %b", misc12a, misc12b, misc12a == misc12b);
        $display("misc13a = %S, misc13b = %S, misc13a == misc13b = %b", misc13a, misc13b, misc13a == misc13b);
        $display("misc14a = %S, misc14b = %S, misc14a == misc14b = %b", misc14a, misc14b, misc14a == misc14b);
        $display("misc15a = %S, misc15b = %S, misc15a == misc15b = %b", misc15a, misc15b, misc15a == misc15b);
        $display("misc16a = %S, misc16b = %S, misc16a == misc16b = %b", misc16a, misc16b, misc16a == misc16b);
        $display("misc17a = %S, misc17b = %S, misc17a == misc17b = %b", misc17a, misc17b, misc17a == misc17b);
        $display("misc18a = %S, misc18b = %S, misc18a == misc18b = %b", misc18a, misc18b, misc18a == misc18b);
        $display("misc19a = %S, misc19b = %S, misc19a == misc19b = %b", misc19a, misc19b, misc19a == misc19b);

        $display("misc20a = %S, misc20b = %S, misc20a == misc20b = %b", misc20a, misc20b, misc20a == misc20b);
        $display("misc21a = %S, misc21b = %S, misc21a == misc21b = %b", misc21a, misc21b, misc21a == misc21b);
        $display("misc22a = %S, misc22b = %S, misc22a == misc22b = %b", misc22a, misc22b, misc22a == misc22b);
        $display("misc23a = %S, misc23b = %S, misc23a == misc23b = %b", misc23a, misc23b, misc23a == misc23b);
        $display("misc24a = %S, misc24b = %S, misc24a == misc24b = %b", misc24a, misc24b, misc24a == misc24b);
        $display("misc25a = %S, misc25b = %S, misc25a == misc25b = %b", misc25a, misc25b, misc25a == misc25b);
        $display("misc26a = %S, misc26b = %S, misc26a == misc26b = %b", misc26a, misc26b, misc26a == misc26b);
        $display("misc27a = %S, misc27b = %S, misc27a == misc27b = %b", misc27a, misc27b, misc27a == misc27b);
        $display("misc28a = %S, misc28b = %S, misc28a == misc28b = %b", misc28a, misc28b, misc28a == misc28b);
        $display("misc29a = %S, misc29b = %S, misc29a == misc29b = %b", misc29a, misc29b, misc29a == misc29b);

   end
 */


endmodule

