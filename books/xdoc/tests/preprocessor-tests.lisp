; XDOC Documentation System for ACL2
; Copyright (C) 2009-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "../preprocess")

(defmacro test (str expect)
  `(make-event
    (b* (((mv acc state)
          (preprocess-main ',str 'context nil nil (pkg-witness "XDOC") state
                           nil))
         (result (str::printtree->str acc))
         (- (cw "~s0 --> ~s1~%" ',str result))
         ((when (equal result ',expect))
          (value '(value-triple :success))))
      (er hard? 'test "Test failed, expected ~s0" ',expect)
      (value '(value-triple :fail)))))

(test "|@('')|"   "|<v></v>|")
(test "|@(''')|"  "|<v>'</v>|")
(test "|@(')')|"  "|<v>)</v>|")
(test "|@('a')|"  "|<v>a</v>|")
(test "|@('ab')|" "|<v>ab</v>|")

(test "foo |@('')| bar"   "foo |<v></v>| bar")
(test "foo |@(''')| bar"  "foo |<v>'</v>| bar")
(test "foo |@(')')| bar"  "foo |<v>)</v>| bar")
(test "foo |@('a')| bar"  "foo |<v>a</v>| bar")
(test "foo |@('ab')| bar" "foo |<v>ab</v>| bar")

(test "@('')| car"   "<v></v>| car")
(test "@(''')| car"  "<v>'</v>| car")
(test "@(')')| car"  "<v>)</v>| car")
(test "@('a')| car"  "<v>a</v>| car")
(test "@('ac')| car" "<v>ac</v>| car")

(test "|@({})|"   "|<code></code>|")
(test "|@({'})|"  "|<code>'</code>|")
(test "|@({)})|"  "|<code>)</code>|")
(test "|@({a})|"  "|<code>a</code>|")
(test "|@({ab})|" "|<code>ab</code>|")
(test "|@({{})|"  "|<code>{</code>|")
(test "|@({}})|"  "|<code>}</code>|")

(test "foo |@({})| bar"   "foo |<code></code>| bar")
(test "foo |@({'})| bar"  "foo |<code>'</code>| bar")
(test "foo |@({)})| bar"  "foo |<code>)</code>| bar")
(test "foo |@({a})| bar"  "foo |<code>a</code>| bar")
(test "foo |@({ab})| bar" "foo |<code>ab</code>| bar")
(test "foo |@({{})| bar"  "foo |<code>{</code>| bar")
(test "foo |@({}})| bar"  "foo |<code>}</code>| bar")

(test "@({})| car"   "<code></code>| car")
(test "@({'})| car"  "<code>'</code>| car")
(test "@({)})| car"  "<code>)</code>| car")
(test "@({a})| car"  "<code>a</code>| car")
(test "@({ac})| car" "<code>ac</code>| car")
(test "@({{})| car"  "<code>{</code>| car")
(test "@({}})| car"  "<code>}</code>| car")
