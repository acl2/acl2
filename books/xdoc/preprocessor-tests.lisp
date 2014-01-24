; XDOC Documentation System for ACL2
; Copyright (C) 2009-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "preprocess")

(defmacro test (str expect)
  `(make-event
    (b* (((mv acc state)
          (preprocess-main ',str nil nil (pkg-witness "XDOC") state nil))
         (result (str::rchars-to-string acc))
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
