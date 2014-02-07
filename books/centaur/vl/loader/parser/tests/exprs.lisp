; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "base")
(include-book "../expressions")

; BOZO I'd like to run these with set-guard-checking :all, but that's not
; embeddable and it seems like I can't even fake it with a make-event.

(defmacro test-parse-expr (&key input (successp 't) expect remainder)
  `(with-output
     :off summary
     (assert! (mv-let (erp val tokens warnings)
                (vl-parse-expression :tokens (make-test-tokens ,input)
                                     :warnings nil
                                     :config *vl-default-loadconfig*)
                (if ,successp
                    (and (prog2$ (cw "Erp: ~x0.~%" erp)
                                 (not erp))
                         (prog2$ (cw "Val: ~x0.~%" val)
                                 (vl-expr-p val))
                         (prog2$ (cw "Pretty: ~x0.~%" (vl-pretty-expr val))
                                 (equal (vl-pretty-expr val) ',expect))
                         (prog2$ (cw "Tokens: ~x0.~%" tokens)
                                 (equal tokens ,remainder))
                         (prog2$ (cw "Warnings: ~x0.~%" warnings)
                                 (equal warnings nil)))
                  ;; Otherwise, we expect it to fail.
                  (prog2$ (cw "Erp: ~x0.~%" erp)
                          erp))))))

(test-parse-expr :input ")"
                 :successp nil)

(test-parse-expr :input "1"
                 :expect 1)

(test-parse-expr :input "3.4"
                 :expect (real "3.4"))

(test-parse-expr :input "\"hello, world\""
                 :expect (str "hello, world"))



(test-parse-expr :input "(3.4)"
                 :expect (real "3.4"))

(test-parse-expr :input "(1:2:3)"
                 :expect (:vl-mintypmax ("VL_EXPLICIT_PARENS") 1 2 3))

(test-parse-expr :input "( 1 : 2 : 3 )"
                 :expect (:vl-mintypmax ("VL_EXPLICIT_PARENS") 1 2 3))

(test-parse-expr :input "( 3 : 4 )"
                 :successp nil)

(test-parse-expr :input "( 3 : 4 : )"
                 :successp nil)



(test-parse-expr :input "foo"
                 :expect (id "foo"))

(test-parse-expr :input "foo[3]"
                 :expect (:vl-bitselect nil (id "foo") 3))

(test-parse-expr :input "foo[1:7]"
                 :expect (:vl-partselect-colon nil (id "foo") 1 7))

(test-parse-expr :input "foo[3][4][5][1 +: 2]"
                 :expect (:vl-partselect-pluscolon nil
                                                   (:vl-bitselect nil
                                                                  (:vl-bitselect nil
                                                                                 (:vl-bitselect nil (id "foo") 3)
                                                                                 4)
                                                                  5)
                                                   1 2))

(test-parse-expr :input "foo[3][1 -: 2]"
                 :expect (:vl-partselect-minuscolon nil
                                                    (:vl-bitselect nil (id "foo") 3)
                                                    1 2))

(test-parse-expr :input "foo.bar"
                 :expect (:vl-hid-dot nil (hid "foo") (hid "bar")))

(test-parse-expr :input "foo.bar.baz"
                 :expect (:vl-hid-dot nil (hid "foo")
                                      (:vl-hid-dot nil (hid "bar") (hid "baz"))))

(test-parse-expr :input "foo[1].bar.baz"
                 :expect (:vl-hid-arraydot nil (hid "foo") 1
                                           (:vl-hid-dot nil (hid "bar") (hid "baz"))))

(test-parse-expr :input "foo[1].bar[2].baz"
                 :expect (:vl-hid-arraydot nil (hid "foo") 1
                                           (:vl-hid-arraydot nil (hid "bar") 2 (hid "baz"))))



(test-parse-expr :input "{}"
                 :successp nil)

(test-parse-expr :input "{3}"
                 :expect (:vl-concat nil 3))

(test-parse-expr :input "{3, 4, 5}"
                 :expect (:vl-concat nil 3 4 5))

(test-parse-expr :input "{3 4}"
                 :successp nil)

(test-parse-expr :input "{0,}"
                 :successp nil)

(test-parse-expr :input "{3 {}}" :successp nil)

(test-parse-expr :input "{3 {4}}"
                 :expect (:vl-multiconcat nil 3 (:vl-concat nil 4)))

(test-parse-expr :input "{3 {4, 5}}"
                 :expect (:vl-multiconcat nil 3 (:vl-concat nil 4 5)))

(test-parse-expr :input "{3 {4 {5}}"
                 :successp nil)





(test-parse-expr :input "foo ()" ;; not an acceptable function call, since no args.
                 :expect (id "foo")
                 :remainder (list (make-vl-plaintoken
                                   :type :vl-lparen
                                   :etext (list (make-vl-echar :char #\(
                                                               :loc (vl-location "[internal string]" 1 4))))
                                  (make-vl-plaintoken
                                   :type :vl-rparen
                                   :etext (list (make-vl-echar :char #\)
                                                               :loc (vl-location "[internal string]" 1 5))))))

(test-parse-expr :input "foo(1)"
                 :expect (:vl-funcall nil (fun "foo") 1))

(test-parse-expr :input "foo(1, 2)"
                 :expect (:vl-funcall nil (fun "foo") 1 2))

(test-parse-expr :input "\\foo+bar (1, 2)"
                 :expect (:vl-funcall nil (fun "foo+bar") 1 2))

(test-parse-expr :input "foo.bar(1, 2)"
                 :expect (:vl-funcall nil (:vl-hid-dot nil
                                                       (hid "foo")
                                                       (hid "bar"))
                                      1 2))

(test-parse-expr :input "foo (* bar = 1, baz, boop *) (* baz = 2*) (3, 4, 5)"
                 :expect (:vl-funcall (("bar" <- 1) "baz" "boop" ("baz" <- 2))
                                      (fun "foo")
                                      3 4 5))

(test-parse-expr :input "foo[1].bar[2].baz(3)"
                 :expect (:vl-funcall nil
                                      (:vl-hid-arraydot nil (hid "foo") 1
                                                        (:vl-hid-arraydot nil (hid "bar") 2 (hid "baz")))
                                      3))



(test-parse-expr :input "$foo"
                 :expect (:vl-syscall nil (sys "$foo")))

(test-parse-expr :input "$foo(1, 2)"
                 :expect (:vl-syscall nil (sys "$foo") 1 2))

(test-parse-expr :input "$foo()"
                 :successp nil)




;               Table 5-4 --- Precedence rules for operators
;
;   Highest Precedence      +  -  !  ~  &  ~&  |  ~|  ^  ~^  ^~    (unary)
;                           **
;                           *  /  %
;                           +  -               (binary)
;                           <<  >>  <<<  >>>
;                           <   <=  >    >=
;                           ==  !=  ===  !==
;                           &                  (binary)
;                           ^  ^~  ~^          (binary)
;                           |                  (binary)
;                           &&
;                           ||
;                           ?:                 (conditional operator)
;   Lowest Precedence       {} {{}}            (concatenations)

(test-parse-expr :input "& (* cool *) x"
                 :expect (:vl-unary-bitand ("cool") (id "x")))


;; Basic associativity tests.

(test-parse-expr :input "1 || 2 || 3"   :expect (:vl-binary-logor nil (:vl-binary-logor nil 1 2) 3))
(test-parse-expr :input "1 && 2 && 3"   :expect (:vl-binary-logand nil (:vl-binary-logand nil 1 2) 3))
(test-parse-expr :input "1 | 2 | 3"     :expect (:vl-binary-bitor nil (:vl-binary-bitor nil 1 2) 3))
(test-parse-expr :input "1 ^ 2 ^ 3"     :expect (:vl-binary-xor nil (:vl-binary-xor nil 1 2) 3))
(test-parse-expr :input "1 ^~ 2 ^ 3"    :expect (:vl-binary-xor nil (:vl-binary-xnor nil 1 2) 3))
(test-parse-expr :input "1 ^~ 2 ~^ 3"   :expect (:vl-binary-xnor nil (:vl-binary-xnor nil 1 2) 3))
(test-parse-expr :input "1 & 2 & 3"     :expect (:vl-binary-bitand nil (:vl-binary-bitand nil 1 2) 3))
(test-parse-expr :input "1 == 2 == 3"   :expect (:vl-binary-eq nil (:vl-binary-eq nil 1 2) 3))
(test-parse-expr :input "1 != 2 == 3"   :expect (:vl-binary-eq nil (:vl-binary-neq nil 1 2) 3))
(test-parse-expr :input "1 !== 2 == 3"  :expect (:vl-binary-eq nil (:vl-binary-cne nil 1 2) 3))
(test-parse-expr :input "1 === 2 == 3"  :expect (:vl-binary-eq nil (:vl-binary-ceq nil 1 2) 3))
(test-parse-expr :input "1 < 2 < 3"     :expect (:vl-binary-lt nil (:vl-binary-lt nil 1 2) 3))
(test-parse-expr :input "1 <= 2 <= 3"   :expect (:vl-binary-lte nil (:vl-binary-lte nil 1 2) 3))
(test-parse-expr :input "1 << 2 >> 3"   :expect (:vl-binary-shr nil (:vl-binary-shl nil 1 2) 3))
(test-parse-expr :input "1 << 2 >>> 3"  :expect (:vl-binary-ashr nil (:vl-binary-shl nil 1 2) 3))
(test-parse-expr :input "1 <<< 2 >>> 3" :expect (:vl-binary-ashr nil (:vl-binary-ashl nil 1 2) 3))
(test-parse-expr :input "1 - 2 + 3"     :expect (:vl-binary-plus nil (:vl-binary-minus nil 1 2) 3))
(test-parse-expr :input "1 - 2 - 3"     :expect (:vl-binary-minus nil (:vl-binary-minus nil 1 2) 3))
(test-parse-expr :input "1 * 2 / 3"     :expect (:vl-binary-div nil (:vl-binary-times nil 1 2) 3))
(test-parse-expr :input "1 % 2 % 3"     :expect (:vl-binary-rem nil (:vl-binary-rem nil 1 2) 3))
(test-parse-expr :input "1 ** 2 ** 3"   :expect (:vl-binary-power nil (:vl-binary-power nil 1 2) 3))

(test-parse-expr :input "1 ? 2 : 3 ? 4 : 5"
                 :expect (:vl-qmark nil 1 2 (:vl-qmark nil 3 4 5)))

(test-parse-expr :input "1 ? 2 ? 3 : 4 : 5"
                 :expect (:vl-qmark nil 1 (:vl-qmark nil 2 3 4) 5))

(test-parse-expr :input "1 ? 2 ? 3 ? 4 : 5 : 6 : 7"
                 :expect (:vl-qmark nil 1
                                    (:vl-qmark nil 2
                                               (:vl-qmark nil 3 4 5)
                                               6)
                                    7))

(test-parse-expr :input "1 ? 2 : 3 ? 4 ? 5 : 6 : 7"
                 :expect (:vl-qmark nil 1 2
                                    (:vl-qmark nil 3
                                               (:vl-qmark nil 4 5 6)
                                               7)))

(test-parse-expr :input "1 ? 2 : 3 ? 4 ? 5 : 6 + 6.5 : 7 + 8"
                 :expect (:vl-qmark nil 1 2
                                    (:vl-qmark nil 3
                                               (:vl-qmark nil 4 5 (:vl-binary-plus nil 6 (real "6.5")))
                                               (:vl-binary-plus nil 7 8))))


;; Basic precedence tests.  In the tests below, 1 op 2 should always bind more
;; tightly.

(test-parse-expr :input "1 || 2 ? 3 : 4"
                 :expect (:vl-qmark nil (:vl-binary-logor nil 1 2) 3 4))

(test-parse-expr :input "1 && 2 || 3" :expect (:vl-binary-logor nil (:vl-binary-logand nil 1 2) 3))
(test-parse-expr :input "3 || 1 && 2" :expect (:vl-binary-logor nil 3 (:vl-binary-logand nil 1 2)))
(test-parse-expr :input "1 | 2 && 3"  :expect (:vl-binary-logand nil (:vl-binary-bitor nil 1 2) 3))
(test-parse-expr :input "3 && 1 | 2"  :expect (:vl-binary-logand nil 3 (:vl-binary-bitor nil 1 2)))
(test-parse-expr :input "1 ^ 2 | 3"   :expect (:vl-binary-bitor nil (:vl-binary-xor nil 1 2) 3))
(test-parse-expr :input "3 | 1 ^ 2"   :expect (:vl-binary-bitor nil 3 (:vl-binary-xor nil 1 2)))
(test-parse-expr :input "1 ^~ 2 | 3"  :expect (:vl-binary-bitor nil (:vl-binary-xnor nil 1 2) 3))
(test-parse-expr :input "3 | 1 ^~ 2"  :expect (:vl-binary-bitor nil 3 (:vl-binary-xnor nil 1 2)))
(test-parse-expr :input "1 ~^ 2 | 3"  :expect (:vl-binary-bitor nil (:vl-binary-xnor nil 1 2) 3))
(test-parse-expr :input "3 | 1 ~^ 2"  :expect (:vl-binary-bitor nil 3 (:vl-binary-xnor nil 1 2)))
(test-parse-expr :input "1 & 2 ^ 3"   :expect (:vl-binary-xor nil (:vl-binary-bitand nil 1 2) 3))
(test-parse-expr :input "3 ^ 1 & 2"   :expect (:vl-binary-xor nil 3 (:vl-binary-bitand nil 1 2)))
(test-parse-expr :input "1 == 2 & 3"  :expect (:vl-binary-bitand nil (:vl-binary-eq nil 1 2) 3))
(test-parse-expr :input "3 & 1 == 2"  :expect (:vl-binary-bitand nil 3 (:vl-binary-eq nil 1 2)))
(test-parse-expr :input "1 < 2 == 3"  :expect (:vl-binary-eq nil (:vl-binary-lt nil 1 2) 3))
(test-parse-expr :input "3 == 1 < 2"  :expect (:vl-binary-eq nil 3 (:vl-binary-lt nil 1 2)))
(test-parse-expr :input "1 << 2 < 3"  :expect (:vl-binary-lt nil (:vl-binary-shl nil 1 2) 3))
(test-parse-expr :input "3 < 1 << 2"  :expect (:vl-binary-lt nil 3 (:vl-binary-shl nil 1 2)))
(test-parse-expr :input "1 + 2 << 3"  :expect (:vl-binary-shl nil (:vl-binary-plus nil 1 2) 3))
(test-parse-expr :input "3 << 1 + 2"  :expect (:vl-binary-shl nil 3 (:vl-binary-plus nil 1 2)))
(test-parse-expr :input "1 * 2 + 3"   :expect (:vl-binary-plus nil (:vl-binary-times nil 1 2) 3))
(test-parse-expr :input "3 + 1 * 2"   :expect (:vl-binary-plus nil 3 (:vl-binary-times nil 1 2)))
(test-parse-expr :input "1 ** 2 * 3"  :expect (:vl-binary-times nil (:vl-binary-power nil 1 2) 3))
(test-parse-expr :input "3 * 1 ** 2"  :expect (:vl-binary-times nil 3 (:vl-binary-power nil 1 2)))

(test-parse-expr :input "-1 ** +2"
                 :expect (:vl-binary-power nil (:vl-unary-minus nil 1) (:vl-unary-plus nil 2)))

(test-parse-expr :input "1--2"
                 :expect (:vl-binary-minus nil 1 (:vl-unary-minus nil 2)))

(test-parse-expr :input "1++2"
                 :expect (:vl-binary-plus nil 1 (:vl-unary-plus nil 2)))


(test-parse-expr :input "3 < (1 << 2)"
                 :expect (:vl-binary-lt nil 3 (:vl-binary-shl ("VL_EXPLICIT_PARENS") 1 2)))
(test-parse-expr :input "(1 + 2 << 3)"
                 :expect (:vl-binary-shl ("VL_EXPLICIT_PARENS") (:vl-binary-plus nil 1 2) 3))
(test-parse-expr :input "(3 << 1) + 2"
                 :expect (:vl-binary-plus nil (:vl-binary-shl ("VL_EXPLICIT_PARENS") 3 1) 2))