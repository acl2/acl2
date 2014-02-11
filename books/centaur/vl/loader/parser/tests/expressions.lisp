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

(defaggregate exprtest
  :tag :exprtest
  ((input    stringp "The input to parse and lex.")
   (successp booleanp "Is the test expected to pass?"
             :default t)
   (expect    "Pretty expression we expect to get out, in case of success.")
   (remainder stringp
              "What we expect to remain in the input stream."
              :default "")
   (warnings  symbol-listp
              "Types of warnings we expect to see.")))

(deflist exprtestlist-p (x)
  (exprtest-p x)
  :guard t)

(define run-exprtest ((test exprtest-p)
                      &key
                      ((config vl-loadconfig-p) '*vl-default-loadconfig*))
  (b* (((exprtest test) test)
       (- (cw "Running test ~x0.~%" test))
       (tokens   (make-test-tokens test.input :config config))
       (warnings nil)
       ((mv errmsg? val tokens warnings) (vl-parse-expression))
       (remainder (vl-tokenlist->string-with-spaces tokens))
       (pretty (and val (vl-pretty-expr val)))

       (test-okp

        (and
         (or (implies test.successp (not errmsg?))
             (cw "FAILURE: Expected parsing to succeed, but got error ~x0.~%"
                 errmsg?))

         (or (implies (not test.successp) errmsg?)
             (cw "FAILURE: Expected parsing to fail, but no error was produced.~%"))

         (or (equal (mergesort test.warnings)
                    (mergesort (vl-warninglist->types warnings)))
             (cw "FAILURE: Expected warnings ~x0, found warnings ~x1.~%"
                 test.warnings warnings))

         (or (not test.successp)
             (equal test.remainder remainder)
             (cw "FAILURE: Expected remainder ~x0, found ~x1.~%"
                 test.remainder remainder))

         (or (not test.successp)
             (equal pretty test.expect)
             (cw "FAILURE: Expected result ~x0, found ~x1.~%"
                 test.expect pretty))))

       ((unless test-okp)
        (cw "*** Test failed: ~x0. ~%" test)
        (cw "*** Results from vl-parse-expression: ~x0.~%"
            (list :errmsg errmsg?
                  :val val
                  :pretty pretty
                  :remainder remainder
                  :warnings warnings))
        (raise "Test failed")))
    t))

(define run-exprtests ((x exprtestlist-p)
                       &key
                       ((config vl-loadconfig-p) '*vl-default-loadconfig*))
  (if (atom x)
      t
    (prog2$ (run-exprtest (car x) :config config)
            (run-exprtests (cdr x) :config config))))

(defconst *basic-ad-hoc-tests*
  (list

   (make-exprtest :input ")"
                  :successp nil)

   (make-exprtest :input "1"
                  :expect 1)

   (make-exprtest :input "3.4"
                  :expect '(real "3.4"))

   (make-exprtest :input "\"hello, world\""
                  :expect '(str "hello, world"))


   (make-exprtest :input "(3.4)"
                  :expect '(real "3.4"))

   (make-exprtest :input "(1:2:3)"
                  :expect '(:vl-mintypmax ("VL_EXPLICIT_PARENS") 1 2 3))

   (make-exprtest :input "( 1 : 2 : 3 )"
                  :expect '(:vl-mintypmax ("VL_EXPLICIT_PARENS") 1 2 3))

   (make-exprtest :input "( 3 : 4 )"
                  :successp nil)

   (make-exprtest :input "( 3 : 4 : )"
                  :successp nil)

   (make-exprtest :input "foo"
                  :expect '(id "foo"))

   (make-exprtest :input "foo[3]"
                  :expect '(:vl-bitselect nil (id "foo") 3))

   (make-exprtest :input "foo[1:7]"
                  :expect '(:vl-partselect-colon nil (id "foo") 1 7))

   (make-exprtest
    :input "foo[3][4][5][1 +: 2]"
    :expect '(:vl-partselect-pluscolon
              nil
              (:vl-bitselect nil
                             (:vl-bitselect nil
                                            (:vl-bitselect nil (id "foo") 3)
                                            4)
                             5)
              1 2))

   (make-exprtest
    :input "foo[3][1 -: 2]"
    :expect '(:vl-partselect-minuscolon nil
                                        (:vl-bitselect nil (id "foo") 3)
                                        1 2))

   (make-exprtest :input "foo.bar"
                  :expect '(:vl-hid-dot nil (hid "foo") (hid "bar")))

   (make-exprtest :input "foo.bar.baz"
                  :expect '(:vl-hid-dot nil (hid "foo")
                                        (:vl-hid-dot nil (hid "bar") (hid "baz"))))

   (make-exprtest
    :input "foo[1].bar.baz"
    :expect '(:vl-hid-arraydot nil (hid "foo") 1
                               (:vl-hid-dot nil (hid "bar") (hid "baz"))))

   (make-exprtest
    :input "foo[1].bar[2].baz"
    :expect '(:vl-hid-arraydot nil (hid "foo") 1
                               (:vl-hid-arraydot nil (hid "bar") 2 (hid "baz"))))


   (make-exprtest :input "{}"
                  :successp nil)

   (make-exprtest :input "{3}"
                  :expect '(:vl-concat nil 3))

   (make-exprtest :input "{3, 4, 5}"
                  :expect '(:vl-concat nil 3 4 5))

   (make-exprtest :input "{3 4}"
                  :successp nil)

   (make-exprtest :input "{0,}"
                  :successp nil)

   (make-exprtest :input "{3 {}}" :successp nil)

   (make-exprtest :input "{3 {4}}"
                  :expect '(:vl-multiconcat nil 3 (:vl-concat nil 4)))

   (make-exprtest :input "{3 {4, 5}}"
                  :expect '(:vl-multiconcat nil 3 (:vl-concat nil 4 5)))

   (make-exprtest :input "{3 {4 {5}}"
                  :successp nil)


   (make-exprtest
    :input "foo ()" ;; not an acceptable function call, since no args.
    :expect '(id "foo")
    :remainder "( )")

   (make-exprtest :input "foo(1)"
                  :expect '(:vl-funcall nil (fun "foo") 1))

   (make-exprtest :input "foo(1, 2)"
                  :expect '(:vl-funcall nil (fun "foo") 1 2))

   (make-exprtest :input "\\foo+bar (1, 2)"
                  :expect '(:vl-funcall nil (fun "foo+bar") 1 2))

   (make-exprtest :input "foo.bar(1, 2)"
                  :expect '(:vl-funcall nil (:vl-hid-dot nil
                                                         (hid "foo")
                                                         (hid "bar"))
                                        1 2))

   (make-exprtest
    :input "foo (* bar = 1, baz, boop *) (* baz = 2*) (3, 4, 5)"
    :expect '(:vl-funcall (("bar" <- 1) "boop" ("baz" <- 2))
                          (fun "foo")
                          3 4 5)
    :warnings '(:vl-warn-shadowed-atts))

   (make-exprtest
    :input "foo[1].bar[2].baz(3)"
    :expect '(:vl-funcall
              nil
              (:vl-hid-arraydot nil (hid "foo") 1
                                (:vl-hid-arraydot nil (hid "bar") 2 (hid "baz")))
              3))

   (make-exprtest
    :input "$foo"
    :expect '(:vl-syscall nil (sys "$foo")))

   (make-exprtest :input "$foo(1, 2)"
                  :expect '(:vl-syscall nil (sys "$foo") 1 2))

   (make-exprtest :input "$foo()"
                  :successp nil)


   ))

(make-event
 (progn$
  (run-exprtests *basic-ad-hoc-tests* :config *vl-default-loadconfig*)
  '(value-triple :success)))




(defconst *basic-precedence-tests*
  (list

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

   (make-exprtest :input "& (* cool *) x"
                  :expect '(:vl-unary-bitand ("cool") (id "x")))


   ;; Basic associativity tests.

   (make-exprtest :input "1 || 2 || 3"   :expect '(:vl-binary-logor nil (:vl-binary-logor nil 1 2) 3))
   (make-exprtest :input "1 && 2 && 3"   :expect '(:vl-binary-logand nil (:vl-binary-logand nil 1 2) 3))
   (make-exprtest :input "1 | 2 | 3"     :expect '(:vl-binary-bitor nil (:vl-binary-bitor nil 1 2) 3))
   (make-exprtest :input "1 ^ 2 ^ 3"     :expect '(:vl-binary-xor nil (:vl-binary-xor nil 1 2) 3))
   (make-exprtest :input "1 ^~ 2 ^ 3"    :expect '(:vl-binary-xor nil (:vl-binary-xnor nil 1 2) 3))
   (make-exprtest :input "1 ^~ 2 ~^ 3"   :expect '(:vl-binary-xnor nil (:vl-binary-xnor nil 1 2) 3))
   (make-exprtest :input "1 & 2 & 3"     :expect '(:vl-binary-bitand nil (:vl-binary-bitand nil 1 2) 3))
   (make-exprtest :input "1 == 2 == 3"   :expect '(:vl-binary-eq nil (:vl-binary-eq nil 1 2) 3))
   (make-exprtest :input "1 != 2 == 3"   :expect '(:vl-binary-eq nil (:vl-binary-neq nil 1 2) 3))
   (make-exprtest :input "1 !== 2 == 3"  :expect '(:vl-binary-eq nil (:vl-binary-cne nil 1 2) 3))
   (make-exprtest :input "1 === 2 == 3"  :expect '(:vl-binary-eq nil (:vl-binary-ceq nil 1 2) 3))
   (make-exprtest :input "1 < 2 < 3"     :expect '(:vl-binary-lt nil (:vl-binary-lt nil 1 2) 3))
   (make-exprtest :input "1 <= 2 <= 3"   :expect '(:vl-binary-lte nil (:vl-binary-lte nil 1 2) 3))
   (make-exprtest :input "1 << 2 >> 3"   :expect '(:vl-binary-shr nil (:vl-binary-shl nil 1 2) 3))
   (make-exprtest :input "1 << 2 >>> 3"  :expect '(:vl-binary-ashr nil (:vl-binary-shl nil 1 2) 3))
   (make-exprtest :input "1 <<< 2 >>> 3" :expect '(:vl-binary-ashr nil (:vl-binary-ashl nil 1 2) 3))
   (make-exprtest :input "1 - 2 + 3"     :expect '(:vl-binary-plus nil (:vl-binary-minus nil 1 2) 3))
   (make-exprtest :input "1 - 2 - 3"     :expect '(:vl-binary-minus nil (:vl-binary-minus nil 1 2) 3))
   (make-exprtest :input "1 * 2 / 3"     :expect '(:vl-binary-div nil (:vl-binary-times nil 1 2) 3))
   (make-exprtest :input "1 % 2 % 3"     :expect '(:vl-binary-rem nil (:vl-binary-rem nil 1 2) 3))
   (make-exprtest :input "1 ** 2 ** 3"   :expect '(:vl-binary-power nil (:vl-binary-power nil 1 2) 3))

   (make-exprtest :input "1 ? 2 : 3 ? 4 : 5"
                  :expect '(:vl-qmark nil 1 2 (:vl-qmark nil 3 4 5)))

   (make-exprtest :input "1 ? 2 ? 3 : 4 : 5"
                  :expect '(:vl-qmark nil 1 (:vl-qmark nil 2 3 4) 5))

   (make-exprtest :input "1 ? 2 ? 3 ? 4 : 5 : 6 : 7"
                  :expect '(:vl-qmark nil 1
                                      (:vl-qmark nil 2
                                                 (:vl-qmark nil 3 4 5)
                                                 6)
                                      7))

   (make-exprtest :input "1 ? 2 : 3 ? 4 ? 5 : 6 : 7"
                  :expect '(:vl-qmark nil 1 2
                                      (:vl-qmark nil 3
                                                 (:vl-qmark nil 4 5 6)
                                                 7)))

   (make-exprtest :input "1 ? 2 : 3 ? 4 ? 5 : 6 + 6.5 : 7 + 8"
                  :expect '(:vl-qmark nil 1 2
                                      (:vl-qmark nil 3
                                                 (:vl-qmark nil 4 5 (:vl-binary-plus nil 6 (real "6.5")))
                                                 (:vl-binary-plus nil 7 8))))


   ;; Basic precedence tests.  In the tests below, 1 op 2 should always bind more
   ;; tightly.

   (make-exprtest :input "1 || 2 ? 3 : 4"
                  :expect '(:vl-qmark nil (:vl-binary-logor nil 1 2) 3 4))

   (make-exprtest :input "1 && 2 || 3" :expect '(:vl-binary-logor nil (:vl-binary-logand nil 1 2) 3))
   (make-exprtest :input "3 || 1 && 2" :expect '(:vl-binary-logor nil 3 (:vl-binary-logand nil 1 2)))
   (make-exprtest :input "1 | 2 && 3"  :expect '(:vl-binary-logand nil (:vl-binary-bitor nil 1 2) 3))
   (make-exprtest :input "3 && 1 | 2"  :expect '(:vl-binary-logand nil 3 (:vl-binary-bitor nil 1 2)))
   (make-exprtest :input "1 ^ 2 | 3"   :expect '(:vl-binary-bitor nil (:vl-binary-xor nil 1 2) 3))
   (make-exprtest :input "3 | 1 ^ 2"   :expect '(:vl-binary-bitor nil 3 (:vl-binary-xor nil 1 2)))
   (make-exprtest :input "1 ^~ 2 | 3"  :expect '(:vl-binary-bitor nil (:vl-binary-xnor nil 1 2) 3))
   (make-exprtest :input "3 | 1 ^~ 2"  :expect '(:vl-binary-bitor nil 3 (:vl-binary-xnor nil 1 2)))
   (make-exprtest :input "1 ~^ 2 | 3"  :expect '(:vl-binary-bitor nil (:vl-binary-xnor nil 1 2) 3))
   (make-exprtest :input "3 | 1 ~^ 2"  :expect '(:vl-binary-bitor nil 3 (:vl-binary-xnor nil 1 2)))
   (make-exprtest :input "1 & 2 ^ 3"   :expect '(:vl-binary-xor nil (:vl-binary-bitand nil 1 2) 3))
   (make-exprtest :input "3 ^ 1 & 2"   :expect '(:vl-binary-xor nil 3 (:vl-binary-bitand nil 1 2)))
   (make-exprtest :input "1 == 2 & 3"  :expect '(:vl-binary-bitand nil (:vl-binary-eq nil 1 2) 3))
   (make-exprtest :input "3 & 1 == 2"  :expect '(:vl-binary-bitand nil 3 (:vl-binary-eq nil 1 2)))
   (make-exprtest :input "1 < 2 == 3"  :expect '(:vl-binary-eq nil (:vl-binary-lt nil 1 2) 3))
   (make-exprtest :input "3 == 1 < 2"  :expect '(:vl-binary-eq nil 3 (:vl-binary-lt nil 1 2)))
   (make-exprtest :input "1 << 2 < 3"  :expect '(:vl-binary-lt nil (:vl-binary-shl nil 1 2) 3))
   (make-exprtest :input "3 < 1 << 2"  :expect '(:vl-binary-lt nil 3 (:vl-binary-shl nil 1 2)))
   (make-exprtest :input "1 + 2 << 3"  :expect '(:vl-binary-shl nil (:vl-binary-plus nil 1 2) 3))
   (make-exprtest :input "3 << 1 + 2"  :expect '(:vl-binary-shl nil 3 (:vl-binary-plus nil 1 2)))
   (make-exprtest :input "1 * 2 + 3"   :expect '(:vl-binary-plus nil (:vl-binary-times nil 1 2) 3))
   (make-exprtest :input "3 + 1 * 2"   :expect '(:vl-binary-plus nil 3 (:vl-binary-times nil 1 2)))
   (make-exprtest :input "1 ** 2 * 3"  :expect '(:vl-binary-times nil (:vl-binary-power nil 1 2) 3))
   (make-exprtest :input "3 * 1 ** 2"  :expect '(:vl-binary-times nil 3 (:vl-binary-power nil 1 2)))

   (make-exprtest :input "-1 ** +2"
                  :expect '(:vl-binary-power nil (:vl-unary-minus nil 1) (:vl-unary-plus nil 2)))

   ;; BOZO wtf ?? can this be right?
   (make-exprtest :input "1--2"
                  :expect '(:vl-binary-minus nil 1 (:vl-unary-minus nil 2)))

   (make-exprtest :input "1++2"
                  :expect '(:vl-binary-plus nil 1 (:vl-unary-plus nil 2)))


   (make-exprtest :input "3 < (1 << 2)"
                  :expect '(:vl-binary-lt nil 3 (:vl-binary-shl ("VL_EXPLICIT_PARENS") 1 2)))
   (make-exprtest :input "(1 + 2 << 3)"
                  :expect '(:vl-binary-shl ("VL_EXPLICIT_PARENS") (:vl-binary-plus nil 1 2) 3))
   (make-exprtest :input "(3 << 1) + 2"
                  :expect '(:vl-binary-plus nil (:vl-binary-shl ("VL_EXPLICIT_PARENS") 3 1) 2))

   ))

(make-event
 (progn$
  (run-exprtests *basic-precedence-tests* :config *vl-default-loadconfig*)
  '(value-triple :success)))


(defconst *basic-atts-tests*
  (list

   (make-exprtest :input "1 + (* foo *) 2"
                  :expect '(:vl-binary-plus ("foo") 1 2))

   (make-exprtest :input "1 + (* foo *) (* bar *) 2"
                  :expect '(:vl-binary-plus ("foo" "bar") 1 2))

   (make-exprtest :input "1 + (* foo, bar *) 2"
                  :expect '(:vl-binary-plus ("foo" "bar") 1 2))

   (make-exprtest :input "1 + (* foo, bar , foo *) 2"
                  ;; The order of attributes here is arguably weird, but seems
                  ;; basically reasonable.  We implement "later attributes win"
                  ;; by just deleting earlier attributes.
                  :expect '(:vl-binary-plus ("bar" "foo") 1 2)
                  :warnings '(:vl-warn-shadowed-atts))

   (make-exprtest :input "1 + (* foo *) (* bar , foo *) 2"
                  :expect '(:vl-binary-plus ("bar" "foo") 1 2)
                  :warnings '(:vl-warn-shadowed-atts))

   (make-exprtest :input "1 + (* foo *) (* bar *) (* foo *) 2"
                  :expect '(:vl-binary-plus ("bar" "foo") 1 2)
                  :warnings '(:vl-warn-shadowed-atts))

   (make-exprtest :input "1 + (* foo = 1, bar , foo = 2 *) 2"
                  :expect '(:vl-binary-plus ("bar" ("foo" <- 2)) 1 2)
                  :warnings '(:vl-warn-shadowed-atts))

   (make-exprtest :input "1 + (* foo = 1, bar = 3, foo = 2 *) 2"
                  :expect '(:vl-binary-plus (("bar" <- 3) ("foo" <- 2)) 1 2)
                  :warnings '(:vl-warn-shadowed-atts))

   (make-exprtest :input "1 + (* foo = 1 *) (* bar = 3, foo = 2 *) 2"
                  :expect '(:vl-binary-plus (("bar" <- 3) ("foo" <- 2)) 1 2)
                  :warnings '(:vl-warn-shadowed-atts))

   (make-exprtest :input "1 + (* foo = 1, bar = 3 *) (* foo = 2 *) 2"
                  :expect '(:vl-binary-plus (("bar" <- 3) ("foo" <- 2)) 1 2)
                  :warnings '(:vl-warn-shadowed-atts))

   ;; Make sure nested attributes are properly prohibited

   (make-exprtest :input "1 + (* foo = 3 *) 2"
                  :expect '(:vl-binary-plus (("foo" <- 3)) 1 2))

   (make-exprtest :input "1 + (* foo = 3 + 4 *) 2"
                  :expect '(:vl-binary-plus
                            (("foo" <- (:vl-binary-plus nil 3 4)))
                            1 2))

   (make-exprtest :input "1 + (* foo = 3 + (* bar *) 4 *) 2"
                  :successp nil)

   (make-exprtest :input "1 + (* foo = 3 + (* bar = 1 *) 4 *) 2"
                  :successp nil)

   ))

(make-event
 (progn$
  (run-exprtests *basic-atts-tests* :config *vl-default-loadconfig*)
  '(value-triple :success)))
