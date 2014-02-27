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

(define make-exprtest-fail ((x exprtest-p))
  (change-exprtest x :successp nil))

(defprojection make-exprtests-fail (x)
  (make-exprtest-fail x)
  :guard (exprtestlist-p x))

(define run-exprtest ((test exprtest-p)
                      &key
                      ((config vl-loadconfig-p) '*vl-default-loadconfig*))
  (b* (((exprtest test) test)
       (- (cw "Running test ~x0; edition ~s1, strict ~x2~%" test
              (vl-loadconfig->edition config)
              (vl-loadconfig->strictp config)))

       (echars (vl-echarlist-from-str test.input))
       ((mv successp tokens warnings)
        (vl-lex echars
                :config config
                :warnings nil))
       ((unless successp)
        (or (not test.successp)
            (raise "FAILURE: didn't even lex the input successfully.")))

       ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens))
       ((mv errmsg? val tokens warnings)
        (vl-parse-expression :tokens tokens
                             :warnings warnings
                             :config config))
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



#||

A very useful tracing mechanism for debugging:

(defmacro trace-parser (fn)
  `(trace$ (,fn
            :entry (list ',fn
                         :tokens (vl-tokenlist->string-with-spaces tokens)
                         :warnings (len warnings))
            :exit (list :errmsg (first values)
                        :val (second values)
                        :remainder (vl-tokenlist->string-with-spaces
                                    (third values))
                        :next-token (and (consp (third values))
                                         (vl-token->type (car (third values))))
                        :warnings (len (fourth values))))))

(trace-parser vl-parse-stream-concatenation-fn)
(trace-parser vl-parse-stream-expression-fn)
(trace-parser vl-parse-1+-stream-expressions-separated-by-commas-fn)
(trace-parser vl-parse-range-expression-fn)
(trace-parser vl-parse-expression-fn)
(trace-parser vl-parse-primary-fn)
(trace-parser vl-parse-simple-type-fn)
(trace-parser vl-parse-pva-tail-fn)
(trace-parser vl-parse-qmark-expression-fn)

(run-exprtest
 (make-exprtest
  :input "1 ? 2 -> 3 : 4"
  :expect '(:vl-qmark nil
                      1
                      (:vl-implies nil 2 3)
                      4)))

(run-exprtest
 (make-exprtest
  :input "1 -> 2 ? 3 -> 4 : 5 -> 6"
  :expect '(:vl-implies nil 1
                        (:vl-implies nil
                                     (:vl-qmark nil 2 (:vl-implies nil 3 4) 5)
                                     6))))



(run-exprtest
 (make-exprtest :input "1 + 2 -> 3"
                :expect '(:vl-implies nil (:vl-binary-plus nil 1 2) 3)))

(run-exprtest
 (make-exprtest :input "{<<{1 with [2]}}"
                :expect '(:vl-stream-left nil
                                          (:vl-with-index nil 1 2))))

(run-exprtest
 (make-exprtest :input "{<< foo::bar::baz {a,b}}"
                :expect '(:vl-stream-left-sized
                          nil
                          (:vl-scope nil
                                     (hid "foo")
                                     (:vl-scope nil
                                                (hid "bar")
                                                (hid "baz")))
                          (id "a")
                          (id "b"))))

||#




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
                  :expect '(:vl-index nil (id "foo") 3))

   (make-exprtest :input "foo[1:7]"
                  :expect '(:vl-partselect-colon nil (id "foo") 1 7))

   (make-exprtest
    :input "foo[3][4][5][1 +: 2]"
    :expect '(:vl-partselect-pluscolon
              nil
              (:vl-index nil
                         (:vl-index nil
                                    (:vl-index nil (id "foo") 3)
                                    4)
                         5)
              1 2))

   (make-exprtest
    :input "foo[3][1 -: 2]"
    :expect '(:vl-partselect-minuscolon nil
                                        (:vl-index nil (id "foo") 3)
                                        1 2))



   ;; HID tests

   (make-exprtest :input "foo.bar"
                  :expect '(:vl-hid-dot nil (hid "foo") (hid "bar")))

   (make-exprtest :input "foo.bar.baz"
                  :expect '(:vl-hid-dot nil (hid "foo")
                                        (:vl-hid-dot nil (hid "bar")
                                                     (hid "baz"))))

   (make-exprtest
    :input "foo[1].bar.baz"
    :expect '(:vl-hid-dot nil
                          (:vl-index nil (hid "foo") 1)
                          (:vl-hid-dot nil (hid "bar") (hid "baz"))))

   (make-exprtest
    :input "foo[1].bar[2].baz"
    :expect '(:vl-hid-dot
              nil
              (:vl-index nil (hid "foo") 1)
              (:vl-hid-dot nil
                           (:vl-index nil (hid "bar") 2)
                           (hid "baz"))))

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
    :expect '(:vl-funcall nil
                          (:vl-hid-dot nil
                                       (:vl-index nil (hid "foo") 1)
                                       (:vl-hid-dot nil
                                                    (:vl-index nil (hid "bar") 2)
                                                    (hid "baz")))
                          3))

   (make-exprtest
    :input "$foo"
    :expect '(:vl-syscall nil (sys "$foo")))

   (make-exprtest :input "$foo(1, 2)"
                  :expect '(:vl-syscall nil (sys "$foo") 1 2))

   (make-exprtest :input "$foo()"
                  :successp nil)


   ))

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


(defconst *all-basic-tests*
  ; Tests that should work on every configuration, Verilog-2005 and
  ; SystemVerilog-2005.
  (append *basic-ad-hoc-tests*
          *basic-precedence-tests*
          *basic-atts-tests*))

(make-event
 (progn$
  (run-exprtests *all-basic-tests*
                 :config (make-vl-loadconfig :edition :verilog-2005
                                             :strictp nil))
  (run-exprtests *all-basic-tests*
                 :config (make-vl-loadconfig :edition :verilog-2005
                                             :strictp t))
  (run-exprtests *all-basic-tests*
                 :config (make-vl-loadconfig :edition :system-verilog-2012
                                             :strictp nil))
  (run-exprtests *all-basic-tests*
                 :config (make-vl-loadconfig :edition :system-verilog-2012
                                             :strictp t))
  '(value-triple :success)))



; DIFF TESTS.
;
; These are special test cases which may be validly parsed in different ways on
; SystemVerilog-2012 versus Verilog-2005.

(progn

 (defconst *sysv-diff-tests* ;; The expected results for SystemVerilog-2012.
   (list

    (make-exprtest :input "3ns"
                   :expect '(time "3ns"))

    (make-exprtest :input "3.0s"
                   :expect '(time "3.0s"))

    (make-exprtest :input "3.0123ps"
                   :expect '(time "3.0123ps"))

    (make-exprtest :input "123.45us"
                   :expect '(time "123.45us"))

    (make-exprtest :input "123.0ms"
                   :expect '(time "123.0ms"))

    (make-exprtest :input "0fs"
                   :expect '(time "0fs"))

    (make-exprtest
     :input "null"
     :expect '(key :vl-null))

    (make-exprtest
     :input "this"
     :expect '(key :vl-this))

    (make-exprtest
     :input "$root.foo"
     :expect '(:vl-hid-dot nil
                           (key :vl-$root)
                           (hid "foo")))

    (make-exprtest
     :input "$root[2]"
     :successp nil)

    (make-exprtest
     :input "$root.foo.bar"
     :expect '(:vl-hid-dot nil
                           (key :vl-$root)
                           (:vl-hid-dot nil
                                        (hid "foo")
                                        (hid "bar"))))

    (make-exprtest
     :input "$root.foo[1].bar"
     :expect '(:vl-hid-dot nil
                           (key :vl-$root)
                           (:vl-hid-dot nil
                                        (:vl-index nil (hid "foo") 1)
                                        (hid "bar"))))

    (make-exprtest
     :input "$root.foo[1][2].bar"
     :expect '(:vl-hid-dot nil
                           (key :vl-$root)
                           (:vl-hid-dot nil
                                        (:vl-index nil
                                                   (:vl-index nil (hid "foo") 1)
                                                   2)
                                        (hid "bar"))))

    (make-exprtest
     :input "$root.foo[1][2].bar[3]"
     :expect
     '(:vl-index nil
                 (:vl-hid-dot nil
                              (key :vl-$root)
                              (:vl-hid-dot nil
                                           (:vl-index nil
                                                      (:vl-index nil (hid "foo") 1)
                                                      2)
                                           (hid "bar")))
                 3))

    (make-exprtest
     :input "$root.foo[1][2].bar[3:4]"
     :expect
     '(:vl-partselect-colon
       nil
       (:vl-hid-dot nil
                    (key :vl-$root)
                    (:vl-hid-dot nil
                                 (:vl-index nil
                                            (:vl-index nil (hid "foo") 1)
                                            2)
                                 (hid "bar")))
       3 4))

    (make-exprtest
     :input "foo[1][2].bar[3:4]"
     :expect
     '(:vl-partselect-colon
       nil
       (:vl-hid-dot nil
                    (:vl-index nil
                               (:vl-index nil (hid "foo") 1)
                               2)
                    (hid "bar"))
       3 4))

    (make-exprtest
     :input "baz.foo[1][2].bar[3:4]"
     :expect
     '(:vl-partselect-colon
       nil
       (:vl-hid-dot nil
                    (hid "baz")
                    (:vl-hid-dot nil
                                 (:vl-index nil
                                            (:vl-index nil (hid "foo") 1)
                                            2)
                                 (hid "bar")))
       3 4))


    ;; Basic precedence/associativity for arrows/equivs

    (make-exprtest :input "1 + 2 -> 3"
                   :expect '(:vl-implies nil (:vl-binary-plus nil 1 2) 3))

    (make-exprtest :input "1 -> 2 -> 3"
                   :expect '(:vl-implies nil 1 (:vl-implies nil 2 3)))

    (make-exprtest :input "1 -> 2 -> 3 -> 4"
                   :expect '(:vl-implies nil 1 (:vl-implies nil 2 (:vl-implies nil 3 4))))

    (make-exprtest :input "1 -> 2 <-> 3 -> 4"
                   :expect '(:vl-implies nil 1 (:vl-equiv nil 2 (:vl-implies nil 3 4))))

    (make-exprtest :input "1 -> 2 <-> 3 <-> 4"
                   :expect '(:vl-implies nil 1 (:vl-equiv nil 2 (:vl-equiv nil 3 4))))

    (make-exprtest :input "1 <-> 2 <-> 3 <-> 4"
                   :expect '(:vl-equiv nil 1 (:vl-equiv nil 2 (:vl-equiv nil 3 4))))

    (make-exprtest :input "1 <-> 2 -> 3 <-> 4"
                   :expect '(:vl-equiv nil 1 (:vl-implies nil 2 (:vl-equiv nil 3 4))))


    ;; Arrows versus ?: is subtle

    (make-exprtest :input "1 ? 2 : 3 -> 4"
                   :expect '(:vl-implies nil (:vl-qmark nil 1 2 3) 4))

    (make-exprtest :input "1 -> 2 ? 3 : 4"
                   :expect '(:vl-implies nil 1 (:vl-qmark nil 2 3 4)))

    (make-exprtest :input "1 ? 2->3 : 4"
                   :expect '(:vl-qmark nil 1 (:vl-implies nil 2 3) 4))

    (make-exprtest :input "1 -> 2 ? 3 : 4 -> 5"
                   ;; The arrows have lowest priority, so (2 ? 3 : 4) should bind
                   ;; most tightly.  The arrows are right associative, so we should
                   ;; have 1 -> ( 2?3:4 -> 5 )
                   :expect '(:vl-implies nil 1
                                         (:vl-implies nil
                                                      (:vl-qmark nil 2 3 4)
                                                      5)))

    (make-exprtest
     :input "1 -> 2 ? 3 -> 4 : 5 -> 6"
     :expect '(:vl-implies nil 1
                           (:vl-implies nil
                                        (:vl-qmark nil 2 (:vl-implies nil 3 4) 5)
                                        6)))

    (make-exprtest :input "1 ? 2 : 3 <-> 4"
                   :expect '(:vl-equiv nil (:vl-qmark nil 1 2 3) 4))

    (make-exprtest :input "1 <-> 2 ? 3 : 4"
                   :expect '(:vl-equiv nil 1 (:vl-qmark nil 2 3 4)))

    (make-exprtest :input "1 ? 2<->3 : 4"
                   :expect '(:vl-qmark nil 1 (:vl-equiv nil 2 3) 4))




    ))

 (defconst *verilog-diff-tests* ;; The expected results for Verilog-2005.
   (list
    (make-exprtest :input "3ns"
                   :expect 3
                   :remainder "ns")

    (make-exprtest :input "3.0s"
                   :expect '(real "3.0")
                   :remainder "s")

    (make-exprtest :input "3.0123ps"
                   :expect '(real "3.0123")
                   :remainder "ps")

    (make-exprtest :input "123.45us"
                   :expect '(real "123.45")
                   :remainder "us")

    (make-exprtest :input "123.0ms"
                   :expect '(real "123.0")
                   :remainder "ms")

    (make-exprtest :input "0fs"
                   :expect 0
                   :remainder "fs")

    (make-exprtest
     :input "null"
     :expect '(id "null"))

    (make-exprtest
     :input "this"
     :expect '(id "this"))

    (make-exprtest
     :input "$root.foo"
     :expect '(:vl-syscall nil (sys "$root"))
     :remainder ". foo")

    (make-exprtest
     :input "$root[2]"
     :expect '(:vl-syscall nil (sys "$root"))
     :remainder "[ 2 ]")

    (make-exprtest
     :input "$root.foo.bar"
     :expect '(:vl-syscall nil (sys "$root"))
     :remainder ". foo . bar")

    (make-exprtest
     :input "$root.foo[1].bar"
     :expect '(:vl-syscall nil (sys "$root"))
     :remainder ". foo [ 1 ] . bar")

    (make-exprtest
     :input "$root.foo[1][2].bar"
     :expect '(:vl-syscall nil (sys "$root"))
     :remainder ". foo [ 1 ] [ 2 ] . bar")


    (make-exprtest
     :input "foo[1].bar[2][3].bar"
     :expect '(:vl-index nil (:vl-index nil (:vl-hid-dot
                                             nil
                                             (:vl-index nil (hid "foo") 1)
                                             (hid "bar"))
                                        2)
                         3)
     :remainder ". bar")

    ;; No implies/equiv operators in Verilog-2005, so these will fail, but
    ;; they'll at least consume the input until the arrow/equiv.

    (make-exprtest :input "1 + 2 -> 3"
                   :expect '(:vl-binary-plus nil 1 2)
                   :remainder "-> 3")

    (make-exprtest :input "1 ? 2 : 3 -> 4"
                   :expect '(:vl-qmark nil 1 2 3)
                   :remainder "-> 4")

    (make-exprtest :input "1 + 2 -> 3"
                   :expect '(:vl-binary-plus nil 1 2)
                   :remainder "-> 3")

    (make-exprtest :input "1 ? 2 : 3 -> 4"
                   :expect '(:vl-qmark nil 1 2 3)
                   :remainder "-> 4")

    (make-exprtest :input "1 -> 2 -> 3"
                   :expect '1
                   :remainder "-> 2 -> 3")

    (make-exprtest :input "1 <-> 2 <-> 3 <-> 4"
                   ;; I originally expected this to return 1.  But that's not
                   ;; right.  Verilog-2005 has no <-> operator so the input
                   ;; above is really : 1 < -> 2 ...  And if we see a 1 <, it's
                   ;; we are going to look for another expression, e.g., we're
                   ;; expecting to see something like 1 < 2.  It seems
                   ;; completely fine to fail in this way, since this isn't
                   ;; good syntax.
                   :successp nil)

    ))

 (make-event
  (progn$

   (run-exprtests *sysv-diff-tests*
                  :config (make-vl-loadconfig :edition :system-verilog-2012
                                              :strictp nil))
   (run-exprtests *sysv-diff-tests*
                  :config (make-vl-loadconfig :edition :system-verilog-2012
                                              :strictp t))
   (run-exprtests *verilog-diff-tests*
                  :config (make-vl-loadconfig :edition :verilog-2005
                                              :strictp nil))
   (run-exprtests *verilog-diff-tests*
                  :config (make-vl-loadconfig :edition :verilog-2005
                                              :strictp t))
   '(value-triple :success))))


(progn

 (defconst *sysv-only-tests*
  ;; These are tests that work with SystemVerilog, but that are just malformed
  ;; for Verilog-2005.
  (list

   ;; extended literals, invalid in verilog-2005
   (make-exprtest :input "'0"
                  :expect '(ext :vl-0val))

   (make-exprtest :input "'1"
                  :expect '(ext :vl-1val))

   (make-exprtest :input "'x"
                  :expect '(ext :vl-xval))

   (make-exprtest :input "'z"
                  :expect '(ext :vl-zval))

   (make-exprtest :input "'02" ;; BOZO can this be right?
                  :expect '(ext :vl-0val)
                  :remainder "2")

   ;; lone $ signs, invalid in verilog-2005
   (make-exprtest :input "$"
                  :expect '(key :vl-$))

   ;; empty queue, invalid in verilog-2005
   (make-exprtest :input "{}"
                  :expect '(key :vl-emptyqueue))


   ;; streaming concatenations, invalid in verilog-2005
   (make-exprtest :input "{<<{}}"
                  :successp nil)

   (make-exprtest :input "{<<}"
                  :successp nil)

   (make-exprtest :input "{<<"
                  :successp nil)

   (make-exprtest :input "{<<{1}"
                  :successp nil)

   (make-exprtest :input "{<<{1}}"
                  :expect '(:vl-stream-left nil 1))

   (make-exprtest :input "{<<{1,2}}"
                  :expect '(:vl-stream-left nil 1 2))

   (make-exprtest :input "{<<{1,2,3+4}}"
                  :expect '(:vl-stream-left nil 1 2 (:vl-binary-plus nil 3 4)))

   (make-exprtest :input "{<<{1 with [2]}}"
                  :expect '(:vl-stream-left nil
                                            (:vl-with-index nil 1 2)))

   (make-exprtest :input "{<<{1 with [(2)]}}"
                  :expect '(:vl-stream-left nil
                                            (:vl-with-index nil 1 2)))

   (make-exprtest :input "{<<{1 with [2 + 3]}}"
                  :expect '(:vl-stream-left
                            nil
                            (:vl-with-index nil 1
                                            (:vl-binary-plus nil 2 3))))

   (make-exprtest :input "{<<{1 with [2:3]}}"
                  :expect '(:vl-stream-left nil
                                            (:vl-with-colon nil 1 2 3)))

   (make-exprtest :input "{<<{1 with [2+:3]}}"
                  :expect '(:vl-stream-left nil
                                            (:vl-with-pluscolon nil 1 2 3)))

   (make-exprtest :input "{<<{1 with [2-:3]}}"
                  :expect '(:vl-stream-left nil
                                            (:vl-with-minuscolon nil 1 2 3)))

   (make-exprtest :input "{<<{1 with [2}}"
                  :successp nil)

   (make-exprtest :input "{<<{1 with 2}}"
                  :successp nil)

   (make-exprtest :input "{<<{1 with [2-:}}"
                  :successp nil)

   (make-exprtest :input "{<<{1 with 2:3}}"
                  :successp nil)

   (make-exprtest :input "{<<{1with[2]}}"
                  ;; BOZO can this be right?  Well, maybe
                  :expect '(:vl-stream-left nil
                                            (:vl-with-index nil 1 2)))


   (make-exprtest :input "{>>{}}"
                  :successp nil)

   (make-exprtest :input "{>>}"
                  :successp nil)

   (make-exprtest :input "{>>"
                  :successp nil)

   (make-exprtest :input "{>>{1}"
                  :successp nil)

   (make-exprtest :input "{>>{1}}"
                  :expect '(:vl-stream-right nil 1))

   (make-exprtest :input "{>>{1,2}}"
                  :expect '(:vl-stream-right nil 1 2))

   (make-exprtest :input "{>>{1,2,3+4}}"
                  :expect '(:vl-stream-right nil 1 2 (:vl-binary-plus nil 3 4)))

   (make-exprtest :input "{>>{1 with [2]}}"
                  :expect '(:vl-stream-right nil
                                             (:vl-with-index nil 1 2)))

   (make-exprtest :input "{>>{1 with [(2)]}}"
                  :expect '(:vl-stream-right nil
                                             (:vl-with-index nil 1 2)))

   (make-exprtest :input "{>>{1 with [2 + 3]}}"
                  :expect '(:vl-stream-right
                            nil
                            (:vl-with-index nil 1
                                            (:vl-binary-plus nil 2 3))))

   (make-exprtest :input "{>>{1 with [2:3]}}"
                  :expect '(:vl-stream-right nil
                                             (:vl-with-colon nil 1 2 3)))

   (make-exprtest :input "{>>{1 with [2+:3]}}"
                  :expect '(:vl-stream-right nil
                                             (:vl-with-pluscolon nil 1 2 3)))

   (make-exprtest :input "{>>{1 with [2-:3]}}"
                  :expect '(:vl-stream-right nil
                                             (:vl-with-minuscolon nil 1 2 3)))

   (make-exprtest :input "{>>{1 with [2}}"
                  :successp nil)

   (make-exprtest :input "{>>{1 with 2}}"
                  :successp nil)

   (make-exprtest :input "{>>{1 with [2-:}}"
                  :successp nil)

   (make-exprtest :input "{>>{1 with 2:3}}"
                  :successp nil)

   (make-exprtest :input "{>>{1with[2]}}"
                  ;; BOZO can this be right?  Well, maybe
                  :expect '(:vl-stream-right nil
                                             (:vl-with-index nil 1 2)))

   ;; Sized streaming concatenations
   (make-exprtest :input "{<<byte{a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-byte)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<<shortint{a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-shortint)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< int {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-int)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< longint{a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-longint)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<<integer {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-integer)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<<time {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-time)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<<bit {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-bit)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< reg {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-reg)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< logic {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-logic)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< shortreal{a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-shortreal)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< real {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-real)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<<realtime {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (basic :vl-realtime)
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< 8 {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  8
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< size {a,b}}"
                  :expect '(:vl-stream-left-sized nil
                                                  (id "size")
                                                  (id "a")
                                                  (id "b")))

   (make-exprtest :input "{<< local::opcode {a,b}}"
                  :expect '(:vl-stream-left-sized
                            nil
                            (:vl-scope nil
                                       (key :vl-local)
                                       (hid "opcode"))
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< foo::bar {a,b}}"
                  :expect '(:vl-stream-left-sized
                            nil
                            (:vl-scope nil
                                       (hid "foo")
                                       (hid "bar"))
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< $unit::bar {a,b}}"
                  :expect '(:vl-stream-left-sized
                            nil
                            (:vl-scope nil
                                       (key :vl-$unit)
                                       (hid "bar"))
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< foo::bar::baz {a,b}}"
                  :expect '(:vl-stream-left-sized
                            nil
                            (:vl-scope nil
                                       (hid "foo")
                                       (:vl-scope nil
                                                  (hid "bar")
                                                  (hid "baz")))
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< foo::bar:: {a,b}}"
                  :successp nil)

   (make-exprtest :input "{<< foo #(.width(6))::bar::baz {a,b}}"
                  ;; Eventually this should be allowed, but we don't have any
                  ;; support for PVAs inside expressions right now.  This unit
                  ;; test is to remind me, if we ever do add such support,
                  ;; that we should have some unit tests for it.
                  :successp nil)


   ;; Associativity tests for new operators

   (make-exprtest :input "1 !=? 2 !=? 3" :expect '(:vl-binary-wildneq nil (:vl-binary-wildneq nil 1 2) 3))
   (make-exprtest :input "1 ==? 2 ==? 3" :expect '(:vl-binary-wildeq  nil (:vl-binary-wildeq nil 1 2) 3))
   (make-exprtest :input "1 !=? 2 == 3"  :expect '(:vl-binary-eq      nil (:vl-binary-wildneq nil 1 2) 3))
   (make-exprtest :input "1 !=? 2 !== 3" :expect '(:vl-binary-cne     nil (:vl-binary-wildneq nil 1 2) 3))


   ;; Basic precedence tests for the new operators.  In the tests below, 1 op 2
   ;; should always bind more tightly.

   (make-exprtest :input "1 + 2 ==? 3" :expect '(:vl-binary-wildeq nil (:vl-binary-plus nil 1 2) 3))
   (make-exprtest :input "1 < 2 ==? 3" :expect '(:vl-binary-wildeq nil (:vl-binary-lt nil 1 2) 3))
   (make-exprtest :input "1 ==? 2 & 3" :expect '(:vl-binary-bitand nil (:vl-binary-wildeq nil 1 2) 3))
   (make-exprtest :input "1 ==? 2 | 3" :expect '(:vl-binary-bitor nil (:vl-binary-wildeq nil 1 2) 3))
   (make-exprtest :input "1 * 2 !=? 3" :expect '(:vl-binary-wildneq nil (:vl-binary-times nil 1 2) 3))
   (make-exprtest :input "1 > 2 !=? 3" :expect '(:vl-binary-wildneq nil (:vl-binary-gt nil 1 2) 3))
   (make-exprtest :input "1 !=? 2 & 3" :expect '(:vl-binary-bitand nil (:vl-binary-wildneq nil 1 2) 3))
   (make-exprtest :input "1 !=? 2 | 3" :expect '(:vl-binary-bitor nil (:vl-binary-wildneq nil 1 2) 3))






   ))

 (make-event
 (progn$
  (run-exprtests *sysv-only-tests*
                 :config (make-vl-loadconfig :edition :system-verilog-2012
                                             :strictp nil))

  (run-exprtests *sysv-only-tests*
                 :config (make-vl-loadconfig :edition :system-verilog-2012
                                             :strictp t))

  (run-exprtests (make-exprtests-fail *sysv-only-tests*)
                 :config (make-vl-loadconfig :edition :verilog-2005
                                             :strictp nil))

  (run-exprtests (make-exprtests-fail *sysv-only-tests*)
                 :config (make-vl-loadconfig :edition :verilog-2005
                                             :strictp t))
  '(value-triple :success))))

