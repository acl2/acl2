; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(defparser-top vl-parse-expression :resulttype vl-expr-p)

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
       (pstate            (make-vl-parsestate :warnings warnings))
       ((mv errmsg? val tokens pstate)
        (vl-parse-expression-top :tokens tokens
                                 :pstate pstate
                                 :config config))
       (remainder (vl-tokenlist->string-with-spaces tokens))
       (pretty (and (not errmsg?) (vl-pretty-expr val)))

       (test-okp

        (and
         (or (implies test.successp (not errmsg?))
             (cw "FAILURE: Expected parsing to succeed, but got error ~x0.~%"
                 errmsg?))

         (or (implies (not test.successp) errmsg?)
             (cw "FAILURE: Expected parsing to fail, but no error was produced.~%"))

         (or (equal (mergesort test.warnings)
                    (mergesort (vl-warninglist->types (vl-parsestate->warnings pstate))))
             (cw "FAILURE: Expected warnings ~x0, found warnings ~x1.~%"
                 test.warnings
                 (vl-parsestate->warnings pstate)))

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
            (list :errmsg    errmsg?
                  :val       val
                  :pretty    pretty
                  :remainder remainder
                  :pstate    pstate))
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

(trace-parser vl-parse-indexed-id-2005-fn)
(trace-parser vl-parse-indexed-id-2012-main-fn)
(trace-parser vl-parse-indexed-id-2012-fn)
(trace-parser vl-parse-indexed-id-fn)
(trace-parser vl-parse-primary-fn)


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
                  :expect '(:index nil "foo" (3) nil))

   (make-exprtest :input "foo[1:7]"
                  :expect '(:index nil "foo" () (:colon 1 7)))

   (make-exprtest
    :input "foo[3][4][5][1 +: 2]"
    :expect '(:index nil "foo" (3 4 5) (:pluscolon 1 2)))

   (make-exprtest
    :input "foo[3][1 -: 2]"
    :expect '(:index nil "foo" (3) (:minuscolon 1 2)))

   ;; HID tests

   (make-exprtest :input "foo.bar"
                  :expect '(:index nil (:dot "foo" "bar") nil nil))

   (make-exprtest :input "foo.bar.baz"
                  :expect '(:index nil (:dot "foo" (:dot "bar" "baz")) nil nil))

   (make-exprtest :input "foo[1].bar.baz"
                  :expect '(:index nil (:dot (:vl-hid-index "foo" (1)) (:dot "bar" "baz")) nil nil))

   (make-exprtest :input "foo[1].bar[2].baz"
                  :expect '(:index nil
                            (:dot (:vl-hid-index "foo" (1))
                             (:dot (:vl-hid-index "bar" (2))
                              "baz"))
                            nil nil))

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
                  :expect '(:vl-multiconcat nil 3 4))

   (make-exprtest :input "{3 {4, 5}}"
                  :expect '(:vl-multiconcat nil 3 4 5))

   (make-exprtest :input "{3 {4 {5}}"
                  :successp nil)


   (make-exprtest :input "foo(1)"
                  :expect '(:vl-funcall nil "foo" 1))

   (make-exprtest :input "foo(1, 2)"
                  :expect '(:vl-funcall nil "foo" 1 2))

   (make-exprtest :input "\\foo+bar (1, 2)"
                  :expect '(:vl-funcall nil "foo+bar" 1 2))

   (make-exprtest :input "foo.bar(1, 2)"
                  :expect '(:vl-funcall nil (:dot "foo" "bar") 1 2))

   (make-exprtest
    :input "foo (* bar = 1, baz, boop *) (* baz = 2*) (3, 4, 5)"
    :expect '(:vl-funcall (("bar" <- 1) "boop" ("baz" <- 2)) "foo" 3 4 5)
    :warnings '(:vl-warn-shadowed-atts))

   (make-exprtest
    :input "foo[1].bar[2].baz(3)"
    :expect '(:vl-funcall nil
                          (:dot (:vl-hid-index "foo" (1))
                           (:dot (:vl-hid-index "bar" (2))
                            "baz"))
              3))

   (make-exprtest :input "$foo"
                  :expect '(:vl-syscall nil "$foo"))

   (make-exprtest :input "$foo(1, 2)"
                  :expect '(:vl-syscall nil "$foo" 1 2))

   (make-exprtest :input "$random"
                  :expect '(:vl-syscall nil "$random"))

   (make-exprtest :input "$urandom"
                  :expect '(:vl-syscall nil "$urandom"))

   (make-exprtest :input "$random()"
                  :expect '(:vl-syscall nil "$random"))

   (make-exprtest :input "$urandom()"
                  :expect '(:vl-syscall nil "$urandom"))

   (make-exprtest :input "$foo()"
                  ;; Historically we thought this should be an error.  However, Verilog
                  ;; simulators appear to accept input like $random(), so I guess it's
                  ;; supposed to work.
                  :expect '(:vl-syscall nil "$foo"))

   ;; These next three are important for property parsing to work correctly.
   (make-exprtest :input "a[*]"
                  :expect '(id "a")
                  :remainder "[ * ]")

   (make-exprtest :input "a[=]"
                  :expect '(id "a")
                  :remainder "[ = ]")

   (make-exprtest :input "a[->]"
                  :expect '(id "a")
                  :remainder "[ -> ]")


   (make-exprtest :input "$rose(foo, @(posedge clock))"
                  :expect '(:vl-syscall nil "$rose"
                            (id "foo")
                            (:event nil (:vl-posedge (id "clock")))))

   (make-exprtest :input "$rose(foo, @(posedge clock or negedge top.reset))"
                  :expect '(:vl-syscall nil "$rose"
                            (id "foo")
                            (:event nil
                             (:vl-posedge (id "clock"))
                             (:vl-negedge (:index nil (:dot "top" "reset") nil nil)))))
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

   ;; Test to make sure Bug 507 is fixed: :// should be lexed as a colon followed
   ;; by a comment, not as a :/ operator.
   (make-exprtest :input "1 ? 2 ://is it secret
                          3 ? 4 :// is it safe
                          5"
                  :expect '(:vl-qmark nil 1 2 (:vl-qmark nil 3 4 5)))


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



   (make-exprtest :input "3 < (1 << 2)"
                  :expect '(:vl-binary-lt nil 3 (:vl-binary-shl ("VL_EXPLICIT_PARENS") 1 2)))
   (make-exprtest :input "(1 + 2 << 3)"
                  :expect '(:vl-binary-shl ("VL_EXPLICIT_PARENS") (:vl-binary-plus nil 1 2) 3))
   (make-exprtest :input "(3 << 1) + 2"
                  :expect '(:vl-binary-plus nil (:vl-binary-shl ("VL_EXPLICIT_PARENS") 3 1) 2))

   ))

(defconst *basic-precedence-tests-2005*
  (list
   ;; BOZO wtf ?? can this be right?
   (make-exprtest :input "1--2"
                  :expect '(:vl-binary-minus nil 1 (:vl-unary-minus nil 2)))

   (make-exprtest :input "1++2"
                  :expect '(:vl-binary-plus nil 1 (:vl-unary-plus nil 2)))))

(defconst *basic-precedence-tests-2012*
  (list
   (make-exprtest :input "1--2"
                  :expect '(:vl-unary-postdec nil 1)
                  :remainder "2")

   (make-exprtest :input "1++2"
                  :expect '(:vl-unary-postinc nil 1)
                  :remainder "2")))


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

   (make-exprtest :input "! | a"
                  :expect
                  '(:VL-UNARY-LOGNOT NIL (:VL-UNARY-BITOR NIL (ID "a"))))
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
  (run-exprtests *basic-precedence-tests-2005*
                 :config (make-vl-loadconfig :edition :verilog-2005 :strictp t))
  (run-exprtests *basic-precedence-tests-2005*
                 :config (make-vl-loadconfig :edition :verilog-2005 :strictp nil))
  (run-exprtests *basic-precedence-tests-2012*
                 :config (make-vl-loadconfig :edition :system-verilog-2012 :strictp t))
  (run-exprtests *basic-precedence-tests-2012*
                 :config (make-vl-loadconfig :edition :system-verilog-2012 :strictp nil))
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

;; #+broken
;;     (make-exprtest
;;      :input "this"
;;      :expect '(key :vl-this))

    (make-exprtest
     :input "$root.foo"
     :expect '(:index nil (:dot :vl-$root "foo") nil nil))

    (make-exprtest
     :input "$root[2]"
     :successp nil)

    (make-exprtest
     :input "$root.foo.bar"
     :expect '(:index nil (:dot :vl-$root (:dot "foo" "bar")) nil nil))

    (make-exprtest
     :input "$root.foo[1].bar"
     :expect '(:index nil (:dot :vl-$root (:dot (:vl-hid-index "foo" (1)) "bar")) nil nil))

    (make-exprtest
     :input "$root.foo[1][2].bar"
     :expect '(:index nil (:dot :vl-$root (:dot (:vl-hid-index "foo" (1 2)) "bar")) nil nil))

    (make-exprtest
     :input "$root.foo[1][2].bar[3]"
     :expect '(:index nil (:dot :vl-$root (:dot (:vl-hid-index "foo" (1 2)) "bar")) (3) nil))

    (make-exprtest
     :input "$root.foo[1][2].bar[3:4]"
     :expect '(:index nil (:dot :vl-$root (:dot (:vl-hid-index "foo" (1 2)) "bar")) nil (:colon 3 4)))

    (make-exprtest
     :input "foo[1][2].bar[3:4]"
     :expect '(:index nil (:dot (:vl-hid-index "foo" (1 2)) "bar") nil (:colon 3 4)))

    (make-exprtest
     :input "baz.foo[1][2].bar[3:4]"
     :expect '(:index nil (:dot "baz" (:dot (:vl-hid-index "foo" (1 2)) "bar")) nil (:colon 3 4)))


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


    ;; tagged union types

    (make-exprtest :input "tagged"
                   :successp nil)

    (make-exprtest :input "tagged foo"
                   :expect '(:vl-tagged nil "foo"))

    (make-exprtest :input "tagged foo 3"
                   :expect '(:vl-tagged nil "foo" 3))

    (make-exprtest :input "tagged foo 3 + 4"
                   ;; The precedence here seems to be ambiguous.  Until we
                   ;; understand what it is supposed to be, this should just
                   ;; fail.
                   :successp nil)

    (make-exprtest :input "tagged foo (3 + 4)"
                   :expect '(:vl-tagged nil "foo"
                                        (:vl-binary-plus
                                         ("VL_EXPLICIT_PARENS") 3 4)))

    (make-exprtest :input "tagged foo {3,4}"
                   :expect '(:vl-tagged nil "foo"
                             (:vl-concat nil 3 4)))

    (make-exprtest :input "tagged foo ({3,4})"
                   :expect '(:vl-tagged nil "foo"
                                        (:vl-concat
                                         ("VL_EXPLICIT_PARENS") 3 4)))

    (make-exprtest :input "foo::bar"
                   :expect '(:index nil (:scope "foo" "bar") nil nil))

    (make-exprtest :input "foo::bar::baz"
                   :expect '(:index nil (:scope "foo" (:scope "bar" "baz")) nil nil))

    (make-exprtest :input "$unit::bar"
                   :expect '(:index nil (:scope (key :vl-$unit) "bar") nil nil))

    (make-exprtest :input "local::bar"
                   :expect '(:index nil (:scope (key :vl-local) "bar") nil nil))

    (make-exprtest :input "foo::bar.baz"
                   :expect '(:index nil (:scope "foo" (:dot "bar" "baz")) nil nil))

    (make-exprtest :input "foo::bar.baz[2].beep"
                   :expect '(:index nil (:scope "foo" (:dot "bar" (:dot (:vl-hid-index "baz" (2)) "beep"))) nil nil))

    (make-exprtest :input "foo::bar.baz[2]"
                   :expect '(:index nil (:scope "foo" (:dot "bar" "baz")) (2) nil))

    (make-exprtest :input "foo::bar.baz[4:3]"
                   :expect '(:index nil (:scope "foo" (:dot "bar" "baz")) nil (:colon 4 3)))


    ;; SystemVerilog versions -- these should fail to parse the assignment
    ;; operator because they aren't in parentheses.
    (make-exprtest :input "a = b"    :expect '(id "a") :remainder "= b")
    (make-exprtest :input "a += b"   :expect '(id "a") :remainder "+= b")
    (make-exprtest :input "a -= b"   :expect '(id "a") :remainder "-= b")
    (make-exprtest :input "a *= b"   :expect '(id "a") :remainder "*= b")
    (make-exprtest :input "a /= b"   :expect '(id "a") :remainder "/= b")
    (make-exprtest :input "a %= b"   :expect '(id "a") :remainder "%= b")
    (make-exprtest :input "a &= b"   :expect '(id "a") :remainder "&= b")
    (make-exprtest :input "a |= b"   :expect '(id "a") :remainder "|= b")
    (make-exprtest :input "a ^= b"   :expect '(id "a") :remainder "^= b")
    (make-exprtest :input "a <<= b"  :expect '(id "a") :remainder "<<= b")
    (make-exprtest :input "a >>= b"  :expect '(id "a") :remainder ">>= b")
    (make-exprtest :input "a <<<= b" :expect '(id "a") :remainder "<<<= b")
    (make-exprtest :input "a >>>= b" :expect '(id "a") :remainder ">>>= b")

   (make-exprtest :input "(a += ~b)"
                  :expect '(:vl-binary-plusassign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-unary-bitnot nil (id "b"))))

   (make-exprtest :input "(a += !b)"
                  :expect '(:vl-binary-plusassign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-unary-lognot nil (id "b"))))

   (make-exprtest :input "(a = b + 1)"
                  :expect '(:vl-binary-assign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-binary-plus nil (id "b") 1)))

   (make-exprtest :input "(a = b & 1)"
                  :expect '(:vl-binary-assign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-binary-bitand nil (id "b") 1)))

   (make-exprtest :input "(a = b | 1)"
                  :expect '(:vl-binary-assign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-binary-bitor nil (id "b") 1)))

   (make-exprtest :input "(a = b < 1)"
                  :expect '(:vl-binary-assign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-binary-lt nil (id "b") 1)))

   (make-exprtest :input "(a = b == 1)"
                  :expect '(:vl-binary-assign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-binary-eq nil (id "b") 1)))

   (make-exprtest :input "(a[1] = b << 1)"
                  :expect '(:vl-binary-assign ("VL_EXPLICIT_PARENS")
                            (:index nil "a" (1) nil)
                            (:vl-binary-shl nil (id "b") 1)))

   (make-exprtest :input "(a[3:0] += b ? c : d)"
                  :expect '(:vl-binary-plusassign ("VL_EXPLICIT_PARENS")
                            (:index nil "a" nil (:colon 3 0))
                            (:vl-qmark nil (id "b") (id "c") (id "d"))))

   (make-exprtest :input "(a -= {b,c})"
                  :expect '(:vl-binary-minusassign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-concat nil (id "b") (id "c"))))

   (make-exprtest :input "(a -= {b,c})"
                  :expect '(:vl-binary-minusassign ("VL_EXPLICIT_PARENS")
                            (id "a")
                            (:vl-concat nil (id "b") (id "c"))))

   ;; Increment/decrement stuff

   (make-exprtest :input "a (* FOO *) ++" :expect '(:vl-unary-postinc ("FOO") (id "a")))
   (make-exprtest :input "a (* FOO *) --" :expect '(:vl-unary-postdec ("FOO") (id "a")))

   (make-exprtest :input "++ (* FOO *) a" :expect '(:vl-unary-preinc ("FOO") (id "a")))
   (make-exprtest :input "-- (* FOO *) a" :expect '(:vl-unary-predec ("FOO") (id "a")))


   (make-exprtest :input "a + b++" :expect '(:vl-binary-plus nil (id "a")
                                             (:vl-unary-postinc nil (id "b"))))

   (make-exprtest :input "a + ++b" :expect '(:vl-binary-plus nil (id "a")
                                             (:vl-unary-preinc nil (id "b"))))

   (make-exprtest :input "a + + b" :expect '(:vl-binary-plus nil (id "a")
                                             (:vl-unary-plus nil (id "b"))))

   ;; Very subtle, see failtests/inc10.v.  This is the behavior I want to
   ;; implement, because some Verilog tools don't interpret this as +(w++).
   (make-exprtest :input "+ w++"
                  :expect '(:vl-unary-plus nil (id "w"))
                  :remainder "++")

   ;; Followup on previous test
   (make-exprtest :input "a + + b ++"
                  :expect '(:vl-binary-plus nil (id "a")
                            (:vl-unary-plus nil (id "b")))
                  :remainder "++")

   ;; Followup on previous test
   (make-exprtest :input "++a++"
                  :expect '(:vl-unary-preinc nil (id "a"))
                  :remainder "++")

   ;; SystemVerilog extends functions to allow empty argument lists
   (make-exprtest :input "foo ()"
                  :expect '(:vl-funcall nil "foo")
                  :remainder "")

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
     :expect '(:vl-syscall nil "$root")
     :remainder ". foo")

    (make-exprtest
     :input "$root[2]"
     :expect '(:vl-syscall nil "$root")
     :remainder "[ 2 ]")

    (make-exprtest
     :input "$root.foo.bar"
     :expect '(:vl-syscall nil "$root")
     :remainder ". foo . bar")

    (make-exprtest
     :input "$root.foo[1].bar"
     :expect '(:vl-syscall nil "$root")
     :remainder ". foo [ 1 ] . bar")

    (make-exprtest
     :input "$root.foo[1][2].bar"
     :expect '(:vl-syscall nil "$root")
     :remainder ". foo [ 1 ] [ 2 ] . bar")


    (make-exprtest
     :input "foo[1].bar[2][3].baz"
     :expect '(:index nil (:dot (:vl-hid-index "foo" (1)) "bar") (2 3) nil)
     :remainder ". baz")

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


    ;; Tagged union types aren't in Verilog-2005, so these should all just
    ;; basically think "tagged" is the first expression.

    (make-exprtest :input "tagged"
                   :expect '(id "tagged"))

    (make-exprtest :input "tagged foo"
                   :expect '(id "tagged")
                   :remainder "foo")

    (make-exprtest :input "tagged foo 3"
                   :expect '(id "tagged")
                   :remainder "foo 3")

    (make-exprtest :input "tagged foo 3 + 4"
                   :expect '(id "tagged")
                   :remainder "foo 3 + 4")

    (make-exprtest :input "tagged foo (3 + 4)"
                   :expect '(id "tagged")
                   :remainder "foo ( 3 + 4 )")

    (make-exprtest :input "foo::bar"
                   :expect '(id "foo")
                   :remainder ": : bar")

    (make-exprtest :input "foo::bar::baz"
                   :expect '(id "foo")
                   :remainder ": : bar : : baz")


   ;; new scope operation stuff
   (make-exprtest :input "$unit::bar"
                  :expect '(:vl-syscall nil "$unit")
                  :remainder ": : bar")

   (make-exprtest :input "local::bar"
                  :expect '(id "local")
                  :remainder ": : bar")

   ;; Verilog versions -- these aren't valid operators in Verilog, so most of these
   ;; should fail because, e.g., in the case of "a += b", we should see "a + ..." where
   ;; the ... part isn't a valid expression.
   (make-exprtest :input "a = b"    :expect '(id "a") :remainder "= b")
   (make-exprtest :input "a += b"   :successp nil)
   (make-exprtest :input "a -= b"   :successp nil)
   (make-exprtest :input "a *= b"   :successp nil)
   (make-exprtest :input "a /= b"   :successp nil)
   (make-exprtest :input "a %= b"   :successp nil)
   (make-exprtest :input "a &= b"   :successp nil)
   (make-exprtest :input "a |= b"   :successp nil)
   (make-exprtest :input "a ^= b"   :successp nil)
   (make-exprtest :input "a <<= b"  :successp nil)
   (make-exprtest :input "a >>= b"  :successp nil)
   (make-exprtest :input "a <<<= b" :successp nil)
   (make-exprtest :input "a >>>= b" :successp nil)

   (make-exprtest :input "foo ()" ;; not an acceptable function call, since no args.
                  :expect '(id "foo")
                  :remainder "( )")


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
                  :expect '(:vl-stream-left nil (1 :with (:arrindex 2))))

   (make-exprtest :input "{<<{1 with [(2)]}}"
                  :expect '(:vl-stream-left nil (1 :with (:arrindex 2))))

   (make-exprtest :input "{<<{1 with [2 + 3]}}"
                  :expect '(:vl-stream-left nil (1 :with (:arrindex (:vl-binary-plus nil 2 3)))))

   (make-exprtest :input "{<<{1 with [2:3]}}"
                  :expect '(:vl-stream-left nil (1 :with (:range 2 3))))

   (make-exprtest :input "{<<{1 with [2+:3]}}"
                  :expect '(:vl-stream-left nil (1 :with (:pluscolon 2 3))))

   (make-exprtest :input "{<<{1 with [2-:3]}}"
                  :expect '(:vl-stream-left nil (1 :with (:minuscolon 2 3))))

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
                  :expect '(:vl-stream-left nil (1 :with (:arrindex 2))))

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
                  :expect '(:vl-stream-right nil (1 :with (:arrindex 2))))

   (make-exprtest :input "{>>{1 with [(2)]}}"
                  :expect '(:vl-stream-right nil (1 :with (:arrindex 2))))

   (make-exprtest :input "{>>{1 with [2 + 3]}}"
                  :expect '(:vl-stream-right nil (1 :with (:arrindex (:vl-binary-plus nil 2 3)))))

   (make-exprtest :input "{>>{1 with [2:3]}}"
                  :expect '(:vl-stream-right nil (1 :with (:range 2 3))))

   (make-exprtest :input "{>>{1 with [2+:3]}}"
                  :expect '(:vl-stream-right nil (1 :with (:pluscolon 2 3))))

   (make-exprtest :input "{>>{1 with [2-:3]}}"
                  :expect '(:vl-stream-right nil (1 :with (:minuscolon 2 3))))

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
                  :expect '(:vl-stream-right nil (1 :with (:arrindex 2))))

   ;; Sized streaming concatenations
   (make-exprtest :input "{<<byte{a,b}}"
                  :expect '(:vl-stream-left nil (:vl-byte signed)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<<shortint{a,b}}"
                  :expect '(:vl-stream-left nil (:vl-shortint signed)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< int {a,b}}"
                  :expect '(:vl-stream-left nil (:vl-int signed)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< longint{a,b}}"
                  :expect '(:vl-stream-left nil (:vl-longint signed)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<<integer {a,b}}"
                  :expect '(:vl-stream-left nil (:vl-integer signed)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<<time {a,b}}"
                  :expect '(:vl-stream-left nil (:vl-time unsigned)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<<bit {a,b}}"
                  :expect '(:vl-stream-left nil (:vl-bit unsigned)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< reg {a,b}}"
                  :expect '(:vl-stream-left nil (:vl-reg unsigned)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< logic {a,b}}"
                  :expect '(:vl-stream-left nil (:vl-logic unsigned)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< shortreal{a,b}}"
                  :expect '(:vl-stream-left nil (:vl-shortreal unsigned)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< real {a,b}}"
                  :expect '(:vl-stream-left nil (:vl-real unsigned)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<<realtime {a,b}}"
                  :expect '(:vl-stream-left nil (:vl-realtime unsigned)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< 8 {a,b}}"
                  :expect '(:vl-stream-left nil 8
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< size {a,b}}"
                  :expect '(:vl-stream-left nil
                            (id "size")
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< local::opcode {a,b}}"
                  :expect '(:vl-stream-left nil
                            (:index nil (:scope (key :vl-local) "opcode") nil nil)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< foo::bar {a,b}}"
                  :expect '(:vl-stream-left nil
                            (:index nil (:scope "foo" "bar") nil nil)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< $unit::bar {a,b}}"
                  :expect '(:vl-stream-left nil
                            (:index nil (:scope (key :vl-$unit) "bar") nil nil)
                            (id "a")
                            (id "b")))

   (make-exprtest :input "{<< foo::bar::baz {a,b}}"
                  :expect '(:vl-stream-left nil
                            (:index nil (:scope "foo" (:scope "bar" "baz")) nil nil)
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


   ;; New fancy assignment operators
   (make-exprtest :input "(a = b)"    :expect '(:vl-binary-assign       ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a += b)"   :expect '(:vl-binary-plusassign   ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a -= b)"   :expect '(:vl-binary-minusassign  ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a *= b)"   :expect '(:vl-binary-timesassign  ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a /= b)"   :expect '(:vl-binary-divassign    ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a %= b)"   :expect '(:vl-binary-remassign    ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a &= b)"   :expect '(:vl-binary-andassign    ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a |= b)"   :expect '(:vl-binary-orassign     ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a ^= b)"   :expect '(:vl-binary-xorassign    ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a <<= b)"  :expect '(:vl-binary-shlassign    ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a >>= b)"  :expect '(:vl-binary-shrassign    ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a <<<= b)" :expect '(:vl-binary-ashlassign   ("VL_EXPLICIT_PARENS") (id "a") (id "b")))
   (make-exprtest :input "(a >>>= b)" :expect '(:vl-binary-ashrassign   ("VL_EXPLICIT_PARENS") (id "a") (id "b")))

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


   ;; Increment and decrement operators
   (make-exprtest :input "a++" :expect '(:vl-unary-postinc nil (id "a")))
   (make-exprtest :input "a--" :expect '(:vl-unary-postdec nil (id "a")))
   (make-exprtest :input "++a" :expect '(:vl-unary-preinc nil (id "a")))
   (make-exprtest :input "--a" :expect '(:vl-unary-predec nil (id "a")))


   ;; casting tests

   (make-exprtest :input "unsigned'(3)" :expect '(:cast nil :unsigned 3))
   (make-exprtest :input "signed'(3+4)" :expect '(:cast nil :signed (:vl-binary-plus nil 3 4)))
   (make-exprtest :input "const'(3+4)"  :expect '(:cast nil :const  (:vl-binary-plus nil 3 4)))
   (make-exprtest :input "string'(3+4)" :expect '(:cast nil (:vl-string unsigned) (:vl-binary-plus nil 3 4)))

   (make-exprtest :input "logic'(3+4)" :expect '(:cast nil (:vl-logic unsigned) (:vl-binary-plus nil 3 4)))
   (make-exprtest :input "myfoo'(3+4)" :expect '(:cast nil (id "myfoo") (:vl-binary-plus nil 3 4)))

   (make-exprtest :input "12'(3+4)" :expect '(:cast nil 12 (:vl-binary-plus nil 3 4)))

   ;; weird but legal, 1 + 2 is a valid expr, is a mintypmax expr, so (1 + 2) is a primary.
   (make-exprtest :input "(1+2)'(3+4)" :expect '(:cast nil (:vl-binary-plus ("VL_EXPLICIT_PARENS") 1 2)
                                                                     (:vl-binary-plus nil 3 4)))

   (make-exprtest :input "1+2'(3)" :expect '(:vl-binary-plus nil 1 (:cast nil 2 3)))

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




#||
(run-exprtests
 (list    (make-exprtest :input "$unit::bar" :expect '(:vl-scope nil (key :vl-$unit) (hid "bar"))))
 :config (make-vl-loadconfig :edition :system-verilog-2012
                             :strictp nil))

(run-exprtests
 :config (make-vl-loadconfig :edition :system-verilog-2012
                             :strictp nil)))

||#
