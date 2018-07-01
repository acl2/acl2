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
(include-book "../statements")


(defparser-top vl-parse-statement :resulttype vl-stmt-p)


(defaggregate stmttest
  :tag :stmttest
  ((input    stringp "The input to parse and lex.")
   (successp booleanp "Is the test expected to pass?" :default t)
   (expect    "Pretty statement we expect to get out, in case of success.")
   (remainder stringp "What we expect to remain in the input stream." :default "")))

(deflist stmttestlist-p (x)
  (stmttest-p x)
  :guard t)


(define make-stmttest-fail ((x stmttest-p))
  (change-stmttest x :successp nil))

(defprojection make-stmttests-fail (x)
  (make-stmttest-fail x)
  :guard (stmttestlist-p x))


(define run-stmttest ((test stmttest-p)
                      &key
                      ((config vl-loadconfig-p) '*vl-default-loadconfig*))
  (b* (((stmttest test) test)
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
        (vl-parse-statement-top :tokens tokens
                                :pstate pstate
                                :config config))
       (remainder (vl-tokenlist->string-with-spaces tokens))
       (pretty (and (not errmsg?) (vl-pretty-stmt val)))

       (test-okp

        (and
         (or (implies test.successp (not errmsg?))
             (cw "FAILURE: Expected parsing to succeed, but got error ~x0.~%"
                 errmsg?))

         (or (implies (not test.successp) errmsg?)
             (cw "FAILURE: Expected parsing to fail, but no error was produced.~%"))

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
        (cw "*** Results from vl-parse-statement: ~x0.~%"
            (list :errmsg    errmsg?
                  :val       val
                  :pretty    pretty
                  :remainder remainder
                  :pstate    pstate))
        (raise "Test failed")))
    t))

(define run-stmttests ((x stmttestlist-p)
                       &key
                       ((config vl-loadconfig-p) '*vl-default-loadconfig*))
  (if (atom x)
      t
    (prog2$ (run-stmttest (car x) :config config)
            (run-stmttests (cdr x) :config config))))


(defsection basic-tests
  ;; We check that these tests will pass on both SystemVerilog-2012 and
  ;; Verilog-2005.

  (defconst *basic-stmt-tests*
    (list
     (make-stmttest :input "foo = bar;"
                    :expect '((id "foo") := (id "bar")))

     (make-stmttest :input "foo <= bar;"
                    :expect '((id "foo") :<= (id "bar")))

     (make-stmttest :input "foo = bar ;"
                    :expect '((id "foo") := (id "bar")))

     (make-stmttest :input "foo < = bar;"
                    :successp nil)


     (make-stmttest :input "$finish;"
                    :expect '(:call "$finish" :system))

     (make-stmttest :input "$finish();"
                    :expect '(:call "$finish" :system))

     (make-stmttest :input "$display(\"foo\");"
                    :expect '(:call "$display" (str "foo") :system))

     (make-stmttest :input "$bits(foo);"
                    :expect '(:call "$bits" (id "foo") :system))

     (make-stmttest :input "factorial(n);"
                    :expect '(:call "factorial" (id "n")))

     (make-stmttest :input "foo.factorial(n);"
                    :expect '(:call (:dot "foo" "factorial")
                              (id "n")))

     (make-stmttest :input "ack(1,2);"
                    :expect '(:call "ack" 1 2))

     (make-stmttest :input "ack(1,2,);"  ;; bozo this might actually be permitted now?
                    :successp nil)

     (make-stmttest :input "ack(,1,2);"  ;; bozo this might actually be permitted now?
                    :successp nil)

     ))

  (make-event (progn$ (run-stmttests *basic-stmt-tests*
                                     :config (make-vl-loadconfig :edition :system-verilog-2012))
                      '(value-triple :success)))

  (make-event (progn$ (run-stmttests *basic-stmt-tests*
                                     :config (make-vl-loadconfig :edition :verilog-2005))
                      '(value-triple :success))))


(defsection system-verilog-only-stmt-tests
  ;; We check that these pass on SystemVerilog-2012.  We don't check how they
  ;; behave on Verilog-2005.

  (defconst *system-verilog-only-stmt-tests*
    (list

     (make-stmttest :input "break;"
                    :expect '(:break))

     (make-stmttest :input "continue;"
                    :expect '(:continue))

     (make-stmttest :input "return;"
                    :expect '(:return nil))

     (make-stmttest :input "return 5;"
                    :expect '(:return 5))

     ;; bozo things like this should work eventually

     (make-stmttest :input "foo::factorial(n);"
                    :expect '(:call (:scope "foo" "factorial")
                              (id "n")))

     (make-stmttest :input "$bits(integer);"
                    :expect '(:call "$bits" (:vl-integer signed) :system))

     (make-stmttest :input "foo(integer);"  ;; no type args for user-defined functions
                    :successp nil)


     (make-stmttest :input "foreach ( arr [i] ) return;"
                    :expect '(:foreach "arr"
                              :vars ("i")
                              :body (:return nil)))

     (make-stmttest :input "foreach ( arr [i, j] ) return;"
                    :expect '(:foreach "arr"
                              :vars ("i" "j")
                              :body (:return nil)))

     (make-stmttest :input "foreach ( arr [] ) return;"
                    :expect '(:foreach "arr"
                              :vars (nil)
                              :body (:return nil)))

     (make-stmttest :input "foreach ( arr [i,] ) return;"
                    :expect '(:foreach "arr"
                              :vars ("i" nil)
                              :body (:return nil)))

     (make-stmttest :input "foreach ( arr [,i] ) return;"
                    :expect '(:foreach "arr"
                              :vars (nil "i")
                              :body (:return nil)))

     (make-stmttest :input "foreach ( foo.barr [i] ) return;"
                    :expect '(:foreach (:dot "foo" "barr")
                              :vars ("i")
                              :body (:return nil)))

     (make-stmttest :input "foreach ( arr i ) return;"  ;; forgot brackets
                    :successp nil)

     (make-stmttest :input "foreach arr [i] return;"  ;; forgot parens
                    :successp nil)

     ))

  (make-event (progn$ (run-stmttests *system-verilog-only-stmt-tests*
                                     :config (make-vl-loadconfig :edition :system-verilog-2012))
                      '(value-triple :success))))




(defsection verilog-only-stmt-tests
  ;; We check that these pass on Verilog-2005.  We don't check how they behave
  ;; on SystemVerilog-2012.


  (defconst *verilog-only-stmt-tests*
    (list

     (make-stmttest :input "break;"
                    :expect '(:call "break"))

     (make-stmttest :input "continue;"
                    :expect '(:call "continue"))

     (make-stmttest :input "return;"
                    :expect '(:call "return"))

     (make-stmttest :input "return 5;"
                    :successp nil)

     (make-stmttest :input "foo::factorial(n);" ;; no scopes in Verilog-2005.
                    :successp nil)

     (make-stmttest :input "$bits(integer);"  ;; no type args in Verilog-2005.
                    :successp nil)

     (make-stmttest :input "foo(integer);"  ;; no type args for user-defined functions
                    :successp nil)
     ))

  (make-event (progn$ (run-stmttests *verilog-only-stmt-tests*
                                     :config (make-vl-loadconfig :edition :verilog-2005))
                      '(value-triple :success))))








#||

(defparser-top vl-parse-state)

(let ((tokens (make-test-tokens "foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "assign foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "force foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "deassign foo ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "release foo ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "(* taco = delicious *) begin end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin deassign foo ; end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin foo = bar ; end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))


(defmacro test-parse-integer-declaration (&key input atts names arrdims initvals (successp 't))
    `(assert! (let ((tokens (make-test-tokens ,input)))
                (mv-let (erp val tokens)
                        (vl-parse-integer-declaration ',atts tokens)
                        (declare (ignore tokens))
                        (if erp
                            (prog2$ (cw "ERP is ~x0.~%" erp)
                                    (not ,successp))
                          (prog2$ (cw "VAL is ~x0.~%" val)
                                  (and ,successp
                                       (test-vardecls-fn val :vl-integer ',atts
                                                         ',names ',arrdims ',initvals))))))))

||#

