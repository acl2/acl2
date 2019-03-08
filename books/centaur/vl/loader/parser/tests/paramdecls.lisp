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
(include-book "../paramdecls")

(define vl-pretty-paramtype ((x vl-paramtype-p))
  (vl-paramtype-case x
    (:vl-implicitvalueparam
     (append '(:implicit)
             (if x.sign (list x.sign) nil)
             (if x.range (list (vl-pretty-range x.range)) nil)
             (if x.default
                 (list '= (vl-pretty-expr x.default))
               nil)))
    (:vl-explicitvalueparam
     (append '(:explicit)
             (list (vl-pretty-datatype x.type))
             (if x.default
                 (list '= (vl-pretty-expr x.default))
               nil)))
    (:vl-typeparam
     (append '(:type)
             (if x.default
                 (list '= (vl-pretty-datatype x.default))
               nil)))))

(define vl-pretty-paramdecl ((x vl-paramdecl-p))
  (b* (((vl-paramdecl x) x))
    (append (list x.name)
            (if x.localp (list :local) nil)
            (vl-pretty-paramtype x.type))))

(define vl-pretty-paramdecls ((x vl-paramdecllist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-paramdecl (car x))
          (vl-pretty-paramdecls (cdr x)))))

(defaggregate vl-paramdecltest
  ((input   stringp)
   (expect  "pretty paramdecls that we expect.")
   (successp booleanp :default t)))

(deflist vl-paramdecltestlist-p (x)
  (vl-paramdecltest-p x))

(define make-paramdecltests-fail ((x vl-paramdecltestlist-p))
  (if (atom x)
      nil
    (cons (change-vl-paramdecltest (car x) :successp nil)
          (make-paramdecltests-fail (cdr x)))))

(defparser-top vl-parse-param-or-localparam-declaration
  :guard (and (vl-atts-p atts)
              ;; Types says what kinds (local or nonlocal) of parameters we permit
              (true-listp types)
              (subsetp types '(:vl-kwd-parameter :vl-kwd-localparam)))
  :resulttype vl-paramdecllist-p)

(define vl-run-paramdecltest ((test vl-paramdecltest-p)
                              (config vl-loadconfig-p))
  (b* (((vl-paramdecltest test) test)
       (tokens   (make-test-tokens test.input))
       (pstate   (make-vl-parsestate :warnings 'blah-warnings))
       (atts     '(("blah")))
       (- (cw "~|-----~%Parsing as ~x0: ~s1~%" (vl-loadconfig->edition config) test.input))
       ((mv err val ?tokens (vl-parsestate pstate))
        (vl-parse-param-or-localparam-declaration-top atts '(:vl-kwd-parameter :vl-kwd-localparam)))
       ((when err)
        (if test.successp
            (raise "Expected successful test but got error: ~s0" err)
          (prog2$ (cw "ERR: ~x0.~%" err) t)))
       (pretty (vl-pretty-paramdecls val))
       (- (cw "VAL: ~x0.~%" val))
       (- (cw "Pretty value: ~x0.~%" pretty))
       (- (cw "Expected:     ~x0.~%" test.expect))
       (- (or (equal pstate.warnings 'blah-warnings)
              (raise "warnings aren't right?")))
       ((unless test.successp)
        (or err
            (raise "Expected failure, but no error.~%"))))
    (or (equal pretty test.expect)
        (raise "Pretty value not as expected."))))

(define vl-run-paramdecltests ((tests vl-paramdecltestlist-p)
                               (config vl-loadconfig-p))
  (or (atom tests)
      (and (vl-run-paramdecltest (car tests) config)
           (vl-run-paramdecltests (cdr tests) config))))


(progn

  (defconst *basic-tests*
    (list

     ;; Basic tests for implicitly/partially typed value parameters
     (make-vl-paramdecltest :input "" :successp nil)
     (make-vl-paramdecltest :input "a" :successp nil)
     (make-vl-paramdecltest :input "3" :successp nil)
     (make-vl-paramdecltest :input "hello = 1" :successp nil)

     (make-vl-paramdecltest :input "parameter" :successp nil)
     (make-vl-paramdecltest :input "localparam" :successp nil)

     ;; Local parameters are required to have default value expressions
     (make-vl-paramdecltest :input "localparam a" :successp nil)
     (make-vl-paramdecltest :input "localparam a, b" :successp nil)


     ;; Some tests with default values
     (make-vl-paramdecltest :input "parameter a = 1"
                            :expect '(("a" :implicit = 1)))

     (make-vl-paramdecltest :input "localparam a = 1"
                            :expect '(("a" :local :implicit = 1)))

     (make-vl-paramdecltest :input "localparam a = 1, b" ;; b must have a default value
                            :successp nil)

     (make-vl-paramdecltest :input "parameter a = 1, b = 2"
                            :expect '(("a" :implicit = 1)
                                      ("b" :implicit = 2)))

     (make-vl-paramdecltest :input "parameter a = 1, b = 2"
                            :expect '(("a" :implicit = 1)
                                      ("b" :implicit = 2)))

     (make-vl-paramdecltest :input "localparam a = 1, b = 2"
                            :expect '(("a" :local :implicit = 1)
                                      ("b" :local :implicit = 2)))

     (make-vl-paramdecltest :input "parameter a = 1 : 2 : 3"
                            :expect '(("a" :implicit = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "localparam a = 1 : 2 : 3"
                            :expect '(("a" :local :implicit = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "localparam a = 1, b = 1 : 2 : 3"
                            :expect '(("a" :local :implicit = 1)
                                      ("b" :local :implicit = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "localparam signed a = 1, b = 1 : 2 : 3"
                            :expect '(("a" :local :implicit :vl-signed = 1)
                                      ("b" :local :implicit :vl-signed = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "localparam signed a = 1, c, b = 1 : 2 : 3" ;; c has no default value
                            :successp nil)

     (make-vl-paramdecltest :input "localparam signed [7:8] a = 1, b = 1 : 2 : 3"
                            :expect '(("a" :local :implicit :vl-signed (:range 7 8) = 1)
                                      ("b" :local :implicit :vl-signed (:range 7 8) = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "localparam [7:8] signed a = 1, b = 1 : 2 : 3" ;; signed must come before range
                            :successp nil)

     (make-vl-paramdecltest :input "parameter [7:8] unsigned a" ;; unsigned must come before range
                            :successp nil)


     (make-vl-paramdecltest :input "parameter [7:8] a = 1, b = 1 : 2 : 3"
                            :expect '(("a" :implicit (:range 7 8) = 1)
                                      ("b" :implicit (:range 7 8) = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "localparam [7:8] a = 1, b = 1 : 2 : 3"
                            :expect '(("a" :local :implicit (:range 7 8) = 1)
                                      ("b" :local :implicit (:range 7 8) = (:vl-mintypmax nil 1 2 3))))


     ;; Special types that are supported in both Verilog-2005 and SystemVerilog-2012.
     (make-vl-paramdecltest :input "parameter integer a = 1, b = 2"
                            :expect '(("a" :explicit (:vl-integer signed) = 1)
                                      ("b" :explicit (:vl-integer signed) = 2)))

     (make-vl-paramdecltest :input "parameter integer [7:0] a = 1, b = 2" ;; no ranges on integer
                            :successp nil)

     (make-vl-paramdecltest :input "parameter [7:0] integer a = 1, b = 2" ;; no ranges on integer
                            :successp nil)



     (make-vl-paramdecltest :input "parameter real a = 1, b = 2"
                            :expect '(("a" :explicit (:vl-real unsigned) = 1)
                                      ("b" :explicit (:vl-real unsigned) = 2)))

     (make-vl-paramdecltest :input "parameter real [7:0] a = 1, b = 2" ;; no ranges on real
                            :successp nil)

     (make-vl-paramdecltest :input "parameter [7:0] real a = 1, b = 2" ;; no ranges on real
                            :successp nil)

     (make-vl-paramdecltest :input "parameter real signed a = 1, b = 2" ;; no signed for real
                            :successp nil)

     (make-vl-paramdecltest :input "parameter signed real a = 1, b = 2" ;; no signed for real
                            :successp nil)



     (make-vl-paramdecltest :input "parameter time a = 1, b = 2"
                            :expect '(("a" :explicit (:vl-time unsigned) = 1)
                                      ("b" :explicit (:vl-time unsigned) = 2)))

     (make-vl-paramdecltest :input "parameter time [7:0] a = 1, b = 2" ;; no ranges on time
                            :successp nil)

     (make-vl-paramdecltest :input "parameter [7:0] time a = 1, b = 2" ;; no ranges on time
                            :successp nil)


     (make-vl-paramdecltest :input "parameter realtime a = 1, b = 2"
                            :expect '(("a" :explicit (:vl-realtime unsigned) = 1)
                                      ("b" :explicit (:vl-realtime unsigned) = 2)))

     (make-vl-paramdecltest :input "parameter realtime [7:0] a = 1, b = 2" ;; no ranges on realtime
                            :successp nil)

     (make-vl-paramdecltest :input "parameter [7:0] realtime a = 1, b = 2" ;; no ranges on realtime
                            :successp nil)

     (make-vl-paramdecltest :input "parameter foo_t = 1"
                            :expect '(("foo_t" :implicit = 1)))

     ))

  (assert! (vl-run-paramdecltests *basic-tests* (make-vl-loadconfig :edition :system-verilog-2012)))
  (assert! (vl-run-paramdecltests *basic-tests* (make-vl-loadconfig :edition :verilog-2005)))

  (defconst *sysv-only-tests*
    ;; Tests that should work in SystemVerilog but not in Verilog-2005.
    (list

     ;; In SystemVerilog, global parameters are not required to have default
     ;; values:

     (make-vl-paramdecltest :input "parameter a"
                            :expect '(("a" :implicit)))

     (make-vl-paramdecltest :input "parameter a [1:0]"
                            :expect '(("a" :explicit (:vl-logic unsigned :udims (:range 1 0)))))

     (make-vl-paramdecltest :input "parameter a, b"
                            :expect '(("a" :implicit)
                                      ("b" :implicit)))

     (make-vl-paramdecltest :input "parameter a, b [1:0][2:0]"
                            :expect '(("a" :implicit)
                                      ("b" :explicit (:vl-logic unsigned :udims (:range 1 0) (:range 2 0)))))

     (make-vl-paramdecltest :input "parameter a = 1, b"
                            :expect '(("a" :implicit = 1)
                                      ("b" :implicit)))

     (make-vl-paramdecltest :input "parameter a = 1, b = 1 : 2 : 3, c"
                            :expect '(("a" :implicit = 1)
                                      ("b" :implicit = (:vl-mintypmax nil 1 2 3))
                                      ("c" :implicit)))

     (make-vl-paramdecltest :input "parameter signed a = 1, c, b = 1 : 2 : 3"
                            :expect '(("a" :implicit :vl-signed = 1)
                                      ("c" :implicit :vl-signed)
                                      ("b" :implicit :vl-signed = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "parameter signed a = 1, c[1:0], b = 1 : 2 : 3"
                            :expect '(("a" :implicit :vl-signed = 1)
                                      ("c" :explicit (:vl-logic signed :udims (:range 1 0)))
                                      ("b" :implicit :vl-signed = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "parameter [7:8] a = 1, c[1:0], b = 1 : 2 : 3"
                            :expect '(("a" :implicit (:range 7 8) = 1)
                                      ("c" :explicit (:vl-logic unsigned (:range 7 8) :udims (:range 1 0)))
                                      ("b" :implicit (:range 7 8) = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "parameter signed [7:8] a = 1, c, b = 1 : 2 : 3"
                            :expect '(("a" :implicit :vl-signed (:range 7 8) = 1)
                                      ("c" :implicit :vl-signed (:range 7 8))
                                      ("b" :implicit :vl-signed (:range 7 8) = (:vl-mintypmax nil 1 2 3))))

     (make-vl-paramdecltest :input "parameter integer a = 1, b = 2, c"
                            :expect '(("a" :explicit (:vl-integer signed) = 1)
                                      ("b" :explicit (:vl-integer signed) = 2)
                                      ("c" :explicit (:vl-integer signed))))



     ;; In SystemVerilog the signing can also be 'unsigned', which isn't permitted in Verilog-2005.
     (make-vl-paramdecltest :input "parameter unsigned a"
                            :expect '(("a" :implicit :vl-unsigned)))

     (make-vl-paramdecltest :input "parameter unsigned [7:0] a"
                            :expect '(("a" :implicit :vl-unsigned (:range 7 0))))

     (make-vl-paramdecltest :input "parameter unsigned [7:0] a [1:0]"
                            :expect '(("a" :explicit (:vl-logic unsigned (:range 7 0) :udims (:range 1 0)))))

     (make-vl-paramdecltest :input "parameter unsigned [7:0] a, b = 3"
                            :expect '(("a" :implicit :vl-unsigned (:range 7 0))
                                      ("b" :implicit :vl-unsigned (:range 7 0) = 3)))

     (make-vl-paramdecltest :input "parameter unsigned [7:0] a, b[1:0] = 3"
                            :expect '(("a" :implicit :vl-unsigned (:range 7 0))
                                      ("b" :explicit (:vl-logic unsigned (:range 7 0) :udims (:range 1 0)) = 3)))


     ;; In SystemVerilog the rhs can be a dollar sign.
     (make-vl-paramdecltest :input "parameter a = $"
                            :expect '(("a" :implicit = (key :vl-$))))


     ;; In SystemVerilog the parameters can be of arbitrary data types.

     (make-vl-paramdecltest :input "parameter foo_t a = 1"
                            :expect '(("a" :explicit (:vl-usertype "foo_t") = 1)))

     (make-vl-paramdecltest :input "parameter foo_t a[1:0] = 1"
                            :expect '(("a" :explicit (:vl-usertype "foo_t" :udims (:range 1 0)) = 1)))

     (make-vl-paramdecltest :input "parameter foo_t a = 1, b"
                            :expect '(("a" :explicit (:vl-usertype "foo_t") = 1)
                                      ("b" :explicit (:vl-usertype "foo_t"))))

     (make-vl-paramdecltest :input "parameter struct { int field; } a = 1"
                            :expect '(("a" :explicit (:vl-struct ("field" :vl-int signed)) = 1)))

     (make-vl-paramdecltest :input "parameter struct { int field; } a = 1, b, c = 2"
                            :expect '(("a" :explicit (:vl-struct ("field" :vl-int signed)) = 1)
                                      ("b" :explicit (:vl-struct ("field" :vl-int signed)))
                                      ("c" :explicit (:vl-struct ("field" :vl-int signed)) = 2)))


     ))

  (assert! (vl-run-paramdecltests *sysv-only-tests*
                                  (make-vl-loadconfig :edition :system-verilog-2012)))

  (assert! (vl-run-paramdecltests (make-paramdecltests-fail *sysv-only-tests*)
                                  (make-vl-loadconfig :edition :verilog-2005))))

#||
(defmacro trace-parser (fn)
  `(trace$ (,fn
            :entry (list ',fn
                         :tokens (vl-tokenlist->string-with-spaces tokens)
                         :pstate pstate)
            :exit (list :errmsg (first values)
                        :val (second values)
                        :remainder (vl-tokenlist->string-with-spaces
                                    (third values))
                        :next-token (and (consp (third values))
                                         (vl-token->type (car (third values))))
                        :pstate (fourth values)))))

(trace-parser vl-parse-param-or-localparam-declaration-fn)
(trace-parser vl-parse-param-assignment-fn)
(trace-parser vl-parse-type-assignment-fn)
(trace-parser vl-parse-datatype-fn)
(trace-parser vl-parse-simple-type-fn)


||#


