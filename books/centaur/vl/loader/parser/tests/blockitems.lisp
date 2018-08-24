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
(include-book "../blockitems")

(defaggregate vl-vardecltest
  ((input    "Input to try to parse." stringp)
   (successp "Should parsing be successful?"
             booleanp
             :default t)
   ;; The rest only matter on success:
   (names    "Names of resulting variable declarations." string-listp)
   (constp   "Expected constp value.  Shared by all variables."
             booleanp
             :default nil)
   (varp     "Expected varp value.  Shared by all variables."
             booleanp
             :default nil)
   (lifetime "Expected lifetime value.  Shared by all variables."
             vl-lifetime-p
             :default nil)
   (type     "Expected pretty-printed data type. Shared by all variables.")
   (atts     "Expected pretty-printed attributes.  Shared by all variables.")
   (dims     "Expected pretty-printed dimension-list.  Unique to each variable."
             (equal (len dims) (len names)))
   (initvals "Expected pretty-printed initial values.  Unique to each variable."
             (equal (len initvals) (len names)))))

(deflist vl-vardecltestlist-p (x)
  (vl-vardecltest-p x))

(define vl-make-vardecltests-fail ((x vl-vardecltestlist-p))
  :returns (failing-x vl-vardecltestlist-p :hyp :fguard)
  (if (atom x)
      nil
    (cons (change-vl-vardecltest (car x) :successp nil)
          (vl-make-vardecltests-fail (cdr x)))))

(define run-vardecltest-aux ((vars     "Values produced by the parser")
                             ;; Expected values
                             (constp   booleanp)
                             (varp     booleanp)
                             (lifetime vl-lifetime-p)
                             (type     "pretty-printed datatype")
                             (atts     "pretty-printed atts")
                             (names    string-listp)
                             (dims     "pretty-printed dimensions" (same-lengthp names dims))
                             (initvals "pretty-printed initial values" (same-lengthp names initvals)))
  :returns (okp booleanp)
  (b* (((when (or (atom vars) (atom names)))
        (if (and (atom vars)
                 (atom names))
            t
          (cw "Didn't get the right number of variables.~% ~
                - Remaining vars: ~x0~% ~
                - Remaining names: ~x1~%"
              vars names)))
       (v1 (car vars))
       ((unless (vl-vardecl-p v1))
        (cw "Not even a valid variable decl: ~x0." v1))
       ((vl-vardecl v1) v1))
    (debuggable-and (not (cw "Inspecting ~x0.~%" (car vars)))
                    (equal (car names)    v1.name)
                    (equal (car initvals) (and v1.initval (vl-pretty-rhs v1.initval)))
                    (equal constp         v1.constp)
                    (equal varp           v1.varp)
                    (equal lifetime       v1.lifetime)
                    (let ((type (append-without-guard
                                 type (and (car dims) (cons ':udims (car dims))))))
                      (or (equal type
                                 (vl-pretty-datatype v1.type))
                          (cw "type -- spec: ~x0 actual: ~x1~%"
                              type (vl-pretty-datatype v1.type))))
                    (equal atts           v1.atts)
                    (run-vardecltest-aux (cdr vars)
                                         constp varp lifetime type atts
                                         (cdr names)
                                         (cdr dims)
                                         (cdr initvals)))))

(define run-vardecltest ((vars "Values produced by the parser")
                         (test vl-vardecltest-p "Test to run."))
  :returns (okp booleanp)
  (b* (((vl-vardecltest test) test))
    (run-vardecltest-aux vars
                         test.constp
                         test.varp
                         test.lifetime
                         test.type
                         test.atts
                         test.names
                         test.dims
                         test.initvals)))

(defparser-top vl-parse-block-item-declaration)

(define test-parse-block-item-declaration-1 ((test vl-vardecltest-p)
                                             (config vl-loadconfig-p))
  :returns (okp booleanp)
  (b* (((vl-vardecltest test) test)
       (tokens   (make-test-tokens test.input))
       (pstate   (make-vl-parsestate :warnings 'blah-warnings))
       (- (cw "-------~%"))
       (- (cw "Testing block item parsing, using edition ~s0.~%" (vl-loadconfig->edition config)))
       (- (cw "Input: ~s0~%" test.input))
       (- (cw "Expect ~s0.~%" (if test.successp "success" "failure")))
       ((mv err vars ?tokens (vl-parsestate pstate)) (vl-parse-block-item-declaration-top))
       ((when err)
        (cw "Parsing reports an error: ~x0.~%" err)
        (and (not test.successp)
             (equal pstate.warnings 'blah-warnings)
             (not (cw "Test successful.~%")))))

    (cw "Parsing reports success: ~x0.~%" vars)
    (debuggable-and test.successp
                    (equal pstate.warnings 'blah-warnings)
                    (run-vardecltest vars test)
                    (not (cw "Test successful.~%")))))

(define test-parse-block-item-declaration ((tests vl-vardecltestlist-p)
                                           (config vl-loadconfig-p))
  :returns (okp booleanp)
  (if (atom tests)
      t
    (and (test-parse-block-item-declaration-1 (car tests) config)
         (test-parse-block-item-declaration (cdr tests) config))))





(progn

  (defconst *common-tests*
    ;; Tests that should behave the same on Verilog-2005 and SystemVerilog-2012.

    (list
     (make-vl-vardecltest :input "integer a, ; "  :successp nil)
     (make-vl-vardecltest :input "integer ; "     :successp nil)
     (make-vl-vardecltest :input "integer a = "   :successp nil)
     (make-vl-vardecltest :input "integer a = ; " :successp nil)

     (make-vl-vardecltest :input "integer a ; "
                          :type     '(:vl-integer signed)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input "integer a, b, c; "
                          :type     '(:vl-integer signed)
                          :names    '("a" "b" "c")
                          :dims     '(nil nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input "integer a[1:2], b, c; "
                          :type     '(:vl-integer signed)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2)) nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input "integer a[1:2][3:4], b, c; "
                          :type     '(:vl-integer signed)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil nil nil))


     (make-vl-vardecltest :input "real a, ; "  :successp nil)
     (make-vl-vardecltest :input "real ; "     :successp nil)
     (make-vl-vardecltest :input "real a = "   :successp nil)
     (make-vl-vardecltest :input "real a = ; " :successp nil)

     (make-vl-vardecltest :input    "real a ; "
                          :type     '(:vl-real unsigned)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "real a, b, c; "
                          :type     '(:vl-real unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(nil nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    "real a[1:2], b, c; "
                          :type     '(:vl-real unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2)) nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    "real a[1:2][3:4], b, c; "
                          :type     '(:vl-real unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil nil nil))


     (make-vl-vardecltest :input "time a, ; "  :successp nil)
     (make-vl-vardecltest :input "time ; "     :successp nil)
     (make-vl-vardecltest :input "time a = "   :successp nil)
     (make-vl-vardecltest :input "time a = ; " :successp nil)

     (make-vl-vardecltest :input    '"time a ; "
                          :type     '(:vl-time unsigned)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    '"time a, b, c; "
                          :type     '(:vl-time unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(nil nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    '"time a[1:2], b, c; "
                          :type     '(:vl-time unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2)) nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    '"time a[1:2][3:4], b, c; "
                          :type     '(:vl-time unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil nil nil))


     (make-vl-vardecltest :input "realtime a, ; "  :successp nil)
     (make-vl-vardecltest :input "realtime ; "     :successp nil)
     (make-vl-vardecltest :input "realtime a = "   :successp nil)
     (make-vl-vardecltest :input "realtime a = ; " :successp nil)

     (make-vl-vardecltest :input    "realtime a ; "
                          :type     '(:vl-realtime unsigned)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "realtime a, b, c; "
                          :type     '(:vl-realtime unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(nil nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    "realtime a[1:2], b, c; "
                          :type     '(:vl-realtime unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2)) nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    "realtime a[1:2][3:4], b, c; "
                          :type     '(:vl-realtime unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil nil nil))



     (make-vl-vardecltest :input "reg a, ; "  :successp nil)
     (make-vl-vardecltest :input "reg ; "     :successp nil)
     (make-vl-vardecltest :input "reg a = "   :successp nil)
     (make-vl-vardecltest :input "reg a = ; " :successp nil)

     (make-vl-vardecltest :input    "reg a ; "
                          :type     '(:vl-reg unsigned)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "reg signed a ; "
                          :type     '(:vl-reg signed)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "reg [1:3] a ; "
                          :type     '(:vl-reg unsigned (:range 1 3))
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "reg signed [1:3] a ; "
                          :type     '(:vl-reg signed (:range 1 3))
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "reg signed [1:3] a, b, c; "
                          :type     '(:vl-reg signed (:range 1 3))
                          :names    '("a" "b" "c")
                          :dims     '(nil nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    "reg a[1:2], b, c; "
                          :names    '("a" "b" "c")
                          :type     '(:vl-reg unsigned)
                          :dims     '(((:range 1 2)) nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    "reg signed a[1:2][3:4], b, c; "
                          :names    '("a" "b" "c")
                          :type     '(:vl-reg signed)
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil nil nil))


     (make-vl-vardecltest :input "event a, ; "  :successp nil)
     (make-vl-vardecltest :input "event ; "     :successp nil)
     (make-vl-vardecltest :input "event a = "   :successp nil)

     (make-vl-vardecltest :input    "event a ; "
                          :type     '(:vl-event unsigned)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "event a, b, c ; "
                          :type     '(:vl-event unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(nil nil nil)
                          :initvals '(nil nil nil))

     (make-vl-vardecltest :input    "event a[3:4][5:6], b[1:2], c ; "
                          :type     '(:vl-event unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 3 4) (:range 5 6))
                                      ((:range 1 2))
                                      nil)
                          :initvals '(nil nil nil))

     ;; Not legal to do implicit things without 'var'
     (make-vl-vardecltest :input "a" :successp nil)
     (make-vl-vardecltest :input "a;" :successp nil)
     (make-vl-vardecltest :input "a = 1;" :successp nil)
     (make-vl-vardecltest :input "unsigned a;" :successp nil)
     (make-vl-vardecltest :input "unsigned a = 1;" :successp nil)
     (make-vl-vardecltest :input "signed a;" :successp nil)
     (make-vl-vardecltest :input "signed a = 1;" :successp nil)
     (make-vl-vardecltest :input "[3:0] a;" :successp nil)
     (make-vl-vardecltest :input "signed [3:0] a;" :successp nil)
     (make-vl-vardecltest :input "unsigned [3:0] a;" :successp nil)
     (make-vl-vardecltest :input "[3:0] a = 1;" :successp nil)
     (make-vl-vardecltest :input "signed [3:0] a = 1;" :successp nil)
     (make-vl-vardecltest :input "unsigned [3:0] a = 1;" :successp nil)

     (make-vl-vardecltest :input "var const a = 5;" :successp nil) ;; const must come first
     (make-vl-vardecltest :input "var const unsigned a = 5;" :successp nil) ;; const must come first
     (make-vl-vardecltest :input "var const signed a = 5;" :successp nil) ;; const must come first
     (make-vl-vardecltest :input "signed var a = 5;" :successp nil) ;; var must come first
     (make-vl-vardecltest :input "unsigned var a = 5;" :successp nil) ;; var must come first
     (make-vl-vardecltest :input "var [3:0] signed a = 5;" :successp nil) ;; signed must come first
     (make-vl-vardecltest :input "var [3:0] unsigned a = 5;" :successp nil) ;; signed must come first
     (make-vl-vardecltest :input "var signed unsigned a = 5;" :successp nil) ;; can't use signed and unsigned together
     (make-vl-vardecltest :input "var automatic static a = 5;" :successp nil) ;; can't use automatic with static
     (make-vl-vardecltest :input "var automatic automatic a = 5;" :successp nil) ;; can't use automatic twice
     (make-vl-vardecltest :input "var static static a = 5;" :successp nil) ;; can't use static twice

     ;; must have a var keyword to use implicit
     (make-vl-vardecltest :input "const a;" :successp nil)
     (make-vl-vardecltest :input "const automatic a;" :successp nil)
     (make-vl-vardecltest :input "const signed a;" :successp nil)
     (make-vl-vardecltest :input "const unsigned a;" :successp nil)
     (make-vl-vardecltest :input "const [3:0] a;" :successp nil)
     (make-vl-vardecltest :input "automatic a;" :successp nil)
     (make-vl-vardecltest :input "automatic automatic a;" :successp nil)
     (make-vl-vardecltest :input "automatic signed a;" :successp nil)
     (make-vl-vardecltest :input "automatic unsigned a;" :successp nil)
     (make-vl-vardecltest :input "automatic [3:0] a;" :successp nil)
     (make-vl-vardecltest :input "static a;" :successp nil)
     (make-vl-vardecltest :input "static static a;" :successp nil)
     (make-vl-vardecltest :input "static signed a;" :successp nil)
     (make-vl-vardecltest :input "static unsigned a;" :successp nil)
     (make-vl-vardecltest :input "static [3:0] a;" :successp nil)

     ))


  (defconst *sysv-only-tests*
    ;; Tests that should succeed on SystemVerilog-2012 but not on Verilog-2005.

    (list
     ;; Verilog-2005 doesn't allow initial values on block items
     (make-vl-vardecltest :input    "integer a[1:2][3:4], b = 5, c = 17 + 8; "
                          :type     '(:vl-integer signed)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil 5 (:vl-binary-plus nil 17 8)))

     (make-vl-vardecltest :input    "real a[1:2][3:4], b = 5, c = 17 + 8; "
                          :type     '(:vl-real unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil 5 (:vl-binary-plus nil 17 8)))

     (make-vl-vardecltest :input    "time a[1:2][3:4], b = 5, c = 17 + 8; "
                          :type     '(:vl-time unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil 5 (:vl-binary-plus nil 17 8)))

     (make-vl-vardecltest :input    "realtime a[1:2][3:4], b = 5, c = 17 + 8; "
                          :type     '(:vl-realtime unsigned)
                          :names    '("a" "b" "c")
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil 5 (:vl-binary-plus nil 17 8)))

     (make-vl-vardecltest :input    "reg [7:0] a[1:2][3:4], b = 5, c = 17 + 8; "
                          :names    '("a" "b" "c")
                          :type     '(:vl-reg unsigned (:range 7 0))
                          :dims     '(((:range 1 2) (:range 3 4)) nil nil)
                          :initvals '(nil 5 (:vl-binary-plus nil 17 8)))


     ;; In Verilog-2005, events can't be assigned initial values, but in
     ;; SystemVerilog this is legal, e.g., Section 6.17 shows events being
     ;; assigned to null and other events.
     (make-vl-vardecltest :input    "event a = 1;"
                          :type     '(:vl-event unsigned)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(1))


     (make-vl-vardecltest :input    "var a;"
                          :type     '(:vl-logic unsigned)
                          :varp     t
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "var a = 5;"
                          :type     '(:vl-logic unsigned)
                          :varp     t
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(5))

     (make-vl-vardecltest :input    "var unsigned a = 5;"
                          :type     '(:vl-logic unsigned)
                          :varp     t
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(5))

     (make-vl-vardecltest :input    "var signed a = 5;"
                          :type     '(:vl-logic signed)
                          :varp     t
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(5))

     (make-vl-vardecltest :input    "const var signed a = 5;"
                          :type     '(:vl-logic signed)
                          :constp   t
                          :varp     t
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(5))

     (make-vl-vardecltest :input    "var automatic a;"
                          :type     '(:vl-logic unsigned)
                          :varp     t
                          :lifetime :vl-automatic
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "var static a;"
                          :type     '(:vl-logic unsigned)
                          :varp     t
                          :lifetime :vl-static
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))


     (make-vl-vardecltest :input    "var logic a;"
                          :type     '(:vl-logic unsigned)
                          :varp     t
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "const var automatic logic signed [3:0] a;"
                          :type     '(:vl-logic signed (:range 3 0))
                          :varp     t
                          :constp   t
                          :lifetime :vl-automatic
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "const var automatic logic signed [3:0][4:0] a;"
                          :type     '(:vl-logic signed (:range 3 0) (:range 4 0))
                          :varp     t
                          :constp   t
                          :lifetime :vl-automatic
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "const var static logic signed [3:0][4:0] a [5:0] = 6, b = 1, c[7:0][8:0];"
                          :type     '(:vl-logic signed (:range 3 0) (:range 4 0))
                          :varp     t
                          :constp   t
                          :lifetime :vl-static
                          :names    '("a"         "b"      "c")
                          :dims     '(((:range 5 0)) nil ((:range 7 0) (:range 8 0)))
                          :initvals '(6            1        nil))

     (make-vl-vardecltest :input    "logic a;"
                          :type     '(:vl-logic unsigned)
                          :names    '("a")
                          :dims     '(nil)
                          :initvals '(nil))

     (make-vl-vardecltest :input    "automatic logic a [3:0];"
                          :type     '(:vl-logic unsigned)
                          :lifetime :vl-automatic
                          :names    '("a")
                          :dims     '(((:range 3 0)))
                          :initvals '(nil))

     (make-vl-vardecltest :input    "automatic struct { int a; shortreal b; } c [3:0], d;"
                          :type     '(:vl-struct
                                      ("a" :vl-int signed)
                                      ("b" :vl-shortreal unsigned))
                          :lifetime :vl-automatic
                          :names    '("c" "d")
                          :dims     '(((:range 3 0)) nil)
                          :initvals '(nil nil))

     ))


  (value-triple (cw "   ============= Running common tests ============== ~%"))
  (assert! (test-parse-block-item-declaration *common-tests*
                                              (make-vl-loadconfig :edition :system-verilog-2012)))
  (assert! (test-parse-block-item-declaration *common-tests*
                                              (make-vl-loadconfig :edition :verilog-2005)))

  (value-triple (cw "   ============= Running sysv only tests ============== ~%"))
  (assert! (test-parse-block-item-declaration *sysv-only-tests*
                                              (make-vl-loadconfig :edition :system-verilog-2012)))
  (assert! (test-parse-block-item-declaration (vl-make-vardecltests-fail *sysv-only-tests*)
                                              (make-vl-loadconfig :edition :verilog-2005)))

  (value-triple (cw "   ============= Done with all tests ============== ~%"))

  )


; BOZO deal with these somehow.  We're not allowed to have a range plus an
; initial value on these declarations.  But we want to be checking this for
; module variable declaration parsing, instead of block item declarations,
; where no initial values are allowed anyway.



;; (test-parse-block-item-declaration
;;  (list
;;   (make-vl-vardecltest :input "integer a[1:2] = 17 ; "  :successp nil)
;;   (make-vl-vardecltest :input "real a[1:2] = 17 ; "     :successp nil)
;;   (make-vl-vardecltest :input "reg a[1:2] = 17 ; "      :successp nil)
;;   (make-vl-vardecltest :input "time a[1:2] = 17 ; "     :successp nil)
;;   (make-vl-vardecltest :input "realtime a[1:2] = 17 ; " :successp nil))
;;  (make-vl-loadconfig :edition :verilog-2005))


