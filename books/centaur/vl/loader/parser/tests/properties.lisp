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
(include-book "../properties")
(include-book "../../../mlib/writer")
(include-book "../../../mlib/strip")


(defparser-top vl-parse-expression-or-dist :resulttype vl-exprdist-p)

(defmacro test-exprdist (&key input expect (successp 't) (extra 'nil))
  `(assert! (b* ((config *vl-default-loadconfig*)
                 (tokens (make-test-tokens ,input))
                 (pstate (make-vl-parsestate))
                 ((mv erp val ?tokens (vl-parsestate pstate))
                  (vl-parse-expression-or-dist-top))
                 ((when erp)
                  (cw "ERP is ~x0.~%" erp)
                  (not ,successp)))
              (cw "VAL is ~x0.~%" val)
              (and ,successp
                   (vl-exprdist-p val)
                   (not pstate.warnings)
                   (or ',extra
                       (not tokens)
                       (cw "Extra tokens not expected?"))
                   (or (equal ',expect (vl-pretty-exprdist val))
                       (cw "Expected ~x0~%" ',expect)
                       (cw "Got:     ~x0~%" (vl-pretty-exprdist val)))))))

(test-exprdist :input ""
               :successp nil)

(test-exprdist :input "a"
               :expect (id "a"))

(test-exprdist :input "a + b"
               :expect (:vl-binary-plus nil (id "a") (id "b")))

(test-exprdist :input "a dist"     ;; not even {}
               :successp nil)

(test-exprdist :input "a dist {}"  ;; need at least one expr
               :successp nil)

(test-exprdist :input "a dist { 5 }"
               :expect (:dist (id "a") (5 := 1)))

(test-exprdist :input "a dist { 5, 9 }"
               :expect (:dist (id "a") (5 := 1) (9 := 1)))

(test-exprdist :input "a dist { 5, 9, }"  ;; extra comma
               :successp nil)

(test-exprdist :input "a dist { 5, 9 "  ;; forgot closing
               :successp nil)

(test-exprdist :input "a dist { 5, 9 := 2}"
               :expect (:dist (id "a") (5 := 1) (9 := 2)))

(test-exprdist :input "a dist { 5 := 6, 9 := 2}"
               :expect (:dist (id "a") (5 := 6) (9 := 2)))

(test-exprdist :input "a dist { [5:6] }"
               :expect (:dist (id "a") (5 6 := 1)))

(test-exprdist :input "a dist { [5:6] := 3}"
               :expect (:dist (id "a") (5 6 := 3)))

(test-exprdist :input "a dist { [5:6] := 3, 100 := 4}"
               :expect (:dist (id "a") (5 6 := 3) (100 := 4)))

(test-exprdist :input "a dist { [5:6] := 3, [100:102] := 4}"
               :expect (:dist (id "a") (5 6 := 3) (100 102 := 4)))

(test-exprdist :input "a dist { [5:6] := 3, [c:d] := 4}"
               :expect (:dist (id "a")
                        (5 6 := 3)
                        ((id "c") (id "d") := 4)))

(test-exprdist :input "a dist { 5 :/ 3 }"
               :expect (:dist (id "a") (5 :/ 3)))

(test-exprdist :input "a dist { 5 :/ 3, }" ;; extra comma
               :successp nil)

(test-exprdist :input "a dist { [5:6] := 3, 100 :/ 4}"
               :expect (:dist (id "a") (5 6 := 3) (100 :/ 4)))

(test-exprdist :input "a dist { [5:6] :/ 3, 100 :/ 4}"
               :expect (:dist (id "a") (5 6 :/ 3) (100 :/ 4)))





(defparser-top vl-parse-cycledelayrange :resulttype vl-range-p)

(defmacro test-cycledelayrange (&key input expect (successp 't) (extra 'nil))
  `(assert! (b* ((config *vl-default-loadconfig*)
                 (tokens (make-test-tokens ,input))
                 (pstate (make-vl-parsestate))
                 ((mv erp val ?tokens (vl-parsestate pstate))
                  (vl-parse-cycledelayrange-top))
                 ((when erp)
                  (cw "ERP is ~x0.~%" erp)
                  (not ,successp)))
              (cw "VAL is ~x0.~%" val)
              (and ,successp
                   (vl-range-p val)
                   (not pstate.warnings)
                   (or ',extra
                       (not tokens)
                       (cw "Extra tokens not expected?"))
                   (or (equal ',expect (vl-pretty-range val))
                       (cw "Expected ~x0~%" ',expect)
                       (cw "Got:     ~x0~%" (vl-pretty-range val)))))))

(test-cycledelayrange :input "" :successp nil)
(test-cycledelayrange :input "#" :successp nil)
(test-cycledelayrange :input "##" :successp nil)
(test-cycledelayrange :input "##[" :successp nil)
(test-cycledelayrange :input "##[3" :successp nil)
(test-cycledelayrange :input "##[3:4" :successp nil)
(test-cycledelayrange :input "##[3]" :successp nil)

(test-cycledelayrange :input "##3" :expect (:range 3 3))
(test-cycledelayrange :input "##a" :expect (:range (id "a") (id "a")))

(test-cycledelayrange :input "##[3:4]" :expect (:range 3 4))
(test-cycledelayrange :input "##[3:$]" :expect (:range 3 (key :vl-$)))

;; BOZO it's not clear to me whether whitespace should be allowed here.  We
;; should probably compare this to what other Verilog tools support.
(test-cycledelayrange :input "##[+]"    :expect (:range 1 (key :vl-$)))
(test-cycledelayrange :input "##[+ ]"   :expect (:range 1 (key :vl-$)))
(test-cycledelayrange :input "##[ +]"   :expect (:range 1 (key :vl-$)))
(test-cycledelayrange :input "##[ + ]"  :expect (:range 1 (key :vl-$)))
(test-cycledelayrange :input "## [+ ]"  :expect (:range 1 (key :vl-$)))
(test-cycledelayrange :input "## [ +]"  :expect (:range 1 (key :vl-$)))
(test-cycledelayrange :input "## [ + ]" :expect (:range 1 (key :vl-$)))

(test-cycledelayrange :input "##[*]"    :expect (:range 0 (key :vl-$)))
(test-cycledelayrange :input "##[* ]"   :expect (:range 0 (key :vl-$)))
(test-cycledelayrange :input "##[ *]"   :expect (:range 0 (key :vl-$)))
(test-cycledelayrange :input "##[ * ]"  :expect (:range 0 (key :vl-$)))
(test-cycledelayrange :input "## [* ]"  :expect (:range 0 (key :vl-$)))
(test-cycledelayrange :input "## [ *]"  :expect (:range 0 (key :vl-$)))
(test-cycledelayrange :input "## [ * ]" :expect (:range 0 (key :vl-$)))

;; BOZO we don't allow space between the #s, is that OK?
(test-cycledelayrange :input "# #[+]" :successp nil)
(test-cycledelayrange :input "# #[*]" :successp nil)



(defparser-top vl-parse-boolean-abbrev :resulttype vl-repetition-p)

(defmacro test-repetition (&key input expect (successp 't) (extra 'nil))
  `(assert! (b* ((config *vl-default-loadconfig*)
                 (tokens (make-test-tokens ,input))
                 (pstate (make-vl-parsestate))
                 ((mv erp val ?tokens (vl-parsestate pstate))
                  (vl-parse-boolean-abbrev-top))
                 ((when erp)
                  (cw "ERP is ~x0.~%" erp)
                  (not ,successp)))
              (cw "VAL is ~x0.~%" val)
              (and ,successp
                   (vl-repetition-p val)
                   (not pstate.warnings)
                   (or ',extra
                       (not tokens)
                       (cw "Extra tokens not expected?"))
                   (or (equal ',expect (vl-pretty-repetition val))
                       (cw "Expected ~x0~%" ',expect)
                       (cw "Got:     ~x0~%" (vl-pretty-repetition val)))))))

(test-repetition :input "" :successp nil)
(test-repetition :input "[]" :successp nil)
(test-repetition :input "[->]" :successp nil)
(test-repetition :input "[=]"  :successp nil)

(test-repetition :input "[*]" :expect (:[*] 0 (key :vl-$)))
(test-repetition :input "[+]" :expect (:[*] 1 (key :vl-$)))

(test-repetition :input "[*3]"   :expect (:[*] 3))
(test-repetition :input "[*3:4]" :expect (:[*] 3 4))
(test-repetition :input "[*3:$]" :expect (:[*] 3 (key :vl-$)))
(test-repetition :input "[* 3]"   :expect (:[*] 3))
(test-repetition :input "[* 3:4]" :expect (:[*] 3 4))
(test-repetition :input "[* 3:$]" :expect (:[*] 3 (key :vl-$)))

(test-repetition :input "[->3]"   :expect (:[->] 3))
(test-repetition :input "[->3:4]" :expect (:[->] 3 4))
(test-repetition :input "[->3:$]" :expect (:[->] 3 (key :vl-$)))
(test-repetition :input "[-> 3]"   :expect (:[->] 3))
(test-repetition :input "[-> 3:4]" :expect (:[->] 3 4))
(test-repetition :input "[-> 3:$]" :expect (:[->] 3 (key :vl-$)))

(test-repetition :input "[=3]"   :expect (:[=] 3))
(test-repetition :input "[=3:4]" :expect (:[=] 3 4))
(test-repetition :input "[=3:$]" :expect (:[=] 3 (key :vl-$)))
(test-repetition :input "[= 3]"   :expect (:[=] 3))
(test-repetition :input "[= 3:4]" :expect (:[=] 3 4))
(test-repetition :input "[= 3:$]" :expect (:[=] 3 (key :vl-$)))


(defparser-top vl-parse-property-expr :resulttype vl-propexpr-p)

(define vl-pps-propexpr ((x vl-propexpr-p))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-propexpr x)))

(define test-prop-prettyprinter-roundtrip ((x vl-propexpr-p))
  (b* ((config *vl-default-loadconfig*)
       (x (vl-propexpr-strip x))
       (pretty-printed (vl-pps-propexpr x))
       (- (cw "Pretty-printed: {{{~%    ")
          (cw-unformatted pretty-printed)
          (cw "~%~%}}}"))
       (tokens (make-test-tokens pretty-printed))
       (pstate (make-vl-parsestate))
       ((mv errmsg val ?tokens (vl-parsestate pstate))
        (vl-parse-property-expr-top))
       (- (cw "Raw ERR is ~x0.~%" errmsg))
       (- (cw "Raw VAL is ~x0.~%" val))
       ((when errmsg)
        (cw "Got an error when parsing back in pretty-printed output!"))
       (val (vl-propexpr-strip val)))
    (and (or (equal val x)
             (cw "Value mismatch when parsing back in pretty-printed output:~%")
             (cw "  Original X: ~x0~%" x)
             (cw "  New Value:  ~x0~%" val)
             (cw "  Pretty-Printed X: ~x0~%" pretty-printed)
             (cw "  Pretty-Printed Val: ~x0~%" (vl-pps-propexpr val)))
         (or (not pstate.warnings)
             (cw "Got warnings when parsing back in pretty-printed output? ~x0~%" pstate.warnings))
         (or (not tokens)
             (cw "Tokens remain after parsing back in pretty-printed output? ~x0~%"
                 tokens)))))


(defmacro test-prop (&key input expect (successp 't) (extra 'nil))
  `(assert! (b* ((- (cw "~% -------- Testing ~s0 ----------- ~%" ',input))
                 (config *vl-default-loadconfig*)
                 (tokens (make-test-tokens ,input))
                 (pstate (make-vl-parsestate))
                 ((mv errmsg val ?tokens (vl-parsestate pstate))
                  (vl-parse-property-expr-top))
                 (- (cw "Raw ERR is ~x0.~%" errmsg))
                 (- (cw "Raw VAL is ~x0.~%" val))
                 (parse-test-okp (if errmsg
                                     (not ,successp)
                                   (and ,successp
                                        (vl-propexpr-p val)
                                        (not pstate.warnings)
                                        (or ',extra
                                            (not tokens)
                                            (cw "Extra tokens not expected?"))
                                        (or (equal ',expect (vl-pretty-propexpr val))
                                            (cw "Expected ~x0~%" ',expect)
                                            (cw "Got:     ~x0~%" (vl-pretty-propexpr val))))))
                 ((unless parse-test-okp)
                  (cw "Test failed!~%"))
                 ((when errmsg)
                  (cw "Skipping pretty-printing test since this test case is of invalid input.")
                  :success))
              (test-prop-prettyprinter-roundtrip val))))


(test-prop :input "" :successp nil)

(test-prop :input "goodp"
           :expect (id "goodp"))

; Note: I think properties can only validly occur before an endproperty,
; closing parenthesis, or semicolon.

(test-prop :input "goodp )"
           :expect (id "goodp")
           :extra ")")

(test-prop :input "goodp endproperty"
           :expect (id "goodp")
           :extra "endproperty")

(test-prop :input "goodp )"
           :expect (id "goodp")
           :extra ";")

(test-prop :input ")" :successp nil)
(test-prop :input "endproperty" :successp nil)
(test-prop :input ";" :successp nil)

(test-prop :input "good dist {1 := 2}"
           :expect (:dist (id "good") (1 := 2)))


;; Basic tests of property expression operators.

(test-prop :input "always good dist {1 := 2}"
           :expect (:always (no-range)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "always (good dist {1 := 2})"
           :expect (:always (no-range)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "(always good dist {1 := 2})"
           :expect (:always (no-range)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "always [1] good dist {1 := 2}"  ;; oops, need a range
           :successp nil)

(test-prop :input "always [1:2] good dist {1 := 2}"
           :expect (:always (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "always [1:2] (good dist {1 := 2})"
           :expect (:always (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "always [1:2] ((((((good dist {1 := 2}))))))"
           :expect (:always (:range 1 2)
                    (:dist (id "good") (1 := 2))))

;; Same tests for s_always.  But s_always requires a range!

(test-prop :input "s_always good dist {1 := 2}"
           :successp nil)

(test-prop :input "s_always (good dist {1 := 2})"
           :successp nil)

(test-prop :input "s_always [1] good dist {1 := 2}"
           :successp nil)

(test-prop :input "s_always [1:2] good dist {1 := 2}"
           :expect (:s_always (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_always [1:2] (good dist {1 := 2})"
           :expect (:s_always (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_always [1:2] ((((((good dist {1 := 2}))))))"
           :expect (:s_always (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_always [1:$] ((((((good dist {1 := 2}))))))"
           :expect (:s_always (:range 1 (key :vl-$))
                    (:dist (id "good") (1 := 2))))


;; Interleave always and s_always

(test-prop :input "s_always [1:2] always good"
           :expect (:s_always (:range 1 2)
                    (:always (no-range) (id "good"))))

(test-prop :input "always [1:2] s_always [3:4] good"
           :expect (:always (:range 1 2)
                    (:s_always (:range 3 4) (id "good"))))

(test-prop :input "always [1:2] (s_always [3:4] good)"
           :expect (:always (:range 1 2)
                    (:s_always (:range 3 4) (id "good"))))

(test-prop :input "(always [1:2] (s_always [3:4] good))"
           :expect (:always (:range 1 2)
                    (:s_always (:range 3 4) (id "good"))))


;; Basic tests for eventually.  Like s_always, eventually requires a range.

(test-prop :input "eventually good dist {1 := 2}"
           :successp nil)

(test-prop :input "eventually (good dist {1 := 2})"
           :successp nil)

(test-prop :input "eventually [1] good dist {1 := 2}"
           :successp nil)

(test-prop :input "eventually [1:2] good dist {1 := 2}"
           :expect (:eventually (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "eventually [1:2] (good dist {1 := 2})"
           :expect (:eventually (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "eventually [1:2] ((((((good dist {1 := 2}))))))"
           :expect (:eventually (:range 1 2)
                    (:dist (id "good") (1 := 2))))


;; Interleave eventually and always

(test-prop :input "eventually [1:2] always good"
           :expect (:eventually (:range 1 2)
                    (:always (no-range) (id "good"))))

(test-prop :input "always [1:2] eventually [3:4] good"
           :expect (:always (:range 1 2)
                    (:eventually (:range 3 4) (id "good"))))

(test-prop :input "always [1:2] (eventually [3:4] good)"
           :expect (:always (:range 1 2)
                    (:eventually (:range 3 4) (id "good"))))

(test-prop :input "(always [1:2] (eventually [3:4] good))"
           :expect (:always (:range 1 2)
                    (:eventually (:range 3 4) (id "good"))))



;; same tests for s_eventually, but the range here is optional

(test-prop :input "s_eventually good dist {1 := 2}"
           :expect (:s_eventually (no-range)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_eventually (good dist {1 := 2})"
           :expect (:s_eventually (no-range)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "(s_eventually good dist {1 := 2})"
           :expect (:s_eventually (no-range)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_eventually [1] good dist {1 := 2}"  ;; oops, need a range
           :successp nil)

(test-prop :input "s_eventually [1:2] good dist {1 := 2}"
           :expect (:s_eventually (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_eventually ([1:2] good dist {1 := 2})" ;; bad parens
           :successp nil)

(test-prop :input "s_eventually [1:2] (good dist {1 := 2})"
           :expect (:s_eventually (:range 1 2)
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_eventually [1:2] ((((((good dist {1 := 2}))))))"
           :expect (:s_eventually (:range 1 2)
                    (:dist (id "good") (1 := 2))))


;; Interleave s_eventually and always

(test-prop :input "s_eventually [1:2] always good"
           :expect (:s_eventually (:range 1 2)
                    (:always (no-range) (id "good"))))

(test-prop :input "always [1:2] s_eventually [3:4] good"
           :expect (:always (:range 1 2)
                    (:s_eventually (:range 3 4) (id "good"))))

(test-prop :input "always [1:2] (s_eventually [3:4] good)"
           :expect (:always (:range 1 2)
                    (:s_eventually (:range 3 4) (id "good"))))

(test-prop :input "(always [1:2] (s_eventually [3:4] good))"
           :expect (:always (:range 1 2)
                    (:s_eventually (:range 3 4) (id "good"))))



;; same testes for s_nexttime.  it takes an optional index instead of an
;; optional range.

(test-prop :input "s_nexttime good dist {1 := 2}"
           :expect (:s_nexttime nil
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_nexttime (good dist {1 := 2})"
           :expect (:s_nexttime nil
                    (:dist (id "good") (1 := 2))))

(test-prop :input "(s_nexttime good dist {1 := 2})"
           :expect (:s_nexttime nil
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_nexttime [1] good dist {1 := 2}"
           :expect (:s_nexttime 1
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_nexttime [1:2] good dist {1 := 2}" ;; oops, index not range!
           :successp nil)

(test-prop :input "s_nexttime [77] (good dist {1 := 2})"
           :expect (:s_nexttime 77
                    (:dist (id "good") (1 := 2))))

(test-prop :input "s_nexttime ([77] (good dist {1 := 2}))" ;; bad parens
           :successp nil)

(test-prop :input "s_nexttime [99] ((((((good dist {1 := 2}))))))"
           :expect (:s_nexttime 99
                    (:dist (id "good") (1 := 2))))


;; Interleave s_nexttime and always.  This is actually really subtle and it's
;; only because of our "handling of not" hack that we should be able to support
;; writing an always after an s_nexttime.

(test-prop :input "s_nexttime always good"
           :expect (:s_nexttime nil
                    (:always (no-range) (id "good"))))

(test-prop :input "s_nexttime [1] always good"
           :expect (:s_nexttime 1
                    (:always (no-range) (id "good"))))

(test-prop :input "always [1:2] s_nexttime [3] good"
           :expect (:always (:range 1 2)
                    (:s_nexttime 3 (id "good"))))

(test-prop :input "always [1:2] (s_nexttime good)"
           :expect (:always (:range 1 2)
                    (:s_nexttime nil (id "good"))))

(test-prop :input "(always [1:2] (s_nexttime [3] good))"
           :expect (:always (:range 1 2)
                    (:s_nexttime 3 (id "good"))))



;; same tests for nexttime.  like s_nexttime it takes an optional index.

(test-prop :input "nexttime good dist {1 := 2}"
           :expect (:nexttime nil
                    (:dist (id "good") (1 := 2))))

(test-prop :input "nexttime (good dist {1 := 2})"
           :expect (:nexttime nil
                    (:dist (id "good") (1 := 2))))

(test-prop :input "(nexttime good dist {1 := 2})"
           :expect (:nexttime nil
                    (:dist (id "good") (1 := 2))))

(test-prop :input "nexttime [1] good dist {1 := 2}"
           :expect (:nexttime 1
                    (:dist (id "good") (1 := 2))))

(test-prop :input "nexttime [1:2] good dist {1 := 2}" ;; oops, index not range!
           :successp nil)

(test-prop :input "nexttime [77] (good dist {1 := 2})"
           :expect (:nexttime 77
                    (:dist (id "good") (1 := 2))))

(test-prop :input "nexttime [99] ((((((good dist {1 := 2}))))))"
           :expect (:nexttime 99
                    (:dist (id "good") (1 := 2))))


;; interleave nexttime and always.

(test-prop :input "nexttime always good"
           :expect (:nexttime nil
                    (:always (no-range) (id "good"))))

(test-prop :input "nexttime [1] always good"
           :expect (:nexttime 1
                    (:always (no-range) (id "good"))))

(test-prop :input "always [1:2] nexttime [3] good"
           :expect (:always (:range 1 2)
                    (:nexttime 3 (id "good"))))

(test-prop :input "always [1:2] (nexttime good)"
           :expect (:always (:range 1 2)
                    (:nexttime nil (id "good"))))

(test-prop :input "(always [1:2] (nexttime [3] good))"
           :expect (:always (:range 1 2)
                    (:nexttime 3 (id "good"))))



;; Basic tests for NOT.  Takes no range and no indices.

(test-prop :input "not good dist {1 := 2}"
           :expect (:not (:dist (id "good") (1 := 2))))

(test-prop :input "not (good dist {1 := 2})"
           :expect (:not (:dist (id "good") (1 := 2))))

(test-prop :input "(not good dist {1 := 2})"
           :expect (:not (:dist (id "good") (1 := 2))))

(test-prop :input "not [1] good dist {1 := 2}" ;; no, no indices
           :successp nil)

(test-prop :input "not [1:2] good dist {1 := 2}" ;; no, no range
           :successp nil)

(test-prop :input "not (((good dist {1 := 2})))"
           :expect (:not (:dist (id "good") (1 := 2))))

(test-prop :input "not (not good)"
           :expect (:not (:not (id "good"))))

(test-prop :input "not (not (not good))"
           :expect (:not (:not (:not (id "good")))))

(test-prop :input "not r1 until r2"
           ;; Tricky and important.  NOT must bind more tightly than UNTIL.
           :expect (:until
                    (:not (id "r1"))
                    (id "r2")))

(test-prop :input "not not r1 until r2"
           ;; Tricky and important.  NOT must bind more tightly than UNTIL.
           :expect (:until
                    (:not (:not (id "r1")))
                    (id "r2")))

(test-prop :input "not always r1 until r2"
           ;; Tricky and very confusing.  Precedence:
           ;;  NOT > UNTIL > ALWAYS
           ;; NCVerilog accepts this and treats it as:
           ;;  NOT (ALWAYS (UNTIL R1 R2))
           ;; We should now be handling this just like NCVerilog thanks to
           ;; the godawful hack.
           :expect (:not
                    (:always (no-range)
                     (:until (id "r1") (id "r2")))))



;; Basic tests for strong.  Takes no range and no indices.
;; Unlike NOT, STRONG requires parens!

(test-prop :input "strong good dist {1 := 2}"  ;; need parens
           :successp nil)

(test-prop :input "strong (good dist {1 := 2})"
           :expect (:strong (:dist (id "good") (1 := 2))))

(test-prop :input "(strong good dist {1 := 2})" ;; need inner parens
           :successp nil)

(test-prop :input "(strong (good dist {1 := 2}))"
           :expect (:strong (:dist (id "good") (1 := 2))))

(test-prop :input "strong [1] good dist {1 := 2}" ;; no, no indices
           :successp nil)

(test-prop :input "strong [1:2] good dist {1 := 2}" ;; no, no range
           :successp nil)

(test-prop :input "strong (((good dist {1 := 2})))"
           :expect (:strong (:dist (id "good") (1 := 2))))

(test-prop :input "strong(strong(good))"
           ;; BOZO this really should fail, because strong should not be able
           ;; to be nested, because it is supposed to take a sequence_expr as
           ;; an argument, not a property_expr.  But because we treat sequence
           ;; and property expressions as one construct and don't
           ;; differentiate, we tolerate this even though the standard says
           ;; we shouldn't.
           :expect (:strong (:strong (id "good"))))


;; similar tests for weak

(test-prop :input "weak good dist {1 := 2}"  ;; need parens
           :successp nil)

(test-prop :input "weak (good dist {1 := 2})"
           :expect (:weak (:dist (id "good") (1 := 2))))

(test-prop :input "(weak good dist {1 := 2})" ;; need inner parens
           :successp nil)

(test-prop :input "(weak (good dist {1 := 2}))"
           :expect (:weak (:dist (id "good") (1 := 2))))

(test-prop :input "weak [1] good dist {1 := 2}" ;; no, no indices
           :successp nil)

(test-prop :input "weak [1:2] good dist {1 := 2}" ;; no, no range
           :successp nil)

(test-prop :input "weak (((good dist {1 := 2})))"
           :expect (:weak (:dist (id "good") (1 := 2))))

(test-prop :input "weak(weak(good))"
           ;; Like strong(strong(good)) we should fail but don't.
           :expect (:weak (:weak (id "good"))))


;; basic tests for accept_on.

(test-prop :input "accept_on"
           :successp nil)

(test-prop :input "accept_on (foo)"
           :successp nil)

(test-prop :input "accept_on foo bar"
           :successp nil)

(test-prop :input "accept_on (foo) bar"
           :expect (:accept_on (id "foo") (id "bar")))

(test-prop :input "accept_on (foo) (bar)"
           :expect (:accept_on (id "foo") (id "bar")))

(test-prop :input "accept_on ((foo)) (bar)"
           :expect (:accept_on (id "foo") (id "bar")))

(test-prop :input "accept_on (foo) good dist {3 := 4}"
           :expect (:accept_on (id "foo")
                    (:dist (id "good") (3 := 4))))

(test-prop :input "accept_on (foo) (good dist {3 := 4})"
           :expect (:accept_on (id "foo")
                    (:dist (id "good") (3 := 4))))

(test-prop :input "accept_on foo good dist {3 := 4}"
           ;; need parens around the condition
           :successp nil)

(test-prop :input "accept_on (foo dist {1 := 2}) good dist {3 := 4}"
           :expect (:accept_on
                    (:dist (id "foo") (1 := 2))
                    (:dist (id "good") (3 := 4))))

(test-prop :input "accept_on foo dist {1 := 2} good dist {3 := 4}"
           ;; need parens around condition
           :successp nil)

(test-prop :input "accept_on (foo dist {1 := 2}) (((good dist {3 := 4})))"
           :expect (:accept_on
                    (:dist (id "foo") (1 := 2))
                    (:dist (id "good") (3 := 4))))

(test-prop :input "accept_on ((foo dist {1 := 2})) (((good dist {3 := 4})))"
           ;; It seems surprising that this fails, but I think it's correct.
           ;; The extra parens around the condition are not allowed because
           ;; the grammar rule is:
           ;;    accept_on '(' expression_or_dist ')' ...
           ;; And an expression_or_dist is really defined as just
           ;;    expression [ 'dist' ... ]
           ;; So there's no option to have additional parens around an
           ;; expression_or_dist.  I can't verify this behavior on NCV or VCS
           ;; yet: NCV seems to only tolerate an expression after accept_on,
           ;; and VCS seems to not even support accept_on at all.
           :successp nil)


;; Similar tests for reject_on

(test-prop :input "reject_on"
           :successp nil)

(test-prop :input "reject_on (foo)"
           :successp nil)

(test-prop :input "reject_on foo bar"
           :successp nil)

(test-prop :input "reject_on (foo) bar"
           :expect (:reject_on (id "foo") (id "bar")))

(test-prop :input "reject_on (foo) (bar)"
           :expect (:reject_on (id "foo") (id "bar")))

(test-prop :input "reject_on ((foo)) (bar)"
           :expect (:reject_on (id "foo") (id "bar")))

(test-prop :input "reject_on (foo) good dist {3 := 4}"
           :expect (:reject_on (id "foo")
                    (:dist (id "good") (3 := 4))))

(test-prop :input "reject_on (foo) (good dist {3 := 4})"
           :expect (:reject_on (id "foo")
                    (:dist (id "good") (3 := 4))))

(test-prop :input "reject_on foo good dist {3 := 4}"
           ;; need parens around the condition
           :successp nil)

(test-prop :input "reject_on (foo dist {1 := 2}) good dist {3 := 4}"
           :expect (:reject_on
                    (:dist (id "foo") (1 := 2))
                    (:dist (id "good") (3 := 4))))

(test-prop :input "reject_on foo dist {1 := 2} good dist {3 := 4}"
           ;; need parens around condition
           :successp nil)

(test-prop :input "reject_on (foo dist {1 := 2}) (((good dist {3 := 4})))"
           :expect (:reject_on
                    (:dist (id "foo") (1 := 2))
                    (:dist (id "good") (3 := 4))))


;; Similar tests for sync_accept_on

(test-prop :input "sync_accept_on"
           :successp nil)

(test-prop :input "sync_accept_on (foo)"
           :successp nil)

(test-prop :input "sync_accept_on foo bar"
           :successp nil)

(test-prop :input "sync_accept_on (foo) bar"
           :expect (:sync_accept_on (id "foo") (id "bar")))

(test-prop :input "sync_accept_on (foo) (bar)"
           :expect (:sync_accept_on (id "foo") (id "bar")))

(test-prop :input "sync_accept_on ((foo)) (bar)"
           :expect (:sync_accept_on (id "foo") (id "bar")))

(test-prop :input "sync_accept_on (foo) good dist {3 := 4}"
           :expect (:sync_accept_on (id "foo")
                    (:dist (id "good") (3 := 4))))

(test-prop :input "sync_accept_on (foo) (good dist {3 := 4})"
           :expect (:sync_accept_on (id "foo")
                    (:dist (id "good") (3 := 4))))

(test-prop :input "sync_accept_on foo good dist {3 := 4}"
           ;; need parens around the condition
           :successp nil)

(test-prop :input "sync_accept_on (foo dist {1 := 2}) good dist {3 := 4}"
           :expect (:sync_accept_on
                    (:dist (id "foo") (1 := 2))
                    (:dist (id "good") (3 := 4))))

(test-prop :input "sync_accept_on foo dist {1 := 2} good dist {3 := 4}"
           ;; need parens around condition
           :successp nil)

(test-prop :input "sync_accept_on (foo dist {1 := 2}) (((good dist {3 := 4})))"
           :expect (:sync_accept_on
                    (:dist (id "foo") (1 := 2))
                    (:dist (id "good") (3 := 4))))


;; similar tests for sync_reject_on

(test-prop :input "sync_reject_on"
           :successp nil)

(test-prop :input "sync_reject_on (foo)"
           :successp nil)

(test-prop :input "sync_reject_on foo bar"
           :successp nil)

(test-prop :input "sync_reject_on (foo) bar"
           :expect (:sync_reject_on (id "foo") (id "bar")))

(test-prop :input "sync_reject_on (foo) (bar)"
           :expect (:sync_reject_on (id "foo") (id "bar")))

(test-prop :input "sync_reject_on ((foo)) (bar)"
           :expect (:sync_reject_on (id "foo") (id "bar")))

(test-prop :input "sync_reject_on (foo) good dist {3 := 4}"
           :expect (:sync_reject_on (id "foo")
                    (:dist (id "good") (3 := 4))))

(test-prop :input "sync_reject_on (foo) (good dist {3 := 4})"
           :expect (:sync_reject_on (id "foo")
                    (:dist (id "good") (3 := 4))))

(test-prop :input "sync_reject_on foo good dist {3 := 4}"
           ;; need parens around the condition
           :successp nil)

(test-prop :input "sync_reject_on (foo dist {1 := 2}) good dist {3 := 4}"
           :expect (:sync_reject_on
                    (:dist (id "foo") (1 := 2))
                    (:dist (id "good") (3 := 4))))

(test-prop :input "sync_reject_on foo dist {1 := 2} good dist {3 := 4}"
           ;; need parens around condition
           :successp nil)

(test-prop :input "sync_reject_on (foo dist {1 := 2}) (((good dist {3 := 4})))"
           :expect (:sync_reject_on
                    (:dist (id "foo") (1 := 2))
                    (:dist (id "good") (3 := 4))))


;; basic tests for if

(test-prop :input "if"
           :successp nil)

(test-prop :input "if foo"
           :successp nil)

(test-prop :input "if foo bar"
           ;; Need explicit parens around foo!
           :successp nil)

(test-prop :input "if (foo) bar"
           :expect (:if (id "foo") (id "bar") 1))

(test-prop :input "if (foo) bar baz"
           ;; Oops, forgot the 'else'!
           :expect (:if (id "foo") (id "bar") 1)
           :extra "baz")

(test-prop :input "if (foo) bar else baz"
           :expect (:if (id "foo") (id "bar") (id "baz")))

(test-prop :input "if (foo dist {3:=4}) bar else baz"
           :expect (:if (:dist (id "foo") (3 := 4))
                    (id "bar")
                    (id "baz")))

(test-prop :input "if ((foo dist {3:=4})) bar else baz"
           ;; Can't have extra parens around exprdist
           :successp nil)

(test-prop :input "if ((foo)) bar else baz"
           ;; Can't have extra parens around exprdist
           :expect (:if (id "foo") (id "bar") (id "baz")))

(test-prop :input "if ((foo)) always bar else baz"
           ;; Can't have extra parens around exprdist
           :expect (:if (id "foo")
                    (:always (no-range) (id "bar"))
                    (id "baz")))

(test-prop :input "if ((foo)) not always bar else baz"
           ;; Can't have extra parens around exprdist
           :expect (:if (id "foo")
                    (:not (:always (no-range) (id "bar")))
                    (id "baz")))

(test-prop :input "if (foo) if (bar) baz"
           :expect (:if (id "foo")
                        (:if (id "bar") (id "baz") 1)
                    1))

(test-prop :input "if (foo) if (bar) baz else taco"
           :expect (:if (id "foo")
                        (:if (id "bar") (id "baz") (id "taco"))
                    1))


;; basic tests for case

(test-prop :input "case"
           :successp nil)

(test-prop :input "case foo"
           :successp nil)

(test-prop :input "case foo endcase"
           ;; At least one case is required.
           :successp nil)

(test-prop :input "case foo default 1 endcase"
           ;; Shouldn't work because the expression needs parens.
           :successp nil)

(test-prop :input "case (foo) default 1 endcase"
           :expect (:case (id "foo")
                    (:case nil :--> 1)))

(test-prop :input "case (foo) default : 1 ; endcase"
           :expect (:case (id "foo")
                    (:case nil :--> 1)))

(test-prop :input "case (foo) default: 1; endcase"
           :expect (:case (id "foo")
                    (:case nil :--> 1)))

(test-prop :input "case (foo) default: 1 endcase"
           :expect (:case (id "foo")
                    (:case nil :--> 1)))

(test-prop :input "case (foo dist {3:=1}) default: 1 endcase"
           :expect (:case (:dist (id "foo") (3 := 1))
                    (:case nil :--> 1)))

(test-prop :input "case (foo) bar: 0 default: 1 endcase"
           :expect (:case (id "foo")
                    (:case ((id "bar")) :--> 0)
                    (:case nil :--> 1)))

(test-prop :input "case (foo) bar: 0; default: 1 endcase"
           :expect (:case (id "foo")
                    (:case ((id "bar")) :--> 0)
                    (:case nil :--> 1)))

(test-prop :input "case (foo) bar: 0; default 1 endcase"
           :expect (:case (id "foo")
                    (:case ((id "bar")) :--> 0)
                    (:case nil :--> 1)))

(test-prop :input "case (foo) bar, baz: 0 default: 1 endcase"
           :expect (:case (id "foo")
                    (:case ((id "bar") (id "baz")) :--> 0)
                    (:case nil :--> 1)))

(test-prop :input "case (foo) bar, baz: 0 ; default: 1 endcase"
           :expect (:case (id "foo")
                    (:case ((id "bar") (id "baz")) :--> 0)
                    (:case nil :--> 1)))

(test-prop :input "case (foo) bar dist {3:=1}, baz: 0 ; default: 1 endcase"
           :expect (:case (id "foo")
                    (:case ((:dist (id "bar") (3 := 1))
                            (id "baz"))
                     :--> 0)
                    (:case nil :--> 1)))

(test-prop :input "case (foo) bar dist {3:=1}, baz: 0 endcase"
           :expect (:case (id "foo")
                    (:case ((:dist (id "bar") (3 := 1))
                            (id "baz"))
                     :--> 0)))

(test-prop :input "case (foo) bar: always good; default: 1 endcase"
           :expect (:case (id "foo")
                    (:case ((id "bar")) :--> (:always (no-range) (id "good")))
                    (:case nil :--> 1)))

(test-prop :input "case (foo)
                     bar: always good;
                     default: if (smoke) fire
                   endcase"
           :expect (:case (id "foo")
                    (:case ((id "bar")) :--> (:always (no-range) (id "good")))
                    (:case nil :--> (:if (id "smoke") (id "fire") 1))))

(test-prop :input "case (foo)
                     bar: case (inner) default 1 endcase
                     default if (smoke) fire
                   endcase"
           :expect (:case (id "foo")
                    (:case ((id "bar")) :--> (:case (id "inner")
                                              (:case nil :--> 1)))
                    (:case nil :--> (:if (id "smoke") (id "fire") 1))))


;; basic tests for |->

(test-prop :input "|->" :successp nil)
(test-prop :input "a |->" :successp nil)
(test-prop :input "|-> b" :successp nil)

(test-prop :input "a |-> b"
           :expect (:-> (id "a") (id "b")))

(test-prop :input "a |-> b |-> c"
           ;; Must be right-associative.
           :expect (:-> (id "a")
                    (:-> (id "b")
                     (id "c"))))

;; always, etc. are lower precedence than |->
(test-prop :input "always a |-> c"
           :expect (:always (no-range)
                    (:-> (id "a") (id "c"))))

(test-prop :input "always [3:0] a |-> c"
           :expect (:always (:range 3 0)
                    (:-> (id "a") (id "c"))))

(test-prop :input "a and b |-> c"
           :expect (:-> (:and (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a |-> b and c"
           :expect (:-> (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "a and b |-> c and d"
           :expect (:-> (:and (id "a") (id "b"))
                        (:and (id "c") (id "d"))))

(test-prop :input "a or b |-> c"
           :expect (:-> (:or (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a |-> b or c"
           :expect (:-> (id "a")
                    (:or (id "b") (id "c"))))

(test-prop :input "a or b |-> c or d"
           :expect (:-> (:or (id "a") (id "b"))
                        (:or (id "c") (id "d"))))


(test-prop :input "not a |-> c"
           ;; Very tricky.
           ;;
           ;; We successfully parse this, but it is not valid according
           ;; to the SystemVerilog grammar.  The left of |-> needs to be
           ;; a sequence expression instead of a property expression.
           ;;
           ;; If you just read the SystemVerilog standard, you could
           ;; imagine that this should be parsed as
           ;;    not (a |-> c)
           ;; because that's a perfectly valid property expression.  So
           ;; that is scary because it seems like perhaps VL is getting
           ;; this wrong.
           ;;
           ;; However, testing with VCS and NCVerilog suggest that both
           ;; tools treat `not a |-> c` as an "error, property expression
           ;; where sequence expression is required".
           ;;
           ;; So basically we're handling this just like real commercial
           ;; tools, and if we ever implement a strong check that you haven't
           ;; used property expressions where sequence expressions are
           ;; required, then that check should flag this and we should be
           ;; doing the right thing.
           :expect (:-> (:not (id "a"))
                        (id "c")))

(test-prop :input "a |-> b and c"
           :expect (:-> (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "not a |-> b and c"
           :expect (:-> (:not (id "a"))
                    (:and (id "b") (id "c"))))

(test-prop :input "a |-> b until c"
           :expect (:-> (id "a")
                    (:until (id "b") (id "c"))))

(test-prop :input "not a |-> b until c"
           :expect (:-> (:not (id "a"))
                    (:until (id "b") (id "c"))))

(test-prop :input "if (foo) a |-> b"
           ;; Tricky, but the if-else is supposed to bind least tightly,
           ;; so I think the a |-> b should go into the true branch.
           :expect (:if (id "foo")
                    (:-> (id "a") (id "b"))
                    1))

(test-prop :input "if (foo) a else b |-> c"
           ;; Tricky, but the if-else is supposed to bind least tightly,
           ;; so I think the a |-> b should go into the false branch,
           ;; rather than on the outside.
           :expect (:if (id "foo")
                    (id "a")
                    (:-> (id "b") (id "c"))))


;; same tests for |=>

(test-prop :input "|=>" :successp nil)
(test-prop :input "a |=>" :successp nil)
(test-prop :input "|=> b" :successp nil)

(test-prop :input "a |=> b"
           :expect (:=> (id "a") (id "b")))

(test-prop :input "a |=> b |=> c"
           :expect (:=> (id "a")
                    (:=> (id "b")
                     (id "c"))))

(test-prop :input "a |=> b |-> c"
           :expect (:=> (id "a")
                    (:-> (id "b")
                     (id "c"))))

(test-prop :input "always a |=> c"
           :expect (:always (no-range)
                    (:=> (id "a") (id "c"))))

(test-prop :input "always [3:0] a |=> c"
           :expect (:always (:range 3 0)
                    (:=> (id "a") (id "c"))))

(test-prop :input "a and b |=> c"
           :expect (:=> (:and (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a |=> b and c"
           :expect (:=> (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "a and b |=> c and d"
           :expect (:=> (:and (id "a") (id "b"))
                        (:and (id "c") (id "d"))))

(test-prop :input "a or b |=> c"
           :expect (:=> (:or (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a |=> b or c"
           :expect (:=> (id "a")
                    (:or (id "b") (id "c"))))

(test-prop :input "a or b |=> c or d"
           :expect (:=> (:or (id "a") (id "b"))
                        (:or (id "c") (id "d"))))

(test-prop :input "not a |=> c"
           :expect (:=> (:not (id "a"))
                        (id "c")))

(test-prop :input "a |=> b and c"
           :expect (:=> (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "not a |=> b and c"
           :expect (:=> (:not (id "a"))
                    (:and (id "b") (id "c"))))

(test-prop :input "a |=> b until c"
           :expect (:=> (id "a")
                    (:until (id "b") (id "c"))))

(test-prop :input "not a |=> b until c"
           :expect (:=> (:not (id "a"))
                    (:until (id "b") (id "c"))))

(test-prop :input "if (foo) a |=> b"
           :expect (:if (id "foo")
                    (:=> (id "a") (id "b"))
                    1))

(test-prop :input "if (foo) a else b |=> c"
           :expect (:if (id "foo")
                    (id "a")
                    (:=> (id "b") (id "c"))))


;; same tests for #-#

(test-prop :input "#-#" :successp nil)
(test-prop :input "a #-#" :successp nil)
(test-prop :input "#-# b" :successp nil)

(test-prop :input "a #-# b"
           :expect (:#-# (id "a") (id "b")))

(test-prop :input "a #-# b #-# c"
           :expect (:#-# (id "a")
                    (:#-# (id "b")
                     (id "c"))))

(test-prop :input "a #-# b |-> c"
           :expect (:#-# (id "a")
                    (:-> (id "b")
                     (id "c"))))

(test-prop :input "a #-# b |=> c"
           :expect (:#-# (id "a")
                    (:=> (id "b")
                     (id "c"))))

(test-prop :input "a |-> b #-# c"
           :expect (:-> (id "a")
                    (:#-# (id "b")
                     (id "c"))))

(test-prop :input "a |=> b #-# c"
           :expect (:=> (id "a")
                    (:#-# (id "b")
                     (id "c"))))

(test-prop :input "always a #-# c"
           :expect (:always (no-range)
                    (:#-# (id "a") (id "c"))))

(test-prop :input "always [3:0] a #-# c"
           :expect (:always (:range 3 0)
                    (:#-# (id "a") (id "c"))))

(test-prop :input "a and b #-# c"
           :expect (:#-# (:and (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a #-# b and c"
           :expect (:#-# (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "a and b #-# c and d"
           :expect (:#-# (:and (id "a") (id "b"))
                        (:and (id "c") (id "d"))))

(test-prop :input "a or b #-# c"
           :expect (:#-# (:or (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a #-# b or c"
           :expect (:#-# (id "a")
                    (:or (id "b") (id "c"))))

(test-prop :input "a or b #-# c or d"
           :expect (:#-# (:or (id "a") (id "b"))
                        (:or (id "c") (id "d"))))

(test-prop :input "not a #-# c"
           :expect (:#-# (:not (id "a"))
                        (id "c")))

(test-prop :input "a #-# b and c"
           :expect (:#-# (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "not a #-# b and c"
           :expect (:#-# (:not (id "a"))
                    (:and (id "b") (id "c"))))

(test-prop :input "a #-# b until c"
           :expect (:#-# (id "a")
                    (:until (id "b") (id "c"))))

(test-prop :input "not a #-# b until c"
           :expect (:#-# (:not (id "a"))
                    (:until (id "b") (id "c"))))

(test-prop :input "if (foo) a #-# b"
           :expect (:if (id "foo")
                    (:#-# (id "a") (id "b"))
                    1))

(test-prop :input "if (foo) a else b #-# c"
           :expect (:if (id "foo")
                    (id "a")
                    (:#-# (id "b") (id "c"))))


;; same tests for #=#

(test-prop :input "#=#" :successp nil)
(test-prop :input "a #=#" :successp nil)
(test-prop :input "#=# b" :successp nil)

(test-prop :input "a #=# b"
           :expect (:#=# (id "a") (id "b")))

(test-prop :input "a #=# b #=# c"
           :expect (:#=# (id "a")
                    (:#=# (id "b")
                     (id "c"))))

(test-prop :input "a #=# b |-> c"
           :expect (:#=# (id "a")
                    (:-> (id "b")
                     (id "c"))))

(test-prop :input "a #=# b |=> c"
           :expect (:#=# (id "a")
                    (:=> (id "b")
                     (id "c"))))

(test-prop :input "a #=# b #-# c"
           :expect (:#=# (id "a")
                    (:#-# (id "b")
                     (id "c"))))

(test-prop :input "a |-> b #=# c"
           :expect (:-> (id "a")
                    (:#=# (id "b")
                     (id "c"))))

(test-prop :input "a |=> b #=# c"
           :expect (:=> (id "a")
                    (:#=# (id "b")
                     (id "c"))))

(test-prop :input "a #-# b #=# c"
           :expect (:#-# (id "a")
                    (:#=# (id "b")
                     (id "c"))))

(test-prop :input "always a #=# c"
           :expect (:always (no-range)
                    (:#=# (id "a") (id "c"))))

(test-prop :input "always [3:0] a #=# c"
           :expect (:always (:range 3 0)
                    (:#=# (id "a") (id "c"))))

(test-prop :input "a and b #=# c"
           :expect (:#=# (:and (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a #=# b and c"
           :expect (:#=# (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "a and b #=# c and d"
           :expect (:#=# (:and (id "a") (id "b"))
                        (:and (id "c") (id "d"))))

(test-prop :input "a or b #=# c"
           :expect (:#=# (:or (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a #=# b or c"
           :expect (:#=# (id "a")
                    (:or (id "b") (id "c"))))

(test-prop :input "a or b #=# c or d"
           :expect (:#=# (:or (id "a") (id "b"))
                        (:or (id "c") (id "d"))))

(test-prop :input "not a #=# c"
           :expect (:#=# (:not (id "a"))
                        (id "c")))

(test-prop :input "a #=# b and c"
           :expect (:#=# (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "not a #=# b and c"
           :expect (:#=# (:not (id "a"))
                    (:and (id "b") (id "c"))))

(test-prop :input "a #=# b until c"
           :expect (:#=# (id "a")
                    (:until (id "b") (id "c"))))

(test-prop :input "not a #=# b until c"
           :expect (:#=# (:not (id "a"))
                    (:until (id "b") (id "c"))))

(test-prop :input "if (foo) a #=# b"
           :expect (:if (id "foo")
                    (:#=# (id "a") (id "b"))
                    1))

(test-prop :input "if (foo) a else b #=# c"
           :expect (:if (id "foo")
                    (id "a")
                    (:#=# (id "b") (id "c"))))



;; basic tests for until

(test-prop :input "until" :successp nil)
(test-prop :input "a until" :successp nil)
(test-prop :input "until b" :successp nil)

(test-prop :input "a until b"
           :expect (:until (id "a") (id "b")))

(test-prop :input "a until b until c"
           ;; Supposed to be right-associative.
           :expect (:until (id "a")
                    (:until (id "b") (id "c"))))

(test-prop :input "(a until b) until c"
           :expect (:until (:until (id "a") (id "b"))
                        (id "c")))

(test-prop :input "a until (b until c)"
           :expect (:until (id "a")
                    (:until (id "b") (id "c"))))

(test-prop :input "not a until b"
           :expect (:until (:not (id "a"))
                           (id "b")))

(test-prop :input "not a until not b"
           :expect (:until (:not (id "a"))
                    (:not (id "b"))))

(test-prop :input "a iff b until c iff d"
           :expect (:until
                    (:iff (id "a") (id "b"))
                    (:iff (id "c") (id "d"))))

(test-prop :input "a until b s_until c implies d"
           ;; These are supposed to be right and equal precedence, so this
           ;; should be: a until (b s_until (c implies d))
           :expect (:until (id "a")
                    (:s_until (id "b")
                     (:implies (id "c") (id "d")))))

(test-prop :input "a until b s_until c iff d implies e"
           :expect (:until (id "a")
                    (:s_until (id "b")
                     (:implies
                      (:iff (id "c") (id "d"))
                      (id "e")))))


;; Same tests for s_until

(test-prop :input "s_until" :successp nil)
(test-prop :input "a s_until" :successp nil)
(test-prop :input "s_until b" :successp nil)

(test-prop :input "a s_until b"
           :expect (:s_until (id "a") (id "b")))

(test-prop :input "a s_until b s_until c"
           ;; Supposed to be right-associative.
           :expect (:s_until (id "a")
                    (:s_until (id "b") (id "c"))))

(test-prop :input "(a s_until b) s_until c"
           :expect (:s_until (:s_until (id "a") (id "b"))
                        (id "c")))

(test-prop :input "a s_until (b s_until c)"
           :expect (:s_until (id "a")
                    (:s_until (id "b") (id "c"))))

(test-prop :input "not a s_until b"
           :expect (:s_until (:not (id "a"))
                           (id "b")))

(test-prop :input "not a s_until not b"
           :expect (:s_until (:not (id "a"))
                    (:not (id "b"))))

(test-prop :input "a iff b s_until c iff d"
           :expect (:s_until
                    (:iff (id "a") (id "b"))
                    (:iff (id "c") (id "d"))))

(test-prop :input "a s_until b until c implies d"
           ;; These are supposed to be right and equal precedence, so this
           ;; should be: a s_until (b until (c implies d))
           :expect (:s_until (id "a")
                    (:until (id "b")
                     (:implies (id "c") (id "d")))))

(test-prop :input "a s_until b until c iff d implies e"
           :expect (:s_until (id "a")
                    (:until (id "b")
                     (:implies
                      (:iff (id "c") (id "d"))
                      (id "e")))))


;; Same tests for until_with

(test-prop :input "until_with" :successp nil)
(test-prop :input "a until_with" :successp nil)
(test-prop :input "until_with b" :successp nil)

(test-prop :input "a until_with b"
           :expect (:until_with (id "a") (id "b")))

(test-prop :input "a until_with b until_with c"
           ;; Supposed to be right-associative.
           :expect (:until_with (id "a")
                    (:until_with (id "b") (id "c"))))

(test-prop :input "(a until_with b) until_with c"
           :expect (:until_with (:until_with (id "a") (id "b"))
                        (id "c")))

(test-prop :input "a until_with (b until_with c)"
           :expect (:until_with (id "a")
                    (:until_with (id "b") (id "c"))))

(test-prop :input "not a until_with b"
           :expect (:until_with (:not (id "a"))
                           (id "b")))

(test-prop :input "not a until_with not b"
           :expect (:until_with (:not (id "a"))
                    (:not (id "b"))))

(test-prop :input "a iff b until_with c iff d"
           :expect (:until_with
                    (:iff (id "a") (id "b"))
                    (:iff (id "c") (id "d"))))

(test-prop :input "a until_with b until c implies d"
           ;; These are supposed to be right and equal precedence, so this
           ;; should be: a until_with (b until (c implies d))
           :expect (:until_with (id "a")
                    (:until (id "b")
                     (:implies (id "c") (id "d")))))

(test-prop :input "a until_with b until c iff d implies e"
           :expect (:until_with (id "a")
                    (:until (id "b")
                     (:implies
                      (:iff (id "c") (id "d"))
                      (id "e")))))


;; Same tests for s_until_with

(test-prop :input "s_until_with" :successp nil)
(test-prop :input "a s_until_with" :successp nil)
(test-prop :input "s_until_with b" :successp nil)

(test-prop :input "a s_until_with b"
           :expect (:s_until_with (id "a") (id "b")))

(test-prop :input "a s_until_with b s_until_with c"
           ;; Supposed to be right-associative.
           :expect (:s_until_with (id "a")
                    (:s_until_with (id "b") (id "c"))))

(test-prop :input "(a s_until_with b) s_until_with c"
           :expect (:s_until_with (:s_until_with (id "a") (id "b"))
                        (id "c")))

(test-prop :input "a s_until_with (b s_until_with c)"
           :expect (:s_until_with (id "a")
                    (:s_until_with (id "b") (id "c"))))

(test-prop :input "not a s_until_with b"
           :expect (:s_until_with (:not (id "a"))
                           (id "b")))

(test-prop :input "not a s_until_with not b"
           :expect (:s_until_with (:not (id "a"))
                    (:not (id "b"))))

(test-prop :input "a iff b s_until_with c iff d"
           :expect (:s_until_with
                    (:iff (id "a") (id "b"))
                    (:iff (id "c") (id "d"))))

(test-prop :input "a s_until_with b until c implies d"
           ;; These are supposed to be right and equal precedence, so this
           ;; should be: a s_until_with (b until (c implies d))
           :expect (:s_until_with (id "a")
                    (:until (id "b")
                     (:implies (id "c") (id "d")))))

(test-prop :input "a s_until_with b until c iff d implies e"
           :expect (:s_until_with (id "a")
                    (:until (id "b")
                     (:implies
                      (:iff (id "c") (id "d"))
                      (id "e")))))


;; Same tests for implies

(test-prop :input "implies" :successp nil)
(test-prop :input "a implies" :successp nil)
(test-prop :input "implies b" :successp nil)

(test-prop :input "a implies b"
           :expect (:implies (id "a") (id "b")))

(test-prop :input "a implies b implies c"
           ;; Supposed to be right-associative.
           :expect (:implies (id "a")
                    (:implies (id "b") (id "c"))))

(test-prop :input "(a implies b) implies c"
           :expect (:implies (:implies (id "a") (id "b"))
                        (id "c")))

(test-prop :input "a implies (b implies c)"
           :expect (:implies (id "a")
                    (:implies (id "b") (id "c"))))

(test-prop :input "not a implies b"
           :expect (:implies (:not (id "a"))
                           (id "b")))

(test-prop :input "not a implies not b"
           :expect (:implies (:not (id "a"))
                    (:not (id "b"))))

(test-prop :input "a iff b implies c iff d"
           :expect (:implies
                    (:iff (id "a") (id "b"))
                    (:iff (id "c") (id "d"))))

(test-prop :input "a implies b until c implies d"
           ;; These are supposed to be right and equal precedence, so this
           ;; should be: a implies (b until (c implies d))
           :expect (:implies (id "a")
                    (:until (id "b")
                     (:implies (id "c") (id "d")))))

(test-prop :input "a implies b until c iff d implies e"
           :expect (:implies (id "a")
                    (:until (id "b")
                     (:implies
                      (:iff (id "c") (id "d"))
                      (id "e")))))


;; basic tests for or

(test-prop :input "or" :successp nil)
(test-prop :input "a or" :successp nil)
(test-prop :input "or b" :successp nil)

(test-prop :input "a or b"
           :expect (:or (id "a") (id "b")))

(test-prop :input "a or b or c"
           :expect (:or (:or (id "a") (id "b"))
                        (id "c")))

(test-prop :input "(a or b) or c"
           :expect (:or (:or (id "a") (id "b"))
                        (id "c")))

(test-prop :input "a or (b or c)"
           :expect (:or (id "a")
                    (:or (id "b") (id "c"))))

(test-prop :input "(not a)"
           :expect (:not (id "a")))

(test-prop :input "(not a) or (not b)"
           :expect (:or (:not (id "a"))
                        (:not (id "b"))))

(test-prop :input "(not a) or not b"
           ;; This is a very tricky case that failed back when we tried to keep
           ;; sequence_expr and property_expr separate, because the
           ;; sequence-level OR thought that it should eat the (not b), but
           ;; that was a property-level expression.  See notes/properties.txt
           ;; for more notes about this.  Fortunately we now just have one level
           ;; of and/or, so this works easily.
           :expect (:or (:not (id "a"))
                        (:not (id "b"))))

(test-prop :input "not a or (not b)"
           :expect (:or (:not (id "a"))
                        (:not (id "b"))))

(test-prop :input "not a or not b"
           :expect (:or (:not (id "a"))
                        (:not (id "b"))))

(test-prop :input "always a or b"
           :expect (:always (no-range) (:or (id "a") (id "b"))))

(test-prop :input "always a or not b"
           :expect (:always (no-range) (:or (id "a") (:not (id "b")))))


;; basic tests for and

(test-prop :input "and" :successp nil)
(test-prop :input "a and" :successp nil)
(test-prop :input "and b" :successp nil)

(test-prop :input "a and b"
           :expect (:and (id "a") (id "b")))

(test-prop :input "a and b and c"
           :expect (:and (:and (id "a") (id "b"))
                        (id "c")))

(test-prop :input "(a and b) and c"
           :expect (:and (:and (id "a") (id "b"))
                        (id "c")))

(test-prop :input "a and (b and c)"
           :expect (:and (id "a")
                    (:and (id "b") (id "c"))))

(test-prop :input "(not a) and (not b)"
           :expect (:and (:not (id "a"))
                         (:not (id "b"))))

(test-prop :input "(not a) and not b"
           :expect (:and (:not (id "a"))
                         (:not (id "b"))))

(test-prop :input "not a and (not b)"
           :expect (:and (:not (id "a"))
                         (:not (id "b"))))

(test-prop :input "not a and not b"
           :expect (:and (:not (id "a"))
                         (:not (id "b"))))

(test-prop :input "a and b or c"
           :expect (:or (:and (id "a") (id "b"))
                        (id "c")))

(test-prop :input "a or b and c"
           :expect (:or (id "a")
                        (:and (id "b") (id "c"))))

(test-prop :input "a or not b and c"
           :expect (:or (id "a")
                        (:and (:not (id "b")) (id "c"))))

(test-prop :input "not a or not b and c"
           :expect (:or (:not (id "a"))
                        (:and (:not (id "b")) (id "c"))))

(test-prop :input "not a or not b and not c"
           :expect (:or (:not (id "a"))
                        (:and (:not (id "b")) (:not (id "c")))))

(test-prop :input "not a or not b dist {3 := 5} and not c"
           :expect (:or (:not (id "a"))
                        (:and (:not (:dist (id "b") (3 := 5)))
                         (:not (id "c")))))

(test-prop :input "always a and b"
           :expect (:always (no-range) (:and (id "a") (id "b"))))

(test-prop :input "always a and not b"
           :expect (:always (no-range) (:and (id "a") (:not (id "b")))))

(test-prop :input "always a or not always b or not c"
           :expect (:always (no-range)
                    (:or (id "a")
                     (:not (:always (no-range)
                            (:or (id "b")
                             (:not (id "c"))))))))


;; basic tests for intersect
;; higher precedence than and/or/not, lower precedence than within/throughout

(test-prop :input "intersect" :successp nil)
(test-prop :input "a intersect" :successp nil)
(test-prop :input "intersect b" :successp nil)

(test-prop :input "a intersect b"
           :expect (:intersect (id "a") (id "b")))

(test-prop :input "a intersect b intersect c"
           ;; supposed to be left-associative
           :expect (:intersect (:intersect (id "a") (id "b"))
                    (id "c")))

(test-prop :input "(a intersect b) intersect c"
           :expect (:intersect (:intersect (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a intersect (b intersect c)"
           :expect (:intersect (id "a")
                    (:intersect (id "b") (id "c"))))

(test-prop :input "a intersect b within c"
           :expect (:intersect (id "a")
                    (:within (id "b") (id "c"))))

(test-prop :input "a within b intersect c"
           :expect (:intersect (:within (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a intersect b and c"
           :expect (:and (:intersect (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a intersect b and c intersect d"
           :expect (:and (:intersect (id "a") (id "b"))
                    (:intersect (id "c") (id "d"))))

(test-prop :input "a intersect b or c"
           :expect (:or (:intersect (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a intersect b or c intersect d"
           :expect (:or (:intersect (id "a") (id "b"))
                        (:intersect (id "c") (id "d"))))

(test-prop :input "always a intersect b"
           :expect (:always (no-range) (:intersect (id "a") (id "b"))))

(test-prop :input "not a intersect b"
           :expect (:not (:intersect (id "a") (id "b"))))

(test-prop :input "(not a) intersect (not b)"
           :expect (:intersect (:not (id "a")) (:not (id "b"))))

(test-prop :input "(not a) intersect not b"
           ;; BOZO?  This is not permitted because an isect_se is looking for
           ;; only a within_se afterward.  NCV also produces a parse error here.
           ;; VCS produces a nicer message explaining the problem.  It's probably
           ;; OK for this to just be a parse error.
           :successp nil)

(test-prop :input "not a intersect c and d"
           :expect (:and (:not (:intersect (id "a") (id "c")))
                    (id "d")))

(test-prop :input "not a intersect c and not d"
           :expect (:and (:not (:intersect (id "a") (id "c")))
                    (:not (id "d"))))

(test-prop :input "always not a intersect c and not d"
           :expect (:always (no-range)
                    (:and (:not (:intersect (id "a") (id "c")))
                     (:not (id "d")))))



;; basic tests for within
;; higher precedence than intersect, lower than throughout

(test-prop :input "within" :successp nil)
(test-prop :input "a within" :successp nil)
(test-prop :input "within b" :successp nil)

(test-prop :input "a within b"
           :expect (:within (id "a") (id "b")))

(test-prop :input "a within b within c"
           ;; supposed to be left-associative
           :expect (:within (:within (id "a") (id "b"))
                    (id "c")))

(test-prop :input "(a within b) within c"
           :expect (:within (:within (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a within (b within c)"
           :expect (:within (id "a")
                    (:within (id "b") (id "c"))))

(test-prop :input "a within b throughout c"
           :expect (:within (id "a")
                    (:throughout (id "b") (id "c"))))

(test-prop :input "a throughout b within c"
           :expect (:within (:throughout (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a within b and c"
           :expect (:and (:within (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a within b and c within d"
           :expect (:and (:within (id "a") (id "b"))
                    (:within (id "c") (id "d"))))

(test-prop :input "a within b or c"
           :expect (:or (:within (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a within b or c within d"
           :expect (:or (:within (id "a") (id "b"))
                        (:within (id "c") (id "d"))))

(test-prop :input "always a within b"
           :expect (:always (no-range) (:within (id "a") (id "b"))))

(test-prop :input "not a within b"
           :expect (:not (:within (id "a") (id "b"))))

(test-prop :input "(not a) within (not b)"
           :expect (:within (:not (id "a")) (:not (id "b"))))

(test-prop :input "(not a) within not b"
           ;; BOZO?  This is not permitted because an isect_se is looking for
           ;; only a within_se afterward.  NCV also produces a parse error here.
           ;; VCS produces a nicer message explaining the problem.  It's probably
           ;; OK for this to just be a parse error.
           :successp nil)

(test-prop :input "not a within c and d"
           :expect (:and (:not (:within (id "a") (id "c")))
                    (id "d")))

(test-prop :input "not a within c and not d"
           :expect (:and (:not (:within (id "a") (id "c")))
                    (:not (id "d"))))

(test-prop :input "always not a within c and not d"
           :expect (:always (no-range)
                    (:and (:not (:within (id "a") (id "c")))
                     (:not (id "d")))))


;; basic tests for throughout
;; higher precedence than within, lower than ##, but right associative
;; and the lhs should be an expression_or_dist, so pretty weird

(test-prop :input "throughout" :successp nil)
(test-prop :input "a throughout" :successp nil)
(test-prop :input "throughout b" :successp nil)

(test-prop :input "a throughout b"
           :expect (:throughout (id "a") (id "b")))

(test-prop :input "a throughout b throughout c"
           ;; supposed to be right-associative
           :expect (:throughout (id "a")
                    (:throughout (id "b") (id "c"))))

(test-prop :input "a throughout b throughout c throughout d"
           :expect (:throughout (id "a")
                    (:throughout (id "b")
                     (:throughout (id "c")
                      (id "d")))))

(test-prop :input "a throughout c ##1 d"
           :expect (:throughout (id "a")
                    (:then (id "c") (:range 1 1) (id "d"))))

(test-prop :input "a throughout c ##[*] d"
           :expect (:throughout (id "a")
                    (:then (id "c") (:range 0 (key :vl-$)) (id "d"))))

(test-prop :input "a throughout (b throughout c)"
           :expect (:throughout (id "a")
                    (:throughout (id "b") (id "c"))))

(test-prop :input "(a throughout b) throughout c"
           ;; BOZO?  Both VCS and NCV provide a nice error that says the LHS is
           ;; invalid for a throughout operator.  We just stop parsing after (a
           ;; throughout b), which should lead to a parse error when we parse
           ;; whole property...endproperty style stuff.  This is probably OK.
           :expect (:throughout (id "a") (id "b"))
           :extra "throughout c")

(test-prop :input "(not a) throughout (not b)"
           ;; Similar
           :expect (:not (id "a"))
           :extra "throughout (not b)")

(test-prop :input "a ##1 b throughout c"
           ;; Similar
           :expect (:then (id "a") (:range 1 1) (id "b"))
           :extra "throughout c")

(test-prop :input "a + b * c dist {3:=5} throughout b"
           ;; But an expression_or_dist is ok.
           :expect (:throughout
                    (:dist (:vl-binary-plus nil (id "a")
                            (:vl-binary-times nil (id "b") (id "c")))
                           (3 := 5))
                    (id "b")))

(test-prop :input "a throughout b and c"
           :expect (:and (:throughout (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a throughout b and c throughout d"
           :expect (:and (:throughout (id "a") (id "b"))
                    (:throughout (id "c") (id "d"))))

(test-prop :input "a throughout b or c"
           :expect (:or (:throughout (id "a") (id "b"))
                    (id "c")))

(test-prop :input "a throughout b or c throughout d"
           :expect (:or (:throughout (id "a") (id "b"))
                        (:throughout (id "c") (id "d"))))

(test-prop :input "always a throughout b"
           :expect (:always (no-range) (:throughout (id "a") (id "b"))))

(test-prop :input "not a throughout b"
           :expect (:not (:throughout (id "a") (id "b"))))

(test-prop :input "not a throughout c and d"
           :expect (:and (:not (:throughout (id "a") (id "c")))
                    (id "d")))

(test-prop :input "not a throughout c and not d"
           :expect (:and (:not (:throughout (id "a") (id "c")))
                         (:not (id "d"))))

(test-prop :input "always not a throughout c and not d"
           :expect (:always (no-range)
                    (:and (:not (:throughout (id "a") (id "c")))
                          (:not (id "d")))))


;; basic tests for ##
;; higher precedence than throughout, within, intersect, and/or, etc.
;; lower precedence than [*...], [=...], etc.  left associative.

(test-prop :input "##1" :successp nil)
(test-prop :input "a ##1" :successp nil)

(test-prop :input "a ##1 b"
           :expect (:then (id "a") (:range 1 1) (id "b")))

(test-prop :input "a ##1 b ##2 c"
           ;; left associative
           :expect (:then (:then (id "a") (:range 1 1) (id "b"))
                    (:range 2 2)
                    (id "c")))

(test-prop :input "(a ##1 b) ##2 c"
           :expect (:then (:then (id "a") (:range 1 1) (id "b"))
                    (:range 2 2)
                    (id "c")))

(test-prop :input "##1 a"
           ;; special -- can start with implicit 1
           :expect (:then 1 (:range 1 1) (id "a")))

(test-prop :input "##1 b ##2 c"
           :expect (:then (:then 1 (:range 1 1) (id "b"))
                    (:range 2 2)
                    (id "c")))

(test-prop :input "(##1 b) ##2 c"
           :expect (:then (:then 1 (:range 1 1) (id "b"))
                    (:range 2 2)
                    (id "c")))

(test-prop :input "##1 (b ##2 c)"
           :expect (:then 1
                    (:range 1 1)
                    (:then (id "b") (:range 2 2) (id "c"))))

(test-prop :input "##1 b ##2 c"
           :expect (:then (:then 1 (:range 1 1) (id "b"))
                    (:range 2 2)
                    (id "c")))

(test-prop :input "a ##1 not b"
           ;; This isn't allowed because not b isn't a sequence expr.
           :successp nil)

(test-prop :input "a ##1 always b"
           :successp nil)

(test-prop :input "a ##1 (b and c)"
           ;; This shouldn't really be allowed but we expect to flag
           ;; it later (property where sequence expected)
           :expect (:then (id "a") (:range 1 1) (:and (id "b") (id "c"))))

(test-prop :input "a ##1 b and c"
           ;; This shouldn't really be allowed but we expect to flag
           ;; it later (property where sequence expected)
           :expect (:and (:then (id "a") (:range 1 1) (id "b"))
                    (id "c")))


;; basic tests of repetitions

(test-prop :input "a[*]"
           :expect (:repeat (id "a")
                    (:[*] 0 (key :vl-$))))

(test-prop :input "a[*3]"
           :expect (:repeat (id "a") (:[*] 3)))

(test-prop :input "a[*3:4]"
           :expect (:repeat (id "a") (:[*] 3 4)))

(test-prop :input "a[=3]"
           :expect (:repeat (id "a") (:[=] 3)))

(test-prop :input "a[=3:4]"
           :expect (:repeat (id "a") (:[=] 3 4)))

(test-prop :input "a[->3]"
           :expect (:repeat (id "a") (:[->] 3)))

(test-prop :input "a[->3:4]"
           :expect (:repeat (id "a") (:[->] 3 4)))

(test-prop :input "a ##1 b[*]"
           :expect (:then (id "a") (:range 1 1)
                    (:repeat (id "b") (:[*] 0 (key :vl-$)))))

(test-prop :input "(a ##1 b)[*]"
           :expect (:repeat
                    (:then (id "a") (:range 1 1) (id "b"))
                    (:[*] 0 (key :vl-$))))

(test-prop :input "(a)[*]"
           :expect (:repeat (id "a")
                    (:[*] 0 (key :vl-$))))

(test-prop :input "(a)[* 3:4]"
           :expect (:repeat (id "a") (:[*] 3 4)))

(test-prop :input "a[* 3:4][* 5:6]"
           :expect (:repeat (id "a") (:[*] 3 4))
           :extra "[ * 5 : 6 ]")

(test-prop :input "(a[* 3:4])[* 5:6]"
           :expect (:repeat (:repeat (id "a") (:[*] 3 4))
                    (:[*] 5 6)))

(test-prop :input "not a[*]"
           :expect (:not (:repeat (id "a")
                          (:[*] 0 (key :vl-$)))))

(test-prop :input "always a and b[*]"
           :expect (:always (no-range)
                    (:and (id "a")
                     (:repeat (id "b") (:[*] 0 (key :vl-$))))))

(test-prop :input "always a ##1 b[*]"
           :expect (:always (no-range)
                    (:then (id "a") (:range 1 1)
                     (:repeat (id "b") (:[*] 0 (key :vl-$))))))


;; basic tests for sequence match item assignment stuff

(test-prop :input "(a,b++)"
           :expect (:assign (id "a")
                    (:vl-unary-postinc nil (id "b"))))

(test-prop :input "(a,b++,c++)"
           :expect (:assign (id "a")
                    (:vl-unary-postinc nil (id "b"))
                    (:vl-unary-postinc nil (id "c"))))

(test-prop :input "(a,++b,c=3)"
           :expect (:assign (id "a")
                    (:vl-unary-preinc nil (id "b"))
                    (:vl-binary-assign nil (id "c") 3)))

(test-prop :input "(a,++b,c*=3)"
           :expect (:assign (id "a")
                    (:vl-unary-preinc nil (id "b"))
                    (:vl-binary-timesassign nil (id "c") 3)))

(test-prop :input "(always a,++b,c*=3)"
           :expect (:assign (:always (no-range) (id "a"))
                    (:vl-unary-preinc nil (id "b"))
                    (:vl-binary-timesassign nil (id "c") 3)))

(test-prop :input "(always a,++b,c*=3)[*3:4]"
           :expect (:repeat (:assign (:always (no-range) (id "a"))
                             (:vl-unary-preinc nil (id "b"))
                             (:vl-binary-timesassign nil (id "c") 3))
                    (:[*] 3 4)))

(test-prop :input "(always a,b/=2,foo(c,d))[*3:4]"
           :expect (:repeat (:assign (:always (no-range) (id "a"))
                             (:vl-binary-divassign nil (id "b") 2)
                             (:vl-funcall nil "foo" (id "c") (id "d")))
                    (:[*] 3 4)))

(test-prop :input "(a, b + c)" ;; not a valid assignment/increment
           :successp nil)



;; basic tests of clocking event stuff

(test-prop :input "@(posedge clk) a"
           :expect (:clock ((:vl-posedge (id "clk")))
                    (id "a")))

(test-prop :input "@(posedge clk or edge clk2) a"
           :expect (:clock ((:vl-posedge (id "clk"))
                            (:vl-edge (id "clk2")))
                    (id "a")))

(test-prop :input "@(posedge clk or edge clk2) a or b"
           :expect (:clock ((:vl-posedge (id "clk"))
                            (:vl-edge (id "clk2")))
                    (:or (id "a") (id "b"))))

(test-prop :input "@(posedge clk or edge clk2) a until b"
           :expect (:clock ((:vl-posedge (id "clk"))
                            (:vl-edge (id "clk2")))
                    (:until (id "a") (id "b"))))

(test-prop :input "@(posedge clk or edge clk2) not always a until b"
           :expect (:clock ((:vl-posedge (id "clk"))
                            (:vl-edge (id "clk2")))
                    (:not (:always (no-range)
                           (:until (id "a") (id "b"))))))


;; basic tests of sequence instances
;; This is always going to be janky because it's totally ambiguous with
;; function calls.

(test-prop :input "foo(x,y,z)"
           :expect (:vl-funcall nil "foo"
                    (id "x")
                    (id "y")
                    (id "z")))

(test-prop :input "foo(x and y,y,z)"
           :expect (:inst "foo"
                    (:prop nil <- (:and (id "x") (id "y")))
                    (:prop nil <- (id "y"))
                    (:prop nil <- (id "z"))))

(test-prop :input "foo(x, y and z)"
           :expect (:inst "foo"
                    (:prop nil <- (id "x"))
                    (:prop nil <- (:and (id "y") (id "z")))))

(test-prop :input "foo(x, .a(y and z))"
           :expect (:inst "foo"
                    (:prop nil <- (id "x"))
                    (:prop "a" <- (:and (id "y") (id "z")))))

(test-prop :input "foo(.a(x), .b(y), .c())"
           :expect (:vl-funcall nil "foo"
                    ("a" (id "x"))
                    ("b" (id "y"))
                    ("c" nil)))

(test-prop :input "foo(.a(x), .b(posedge clk or negedge resetb), .c())"
           :expect (:inst "foo"
                    (:prop "a" <- (id "x"))
                    (:event "b" <- ((:vl-posedge (id "clk"))
                                    (:vl-negedge (id "resetb"))))
                    (:blank "c")))

(test-prop :input "foo(a, b, , .c(posedge clk or negedge resetb), .d())"
           :expect (:inst "foo"
                    (:prop nil <- (id "a"))
                    (:prop nil <- (id "b"))
                    (:blank nil)
                    (:event "c" <- ((:vl-posedge (id "clk"))
                                    (:vl-negedge (id "resetb"))))
                    (:blank "d")))

(test-prop :input "foo.bar(a, b, c)"
           :expect (:vl-funcall nil (:dot "foo" "bar")
                    (id "a") (id "b") (id "c")))

(test-prop :input "foo.bar(.a(1), .b(2))"
           :expect (:vl-funcall nil (:dot "foo" "bar")
                    ("a" 1) ("b" 2)))

(test-prop :input "foo.bar(1, .b(2))"
           :expect (:vl-funcall nil (:dot "foo" "bar") 1 ("b" 2)))

(test-prop :input "foo.bar(.a(posedge foo), .b(2))"
           :expect (:inst (:dot "foo" "bar")
                    (:event "a" <- ((:vl-posedge (id "foo"))))
                    (:prop "b" <- 2)))

(test-prop :input "foo.bar(posedge foo, .b(2))"
           :expect (:inst (:dot "foo" "bar")
                    (:event nil <- ((:vl-posedge (id "foo"))))
                    (:prop "b" <- 2)))

(test-prop :input "foo.bar((posedge foo or posedge bar), .b(2))"
           :expect (:inst (:dot "foo" "bar")
                    (:event nil <- ((:vl-posedge (id "foo"))
                                    (:vl-posedge (id "bar"))))
                    (:prop "b" <- 2)))

(test-prop :input "foo.bar(posedge foo or posedge bar, .b(2))"
           ;; I mean, maybe this should work, but is it a property expression
           ;; or is it an edge expression?  what a mess
           :successp nil)


