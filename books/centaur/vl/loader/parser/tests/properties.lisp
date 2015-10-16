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

(local (defthm vl-distweighttype-p-forward
         (implies (vl-distweighttype-p x)
                  (or (equal x :vl-weight-each)
                      (equal x :vl-weight-total)))
         :rule-classes :forward-chaining))

(local (defthm vl-distitem->type-forward
         (implies (vl-distweighttype-p x)
                  (or (equal x :vl-weight-each)
                      (equal x :vl-weight-total)))
         :rule-classes :forward-chaining))

(define vl-pretty-distitem ((x vl-distitem-p))
  (b* (((vl-distitem x)))
    (append (list (vl-pretty-expr x.left))
            (and x.right
                 (list (vl-pretty-expr x.right)))
            (case x.type
              (:vl-weight-each  '(:=))
              (:vl-weight-total '(:/)))
            (list (vl-pretty-expr x.weight)))))

(defprojection vl-pretty-distlist ((x vl-distlist-p))
  (vl-pretty-distitem x))

(define vl-pretty-exprdist ((x vl-exprdist-p))
  (b* (((vl-exprdist x))
       ((unless (consp x.dist))
        (vl-pretty-expr x.expr)))
    (list* :dist
           (vl-pretty-expr x.expr)
           (vl-pretty-distlist x.dist))))

(defparser-top vl-parse-expression-or-dist :resulttype vl-exprdist-p)

(define vl-pretty-exprdistlist ((x vl-exprdistlist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-exprdist (car x))
          (vl-pretty-exprdistlist (cdr x)))))


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





(define vl-pretty-repetition ((x vl-repetition-p))
  (b* (((vl-repetition x)))
    (list* (case x.type
             (:vl-repetition-consecutive    :[*])
             (:vl-repetition-goto           :[->])
             (:vl-repetition-nonconsecutive :[=]))
           (vl-pretty-expr x.left)
           (if x.right
               (list (vl-pretty-expr x.right))
             nil))))

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


(defines vl-pretty-propexpr

  (define vl-pretty-propexpr ((x vl-propexpr-p))
    :measure (vl-propexpr-count x)
    (vl-propexpr-case x
      (:vl-propcore (vl-pretty-exprdist x.guts))
      (:vl-propinst (list* :inst
                           (vl-pretty-scopeexpr x.ref)
                           (vl-pretty-propactuallist x.args)))
      (:vl-propthen (list :then
                          (vl-pretty-propexpr x.left)
                          (vl-pretty-range x.delay)
                          (vl-pretty-propexpr x.right)))
      (:vl-proprepeat (list :repeat
                            (vl-pretty-propexpr x.seq)
                            (vl-pretty-repetition x.reps)))
      (:vl-propassign (list* :assign
                             (vl-pretty-propexpr x.seq)
                             (vl-pretty-exprlist x.items)))
      (:vl-propthroughout (list :throughout
                                (vl-pretty-exprdist x.left)
                                (vl-pretty-propexpr x.right)))
      (:vl-propclock (list :clock
                           (vl-pretty-evatomlist x.trigger)
                           (vl-pretty-propexpr x.then)))
      (:vl-propunary (list (case x.op
                             (:vl-prop-firstmatch :firstmatch)
                             (:vl-prop-not        :not)
                             (:vl-prop-strong     :strong)
                             (:vl-prop-weak       :weak))
                           (vl-pretty-propexpr x.arg)))
      (:vl-propbinary (list (case x.op
                              (:vl-prop-and           :and)
                              (:vl-prop-intersect     :intersect)
                              (:vl-prop-or            :or)
                              (:vl-prop-within        :within)
                              (:vl-prop-iff           :iff)
                              (:vl-prop-until         :until)
                              (:vl-prop-suntil        :s_until)
                              (:vl-prop-untilwith     :until_with)
                              (:vl-prop-suntilwith    :s_until_with)
                              (:vl-prop-word-implies  :implies)
                              (:vl-prop-thin-implies  :->)
                              (:vl-prop-fat-implies   :=>)
                              (:vl-prop-thin-follows  :#-#)
                              (:vl-prop-fat-follows   :#=#))
                            (vl-pretty-propexpr x.left)
                            (vl-pretty-propexpr x.right)))
      (:vl-propalways (list (if x.strongp :s_always :always)
                            (vl-pretty-maybe-range x.range)
                            (vl-pretty-propexpr x.prop)))
      (:vl-propeventually (list (if x.strongp :s_eventually :eventually)
                                (vl-pretty-maybe-range x.range)
                                (vl-pretty-propexpr x.prop)))
      (:vl-propaccept (list (case x.op
                              (:vl-prop-accepton      :accept_on)
                              (:vl-prop-syncaccepton  :sync_accept_on)
                              (:vl-prop-rejecton      :reject_on)
                              (:vl-prop-syncrejecton  :sync_reject_on))
                            (vl-pretty-exprdist x.condition)
                            (vl-pretty-propexpr x.prop)))
      (:vl-propnexttime (list (if x.strongp :s_nexttime :nexttime)
                              (vl-pretty-maybe-expr x.expr)
                              (vl-pretty-propexpr x.prop)))
      (:vl-propif (list :if
                        (vl-pretty-exprdist x.condition)
                        (vl-pretty-propexpr x.then)
                        (vl-pretty-propexpr x.else)))
      (:vl-propcase (list :case
                          (vl-pretty-exprdist x.condition)
                          (vl-pretty-propcaseitemlist x.cases)))))

  (define vl-pretty-propactual ((x vl-propactual-p))
    :measure (vl-propactual-count x)
    (vl-propactual-case x
      (:blank (list :blank x.name))
      (:event (list :event x.name '<- (vl-pretty-evatomlist x.evatoms)))
      (:prop  (list :prop x.name '<- (vl-pretty-propexpr x.prop)))))

  (define vl-pretty-propactuallist ((x vl-propactuallist-p))
    :measure (vl-propactuallist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-propactual (car x))
            (vl-pretty-propactuallist (cdr x)))))

  (define vl-pretty-propcaseitem ((x vl-propcaseitem-p))
    :measure (vl-propcaseitem-count x)
    (b* (((vl-propcaseitem x)))
      (list :case
            (vl-pretty-exprdistlist x.match)
            :do
            (vl-pretty-propexpr x.prop))))

  (define vl-pretty-propcaseitemlist ((x vl-propcaseitemlist-p))
    :measure (vl-propcaseitemlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-propcaseitem (car x))
            (vl-pretty-propcaseitemlist (cdr x))))))

(defparser-top vl-parse-property-expr :resulttype vl-propexpr-p)


(defmacro test-prop (&key input expect (successp 't) (extra 'nil))
  `(assert! (b* ((config *vl-default-loadconfig*)
                 (tokens (make-test-tokens ,input))
                 (pstate (make-vl-parsestate))
                 ((mv erp val ?tokens (vl-parsestate pstate))
                  (vl-parse-property-expr-top))
                 ((when erp)
                  (cw "ERP is ~x0.~%" erp)
                  (not ,successp)))
              (cw "VAL is ~x0.~%" val)
              (and ,successp
                   (vl-propexpr-p val)
                   (not pstate.warnings)
                   (or ',extra
                       (not tokens)
                       (cw "Extra tokens not expected?"))
                   (or (equal ',expect (vl-pretty-propexpr val))
                       (cw "Expected ~x0~%" ',expect)
                       (cw "Got:     ~x0~%" (vl-pretty-propexpr val)))))))

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


;; Interleave s_nexttime and always

;; BOZO these should be working I think.

(test-prop :input "s_nexttime always good"
           :expect (:s_nexttime nil
                    (:always (no-range) (id "good"))))

(test-prop :input "s_nexttime [1] always good"
           :expect (:s_nexttime 1
                    (:always (no-range) (id "good"))))

(test-prop :input "always [1:2] s_nexttime [3] good"
           :expect (:always (:range 1 2)
                    (:s_nexttime 3 (id "good"))))

(test-prop :input "always [1:2] (s_nexttime [3:4] good)"
           :expect (:always (:range 1 2)
                    (:s_nexttime (:range 3 4) (id "good"))))

(test-prop :input "(always [1:2] (s_nexttime [3:4] good))"
           :expect (:always (:range 1 2)
                    (:s_nexttime (:range 3 4) (id "good"))))




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
           ;; this must fail because strong can't be nested: it takes
           ;; a sequence_expr as an argument, not a property_expr.
           :successp nil)


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
           ;; this must fail because weak can't be nested: it takes
           ;; a sequence_expr as an argument, not a property_expr.
           :successp nil)


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
           )
           :expect (:until
                    (:not (:not (id "r1")))
                    (id "r2")))

