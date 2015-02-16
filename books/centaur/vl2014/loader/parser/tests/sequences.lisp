; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "base")
(include-book "../sequences")

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
  (b* (((vl-exprdist x)))
    (list (vl-pretty-expr x.expr)
          :dist
          (vl-pretty-distlist x.dist))))

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
               :expect ((id "a") :dist nil))

(test-exprdist :input "a + b"
               :expect ((:vl-binary-plus nil (id "a") (id "b")) :dist nil))

(test-exprdist :input "a dist"     ;; not even {}
               :successp nil)

(test-exprdist :input "a dist {}"  ;; need at least one expr
               :successp nil)

(test-exprdist :input "a dist { 5 }"
               :expect ((id "a") :dist ((5 := 1))))

(test-exprdist :input "a dist { 5, 9 }"
               :expect ((id "a") :dist ((5 := 1)
                                        (9 := 1))))

(test-exprdist :input "a dist { 5, 9, }"  ;; extra comma
               :successp nil)

(test-exprdist :input "a dist { 5, 9 "  ;; forgot closing
               :successp nil)

(test-exprdist :input "a dist { 5, 9 := 2}"
               :expect ((id "a") :dist ((5 := 1) (9 := 2))))

(test-exprdist :input "a dist { 5 := 6, 9 := 2}"
               :expect ((id "a") :dist ((5 := 6) (9 := 2))))

(test-exprdist :input "a dist { [5:6] }"
               :expect ((id "a") :dist ((5 6 := 1))))

(test-exprdist :input "a dist { [5:6] := 3}"
               :expect ((id "a") :dist ((5 6 := 3))))

(test-exprdist :input "a dist { [5:6] := 3, 100 := 4}"
               :expect ((id "a") :dist ((5 6 := 3)
                                        (100 := 4))))

(test-exprdist :input "a dist { [5:6] := 3, [100:102] := 4}"
               :expect ((id "a") :dist ((5 6 := 3)
                                        (100 102 := 4))))

(test-exprdist :input "a dist { [5:6] := 3, [c:d] := 4}"
               :expect ((id "a") :dist ((5 6 := 3)
                                        ((id "c") (id "d") := 4))))


(test-exprdist :input "a dist { 5 :/ 3 }"
               :expect ((id "a") :dist ((5 :/ 3))))

(test-exprdist :input "a dist { 5 :/ 3, }" ;; extra comma
               :successp nil)

(test-exprdist :input "a dist { [5:6] := 3, 100 :/ 4}"
               :expect ((id "a") :dist ((5 6 := 3) (100 :/ 4))))

(test-exprdist :input "a dist { [5:6] :/ 3, 100 :/ 4}"
               :expect ((id "a") :dist ((5 6 :/ 3) (100 :/ 4))))





(define vl-pretty-cycledelayrange ((x vl-cycledelayrange-p))
  (b* (((vl-cycledelayrange x)))
    (list* :del
           (vl-pretty-expr x.left)
           (and x.right
                (list (vl-pretty-expr x.right))))))

(defparser-top vl-parse-cycledelayrange :resulttype vl-cycledelayrange-p)

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
                   (vl-cycledelayrange-p val)
                   (not pstate.warnings)
                   (or ',extra
                       (not tokens)
                       (cw "Extra tokens not expected?"))
                   (or (equal ',expect (vl-pretty-cycledelayrange val))
                       (cw "Expected ~x0~%" ',expect)
                       (cw "Got:     ~x0~%" (vl-pretty-cycledelayrange val)))))))

(test-cycledelayrange :input "" :successp nil)
(test-cycledelayrange :input "#" :successp nil)
(test-cycledelayrange :input "##" :successp nil)
(test-cycledelayrange :input "##[" :successp nil)
(test-cycledelayrange :input "##[3" :successp nil)
(test-cycledelayrange :input "##[3:4" :successp nil)
(test-cycledelayrange :input "##[3]" :successp nil)

(test-cycledelayrange :input "##3" :expect (:del 3))
(test-cycledelayrange :input "##a" :expect (:del (id "a")))

(test-cycledelayrange :input "##[3:4]" :expect (:del 3 4))
(test-cycledelayrange :input "##[3:$]" :expect (:del 3 (key :vl-$)))

;; BOZO it's not clear to me whether whitespace should be allowed here.  We
;; should probably compare this to what other Verilog tools support.
(test-cycledelayrange :input "##[+]"    :expect (:del 1 (key :vl-$)))
(test-cycledelayrange :input "##[+ ]"   :expect (:del 1 (key :vl-$)))
(test-cycledelayrange :input "##[ +]"   :expect (:del 1 (key :vl-$)))
(test-cycledelayrange :input "##[ + ]"  :expect (:del 1 (key :vl-$)))
(test-cycledelayrange :input "## [+ ]"  :expect (:del 1 (key :vl-$)))
(test-cycledelayrange :input "## [ +]"  :expect (:del 1 (key :vl-$)))
(test-cycledelayrange :input "## [ + ]" :expect (:del 1 (key :vl-$)))

(test-cycledelayrange :input "##[*]"    :expect (:del 0 (key :vl-$)))
(test-cycledelayrange :input "##[* ]"   :expect (:del 0 (key :vl-$)))
(test-cycledelayrange :input "##[ *]"   :expect (:del 0 (key :vl-$)))
(test-cycledelayrange :input "##[ * ]"  :expect (:del 0 (key :vl-$)))
(test-cycledelayrange :input "## [* ]"  :expect (:del 0 (key :vl-$)))
(test-cycledelayrange :input "## [ *]"  :expect (:del 0 (key :vl-$)))
(test-cycledelayrange :input "## [ * ]" :expect (:del 0 (key :vl-$)))

;; BOZO we don't allow space between the #s, is that OK?
(test-cycledelayrange :input "# #[+]" :successp nil)
(test-cycledelayrange :input "# #[*]" :successp nil)



(define vl-pretty-repetition ((x vl-repetition-p))
  (b* (((vl-repetition x)))
    (list* x.type
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

(test-repetition :input "[*]" :expect (:vl-repetition-consecutive 0 (key :vl-$)))
(test-repetition :input "[+]" :expect (:vl-repetition-consecutive 1 (key :vl-$)))

(test-repetition :input "[*3]"   :expect (:vl-repetition-consecutive 3))
(test-repetition :input "[*3:4]" :expect (:vl-repetition-consecutive 3 4))
(test-repetition :input "[*3:$]" :expect (:vl-repetition-consecutive 3 (key :vl-$)))
(test-repetition :input "[* 3]"   :expect (:vl-repetition-consecutive 3))
(test-repetition :input "[* 3:4]" :expect (:vl-repetition-consecutive 3 4))
(test-repetition :input "[* 3:$]" :expect (:vl-repetition-consecutive 3 (key :vl-$)))

(test-repetition :input "[->3]"   :expect (:vl-repetition-goto 3))
(test-repetition :input "[->3:4]" :expect (:vl-repetition-goto 3 4))
(test-repetition :input "[->3:$]" :expect (:vl-repetition-goto 3 (key :vl-$)))
(test-repetition :input "[-> 3]"   :expect (:vl-repetition-goto 3))
(test-repetition :input "[-> 3:4]" :expect (:vl-repetition-goto 3 4))
(test-repetition :input "[-> 3:$]" :expect (:vl-repetition-goto 3 (key :vl-$)))

(test-repetition :input "[=3]"   :expect (:vl-repetition-nonconsecutive 3))
(test-repetition :input "[=3:4]" :expect (:vl-repetition-nonconsecutive 3 4))
(test-repetition :input "[=3:$]" :expect (:vl-repetition-nonconsecutive 3 (key :vl-$)))
(test-repetition :input "[= 3]"   :expect (:vl-repetition-nonconsecutive 3))
(test-repetition :input "[= 3:4]" :expect (:vl-repetition-nonconsecutive 3 4))
(test-repetition :input "[= 3:$]" :expect (:vl-repetition-nonconsecutive 3 (key :vl-$)))

