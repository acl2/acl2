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
(include-book "../../mlib/welltyped")
(local (include-book "../../util/arithmetic"))

(define vl-condition-fix
  ((condition vl-expr-p))
  :guard (and (vl-expr->finaltype condition)
              (posp (vl-expr->finalwidth condition)))
  :returns (rhs :hyp :fguard
                (and (vl-expr-p rhs)
                     (equal (vl-expr->finalwidth rhs) 1)
                     (equal (vl-expr->finaltype rhs) :vl-unsigned)))
  :parents (vl-ifstmt)
  :short "Construct a one-bit wide expression that is equivalent to
@('condition') in the context of @('if (condition) ...')."

  :long "<p>This function produces an aesthetically nice expression that is
equivalent to @('condition') in the context of an if statement.</p>

<p>When @('condition') is wider than 1 bit, then @('if (condition) ...') is
the same as @('if (|condition) ...').</p>

<p>We build @('|condition') only if we have to.  That is, if @('condition') is
only one bit wide to begin with, then we just return it unchanged.</p>"

  (b* ((condition (vl-expr-fix condition))
       ((when (and (eql (vl-expr->finalwidth condition) 1)
                   (eq (vl-expr->finaltype condition) :vl-unsigned)))
        condition))
    (make-vl-nonatom :op         :vl-unary-bitor
                     :args       (list condition)
                     :finalwidth 1
                     :finaltype  :vl-unsigned))
  ///
  (local (in-theory (enable vl-expr-welltyped-p)))
  (defthm vl-expr-welltyped-p-of-vl-condition-fix
    (implies (and (vl-expr-welltyped-p condition)
                  ;(force (vl-expr-p condition))
                  (force (vl-expr->finaltype condition))
                  (force (posp (vl-expr->finalwidth condition))))
             (vl-expr-welltyped-p (vl-condition-fix condition)))
    :hints(("Goal"
            :expand ((:free (op args atts finalwidth finaltype)
                      (vl-expr-welltyped-p
                       (make-vl-nonatom :op op
                                        :args args
                                        :atts atts
                                        :finalwidth finalwidth
                                        :finaltype finaltype))))))))

(define vl-condition-neg
  ((condition (and (vl-expr-p condition)
                   (posp (vl-expr->finalwidth condition))
                   (vl-expr->finaltype condition))))
  :returns (rhs :hyp :fguard
                (and (vl-expr-p rhs)
                     (equal (vl-expr->finalwidth rhs) 1)
                     (equal (vl-expr->finaltype rhs) :vl-unsigned)))
  :parents (vl-ifstmt)
  :short "Construct a one-bit wide expression that is equivalent to
@('!condition')."

  :long "<p>We produce an expression that is equivalent to @('!condition').</p>

<p>For compatibility with @(see oprewrite), the expression we actually generate
is:</p>

<ul>
<li>@('~(|condition)'), if @('condition') is more than 1 bit wide, or</li>
<li>@('~condition') when condition is exactly 1 bit wide.</li>
</ul>"

  (if (and (eql (vl-expr->finalwidth condition) 1)
           (eq (vl-expr->finaltype condition) :vl-unsigned))
      (make-vl-nonatom :op         :vl-unary-bitnot
                       :args       (list condition)
                       :finalwidth 1
                       :finaltype  :vl-unsigned)

    (b* ((redux (make-vl-nonatom :op         :vl-unary-bitor
                                 :args       (list condition)
                                 :finalwidth 1
                                 :finaltype :vl-unsigned)))
      (make-vl-nonatom :op         :vl-unary-bitnot
                       :args       (list redux)
                       :finalwidth 1
                       :finaltype  :vl-unsigned)))
  ///
  (local (in-theory (enable vl-expr-welltyped-p)))
  (defthm vl-expr-welltyped-p-of-vl-condition-neg
    (implies (and (vl-expr-welltyped-p condition)
                  (force (vl-expr-p condition))
                  (force (vl-expr->finaltype condition))
                  (force (posp (vl-expr->finalwidth condition))))
             (vl-expr-welltyped-p (vl-condition-neg condition)))))


(define vl-condition-merge
  ((outer-cond "may be @('nil') to say there is no outer condition"
               (or (not outer-cond)
                   (and (vl-expr-p outer-cond)
                        (vl-expr->finaltype outer-cond)
                        (posp (vl-expr->finalwidth outer-cond)))))
   (inner-cond (and (vl-expr-p inner-cond)
                    (vl-expr->finaltype inner-cond)
                    (posp (vl-expr->finalwidth inner-cond)))))
  :returns (ans "a one-bit wide expression equivalent to
                 @('outer-cond && inner-cond')"
                :hyp :fguard
                (and (vl-expr-p ans)
                     (equal (vl-expr->finalwidth ans) 1)
                     (equal (vl-expr->finaltype ans) :vl-unsigned)))
  :parents (vl-ifstmt)
  :short "Join conditions from nested @('if') expressions."
  :long "<p>For compatibility with @(see oprewrite), we actually build
something like @('(|outer-cond & |inner-cond)'), except we omit the reduction
operators where possible.</p>"
  (if (not outer-cond)
      (vl-condition-fix inner-cond)
    (make-vl-nonatom :op :vl-binary-bitand
                     :args (list (vl-condition-fix outer-cond)
                                 (vl-condition-fix inner-cond))
                     :finalwidth 1
                     :finaltype :vl-unsigned))
  ///
  (local (in-theory (enable vl-expr-welltyped-p)))
  (defthm vl-expr-welltyped-p-of-vl-condition-merge
    (implies (and (or (not outer-cond)
                      (vl-expr-welltyped-p outer-cond))
                  (vl-expr-welltyped-p inner-cond)
                  (or (not outer-cond)
                      (and (vl-expr-p outer-cond)
                           (vl-expr->finaltype outer-cond)
                           (posp (vl-expr->finalwidth outer-cond))))
                  (and (vl-expr-p inner-cond)
                       (vl-expr->finaltype inner-cond)
                       (posp (vl-expr->finalwidth inner-cond))))
             (vl-expr-welltyped-p
              (vl-condition-merge outer-cond inner-cond)))))


(define vl-safe-qmark-expr ((condition  vl-expr-p)
                            (true-expr  vl-expr-p)
                            (false-expr vl-expr-p))
  :returns (new-expr vl-expr-p :hyp :fguard)
  (b* (((unless (and (posp (vl-expr->finalwidth condition))
                     (posp (vl-expr->finalwidth true-expr))
                     (posp (vl-expr->finalwidth false-expr))
                     (eql (vl-expr->finalwidth true-expr)
                          (vl-expr->finalwidth false-expr))
                     (vl-expr->finaltype condition)
                     (vl-expr->finaltype true-expr)
                     (vl-expr->finaltype false-expr)))
        (raise "Bad sizes when trying to construct ?: expression: condition ~
                ~x0, true ~x1, false ~x2."  condition true-expr false-expr)
        |*sized-1'bx*|)
       (new-type (vl-exprtype-max (vl-expr->finaltype true-expr)
                                  (vl-expr->finaltype false-expr))))
    (make-vl-nonatom :op :vl-qmark
                     :args (list (vl-condition-fix condition)
                                 true-expr false-expr)
                     :finalwidth (vl-expr->finalwidth true-expr)
                     :finaltype new-type)))
