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
(include-book "../../mlib/welltyped")
(local (include-book "../../util/arithmetic"))

(define vl-condition-fix
  ((condition (and (vl-expr-p condition)
                   (vl-expr->finaltype condition)
                   (posp (vl-expr->finalwidth condition)))))
  :returns (rhs :hyp :fguard
                (and (vl-expr-p rhs)
                     (equal (vl-expr->finalwidth rhs) 1)
                     (equal (vl-expr->finaltype rhs) :vl-unsigned)))
  :parents (if-statements)
  :short "Construct a one-bit wide expression that is equivalent to
@('condition') in the context of @('if (condition) ...')."

  :long "<p>This function produces an aesthetically nice expression that is
equivalent to @('condition') in the context of an if statement.</p>

<p>When @('condition') is wider than 1 bit, then @('if (condition) ...') is
the same as @('if (|condition) ...').</p>

<p>We build @('|condition') only if we have to.  That is, if @('condition') is
only one bit wide to begin with, then we just return it unchanged.</p>"

  (if (and (eql (vl-expr->finalwidth condition) 1)
           (eq (vl-expr->finaltype condition) :vl-unsigned))
      condition
    (make-vl-nonatom :op         :vl-unary-bitor
                     :args       (list condition)
                     :finalwidth 1
                     :finaltype  :vl-unsigned))
  ///
  (local (in-theory (enable vl-expr-welltyped-p)))
  (defthm vl-expr-welltyped-p-of-vl-condition-fix
    (implies (and (vl-expr-welltyped-p condition)
                  (force (vl-expr-p condition))
                  (force (vl-expr->finaltype condition))
                  (force (posp (vl-expr->finalwidth condition))))
             (vl-expr-welltyped-p (vl-condition-fix condition)))))


(define vl-condition-neg
  ((condition (and (vl-expr-p condition)
                   (posp (vl-expr->finalwidth condition))
                   (vl-expr->finaltype condition))))
  :returns (rhs :hyp :fguard
                (and (vl-expr-p rhs)
                     (equal (vl-expr->finalwidth rhs) 1)
                     (equal (vl-expr->finaltype rhs) :vl-unsigned)))
  :parents (if-statements)
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
  :parents (if-statements)
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
