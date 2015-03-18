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
(include-book "centaur/svex/vl-expr" :dir :system)
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc scopesubst
  :parents (unparameterization)
  :short "Scope aware substitution that replaces occurrences of resolved
parameters with their values.")

(local (xdoc::set-default-parents scopesubst))

(define vl-patternkey-consteval-index ((x vl-expr-p)
                                       (conf vl-svexconf-p))
  ;; We throw out the warnings from this because we don't want to get warned if
  ;; a struct field name is not a valid variable.
  :returns (mv (warnings vl-warninglist-p)
               (changedp)
               (new-x (and (vl-expr-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-expr-fix x))))))
  (b* (((mv & changedp new-x) (vl-expr-consteval x conf)))
    (mv nil changedp new-x)))

(define vl-maybe-expr-consteval ((x vl-maybe-expr-p)
                                 (conf vl-svexconf-p))
  ;; We throw out the warnings from this because we don't want to get warned if
  ;; a struct field name is not a valid variable.
  :returns (mv (warnings vl-warninglist-p)
               (changedp)
               (new-x (and (vl-maybe-expr-p new-x)
                           (implies (not changedp)
                                    (equal new-x (vl-maybe-expr-fix x))))))
  (if x
      (vl-expr-consteval x conf)
    (mv nil nil nil)))

(fty::defvisitor-template resolve-indices ((x :object)
                                           (conf vl-svexconf-p))
  ;; BOZO When we were defining this by hand we used to arrange so that we only
  ;; reconsed the structures when they were actually updated (in the :exec
  ;; part, whereas the :logic part always rebuilt them). That would require
  ;; adding such a feature to defvisitor.  Might there be some useful way to
  ;; generalize this?
  :returns (mv (warnings (:join (append-without-guard warnings1 warnings)
                          :tmp-var warnings1
                          :initial nil)
                         vl-warninglist-p)
               (changedp (:join (or changedp1 changedp)
                          :tmp-var changedp1
                          :initial nil))
               (new-x (:update
                       (mbe :logic :update
                            :exec (if changedp
                                      :update
                                    x))
                       :type (and (:type new-x)
                                  (implies (not changedp)
                                           (equal new-x
                                                  (:fix x)))))))
  ;; (and (vl-range-p new-x)
  ;;      (implies (not changedp)
  ;;               (equal new-x (vl-range-fix x))))
  :prod-fns ((vl-range             (msb vl-expr-consteval)
                                   (lsb vl-expr-consteval))
             (vl-hidindex          (indices vl-exprlist-consteval))
             (vl-plusminus         (base vl-expr-consteval)
                                   (width vl-expr-consteval))
             (vl-arrayrange-index  (expr vl-expr-consteval))
             (vl-valuerange-single (expr vl-expr-consteval))
             (vl-patternkey-expr   (key vl-patternkey-consteval-index))
             (vl-assignpat-repeat  (reps vl-expr-consteval))
             (vl-index             (indices vl-exprlist-consteval))
             (vl-multiconcat       (reps vl-expr-consteval))
             (vl-explicitvalueparam (default vl-maybe-expr-consteval))
             (vl-implicitvalueparam (default vl-maybe-expr-consteval))
             (vl-stream            (size vl-maybe-expr-consteval)))
  :field-fns ((generates :skip))
  :type-fns ((vl-atts (lambda (x conf) (declare (ignore conf)) (mv nil nil x))))
  :fnname-template <type>-resolve-indices)


(set-bogus-mutual-recursion-ok t)

;; (local (in-theory (disable 
;;         (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-CORETYPE)
;;         (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-ENUM)
;;         (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-STRUCT)
;;         (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-UNION)
;;         (:REWRITE VL-DATATYPE-PDIMS-WHEN-VL-USERTYPE)
;;         (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-CORETYPE)
;;         (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-ENUM)
;;         (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-STRUCT)
;;         (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-UNION)
;;         (:REWRITE VL-DATATYPE-UDIMS-WHEN-VL-USERTYPE)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-BINARY)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-CALL)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-CAST)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-CONCAT)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-INDEX)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-INSIDE)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-MINTYPMAX)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-MULTICONCAT)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-PATTERN)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-QMARK)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-SPECIAL)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-STREAM)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-TAGGED)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-UNARY)
;;         (:REWRITE VL-EXPR-TYPE-WHEN-VL-VALUE))))

(local (in-theory (disable (tau-system)
                           vl-warninglist-p-when-subsetp-equal
                           vl-warninglist-p-when-not-consp
                           double-containment
                           not)))

(local (defthm consp-car-of-keyvallist
         (implies (and (vl-keyvallist-p x)
                       (consp x))
                  (consp (car x)))))

(local (defthm consp-car-of-vl-atts
         (implies (and (vl-atts-p x)
                       (consp x))
                  (consp (car x)))))

(local (defthm consp-car-of-vl-atts
         (implies (and (vl-atts-p x)
                       (consp x))
                  (consp (car x)))))

(local (in-theory (disable (vl-packeddimension-unsized)
                           (vl-partselect-none)
                           (vl-patternkey-default)
                           (vl-arrayrange-none)
                           acl2::true-listp-append
                           (:t binary-append)
                           acl2::append-atom-under-list-equiv
                           acl2::consp-when-member-equal-of-cons-listp
                           acl2::consp-when-member-equal-of-atom-listp
                           acl2::consp-append)))


(with-output :off (event prove)
  (fty::defvisitors vl-resolve-indices
    :types (vl-design vl-genblob)
    :template resolve-indices))

