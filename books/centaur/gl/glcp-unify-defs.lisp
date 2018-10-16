; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")

(include-book "general-objects")
(local (include-book "general-object-thms"))

(verify-guards general-concrete-obj) ;; redundant

;; x is a concrete object
(defund glcp-unify-concrete (pat x alist)
  (declare (xargs :guard (pseudo-termp pat)))
  (b* (((when (atom pat))
        (if (and pat (mbt (symbolp pat)))
            (let ((pair (hons-assoc-equal pat alist)))
              (if pair
                  (if (and (general-concretep (cdr pair))
                           (equal (general-concrete-obj (cdr pair)) x))
                      (mv t alist)
                    (mv nil nil))
                (mv t (cons (cons pat (g-concrete-quote x)) alist))))
          (if (eq x nil)
              (mv t alist)
            (mv nil nil))))
       ((when (eq (car pat) 'quote))
        (if (equal (cadr pat) x)
            (mv t alist)
          (mv nil nil)))
       ((when (and (eq (car pat) 'acl2::logcons$inline)
                   (int= (len pat) 3)))
        (if (integerp x)
            (b* (((mv logcar-ok alist)
                  (glcp-unify-concrete (second pat) (logcar x) alist))
                 ((unless logcar-ok) (mv nil nil)))
              (glcp-unify-concrete (third pat) (logcdr x) alist))
          (mv nil nil)))
       ((when (and (eq (car pat) 'cons)
                   (int= (len pat) 3)))
        (if (consp x)
            (b* (((mv car-ok alist)
                  (glcp-unify-concrete (second pat) (car x) alist))
                 ((unless car-ok) (mv nil nil)))
              (glcp-unify-concrete (third pat) (cdr x) alist))
          (mv nil nil))))
    ;; ((and (eq (car pat) 'binary-+)
    ;;       (int= (len pat) 3))
    ;;  (cond ((not (acl2-numberp x))
    ;;         (mv nil nil))
    ;;        ((quotep (second pat))
    ;;         (let ((num (unquote (second pat))))
    ;;           (if (acl2-numberp num)
    ;;               (glcp-unify-concrete (third pat) (- x num) alist)
    ;;             (mv nil nil))))
    ;;        ((quotep (third pat))
    ;;         (let ((num (unquote (third pat))))
    ;;           (if (acl2-numberp num)
    ;;               (glcp-unify-concrete (second pat) (- x num) alist)
    ;;             (mv nil nil))))
    ;;        (t (mv nil nil))))
    (mv nil nil)))

(defthm symbol-alistp-glcp-unify-concrete
  (implies (and (symbol-alistp alist)
                (pseudo-termp pat))
           (symbol-alistp (mv-nth 1 (glcp-unify-concrete pat x alist))))
  :hints(("Goal" :in-theory (enable glcp-unify-concrete))))

(mutual-recursion
 (defun glcp-unify-term/gobj (pat x alist)
   (declare (xargs :guard (pseudo-termp pat)
                   :guard-debug t))
   (b* (((when (atom pat))
         (if (and pat (mbt (symbolp pat)))
             (let ((pair (hons-assoc-equal pat alist)))
               (if pair
                   (if (equal x (cdr pair))
                       (mv t alist)
                     (mv nil nil))
                 (mv t (cons (cons pat x) alist))))
           (if (eq x nil) (mv t alist) (mv nil nil))))
        
        ((when (eq (car pat) 'quote))
         (if (and (general-concretep x)
                  (equal (general-concrete-obj x) (cadr pat)))
             (mv t alist)
           (mv nil nil)))
        ((when (atom x))
         (glcp-unify-concrete pat x alist))
        ((when (eq (tag x) :g-concrete))
         (glcp-unify-concrete pat (g-concrete->obj x) alist))
        ((when (and (eq (car pat) 'if)
                    (eql (len pat) 4)
                    (eq (tag x) :g-ite)))
         (b* ((test (g-ite->test x))
              (then (g-ite->then x))
              (else (g-ite->else x))
              ((mv ok alist)
               (glcp-unify-term/gobj (second pat) test alist))
              ((unless ok) (mv nil nil))
              ((mv ok alist)
               (glcp-unify-term/gobj (third pat) then alist))
              ((unless ok) (mv nil nil)))
           (glcp-unify-term/gobj (fourth pat) else alist)))
        ((when (and (eq (car pat) 'acl2::logcons$inline)
                    (int= (len pat) 3)
                    (eq (tag x) :g-integer)))
         (b* ((bits (g-integer->bits x))
              ((mv first rest ?end) (first/rest/end (acl2::list-fix bits)))
              ((mv car-ok alist)
               (glcp-unify-term/gobj (second pat)
                                     (mk-g-integer (bfr-scons first (bfr-sterm nil)))
                                     alist))
              ((unless car-ok) (mv nil nil)))
           (glcp-unify-term/gobj (third pat)
                                 (mk-g-integer rest)
                                 alist)))
        ((when (or (eq (tag x) :g-boolean)
                   (eq (tag x) :g-integer)
                   (eq (tag x) :g-ite)
                   (eq (tag x) :g-var)))
         (mv nil nil))
        ((unless (eq (tag x) :g-apply))
         ;; cons case
         (if (and (eq (car pat) 'cons)
                  (int= (len pat) 3))
             (b* (((mv ok alist) (glcp-unify-term/gobj (cadr pat) (car x) alist))
                  ((unless ok) (mv nil nil)))
               (glcp-unify-term/gobj (caddr pat) (cdr x) alist))
           (mv nil nil)))
        ;; g-apply case remains
        ((when (equal (g-apply->fn x) (car pat)))
         (glcp-unify-term/gobj-list (cdr pat) (g-apply->args x) alist)))
     (mv nil nil)))
 (defun glcp-unify-term/gobj-list (pat x alist)
   (declare (xargs :guard (pseudo-term-listp pat)))
   (b* (((when (atom pat))
         (if (eq x nil) (mv t alist) (mv nil nil)))
        ((when (atom x)) (mv nil nil))
        ((when (g-keyword-symbolp (tag x)))
         ;;for now at least
         (mv nil nil))
        ((mv ok alist)
         (glcp-unify-term/gobj (car pat) (car x) alist))
        ((unless ok) (mv nil nil)))
     (glcp-unify-term/gobj-list (cdr pat) (cdr x) alist))))

(in-theory (disable glcp-unify-term/gobj
                    glcp-unify-term/gobj-list))
