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

(in-package "FGL")

(include-book "bfr")
(include-book "arith-base")
(include-book "logicman")
(include-book "clause-processors/unify-subst" :dir :system)

(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable logcar logcdr)))

(fty::defmap glcp-unify-alist :key-type symbolp :val-type gl-object)

(define glcp-unify-alist-bfrlist ((x glcp-unify-alist-p))
  :returns (bfrlist)
  (if (atom x)
      nil
    (append (and (mbt (and (consp (car x))
                           (symbolp (caar x))))
                 (gl-object-bfrlist (cdar x)))
            (glcp-unify-alist-bfrlist (cdr x))))
  ///
  (local (in-theory (enable glcp-unify-alist-fix))))

(define glcp-unify-concrete ((pat pseudo-termp)
                             (x) ;; value
                             (alist glcp-unify-alist-p))
  :returns (mv flag
               (new-alist glcp-unify-alist-p))
  :verify-guards nil
  (b* ((alist (glcp-unify-alist-fix alist))
       ((when (acl2::variablep pat))
        (if (and pat (mbt (symbolp pat)))
            (b* ((pair (hons-assoc-equal pat alist))
                 ((unless pair)
                  (mv t (cons (cons pat (g-concrete x)) alist)))
                 (obj (cdr pair)))
              (gl-object-case obj
                :g-concrete (if (equal obj.val x)
                                (mv t alist)
                              (mv nil nil))
                :otherwise (mv nil nil)))
          (if (eq x nil)
              (mv t alist)
            (mv nil nil))))
       ((when (acl2::fquotep pat))
        (if (hons-equal (acl2::unquote pat) x)
            (mv t alist)
          (mv nil nil)))
       (fn (acl2::ffn-symb pat))
       ((when (or (eq fn 'intcons)
                  (eq fn 'intcons*)))
        (b* (((unless (int= (len pat) 3)) (mv nil nil))
             ((unless (integerp x)) (mv nil nil))
             ((when (and (or (eql x -1) (eql x 0))
                         (eq fn 'intcons)))
              (mv nil nil))
             (bitvar (second pat))
             ((unless (and (acl2::variablep bitvar)
                           bitvar
                           (mbt (symbolp bitvar))))
              (mv nil nil))
             (alist (cons (cons bitvar (acl2::bit->bool (logcar x))) alist)))
          (glcp-unify-concrete (third pat) (logcdr x) alist)))
       ((when (eq fn 'cons))
        (b* (((unless (int= (len pat) 3)) (mv nil nil))
             ((unless (consp x)) (mv nil nil))
             ((mv car-ok alist)
              (glcp-unify-concrete (second pat) (car x) alist))
             ((unless car-ok) (mv nil nil)))
          (glcp-unify-concrete (third pat) (cdr x) alist))))
    (mv nil nil))
  ///
  (verify-guards glcp-unify-concrete)

  (defret bfrlist-of-<fn>
    (implies (not (member b (glcp-unify-alist-bfrlist alist)))
             (not (member b (glcp-unify-alist-bfrlist new-alist))))
    :hints(("Goal" :in-theory (enable glcp-unify-alist-bfrlist)))))


(defines glcp-unify-term/gobj
  (define glcp-unify-term/gobj ((pat pseudo-termp)
                                (x gl-object-p)
                                (alist glcp-unify-alist-p))
  :returns (mv flag
               (new-alist glcp-unify-alist-p))
  :measure (acl2-count pat)
   (b* ((alist (glcp-unify-alist-fix alist))
        (x (gl-object-fix x))
        ((when (acl2::variablep pat))
         (if (and pat (mbt (symbolp pat)))
             (let ((pair (hons-assoc-equal pat alist)))
               (if pair
                   (if (equal x (cdr pair))
                       (mv t alist)
                     (mv nil nil))
                 (mv t (cons (cons pat x) alist))))
           (if (eq x nil) (mv t alist) (mv nil nil))))
        
        ((when (acl2::fquotep pat))
         (gl-object-case x
           :g-concrete (if (hons-equal x.val (acl2:unquote pat))
                           (mv t alist)
                         (mv nil nil))
           :otherwise (mv nil nil)))
        ((when (gl-object-case x :g-concrete))
         (glcp-unify-concrete pat x.val alist))
        (fn (acl2::ffn-symb pat))
        ((when (and (eq fn 'if)
                    (eql (len pat) 4)
                    (gl-object-case x :g-ite)))
         (b* (((g-ite x))
              ((mv ok alist)
               (glcp-unify-term/gobj (second pat) x.test alist))
              ((unless ok) (mv nil nil))
              ((mv ok alist)
               (glcp-unify-term/gobj (third pat) x.then alist))
              ((unless ok) (mv nil nil)))
           (glcp-unify-term/gobj (fourth pat) x.else alist)))
        ((when (and (or (eq fn 'acl2::logcons$inline)
                        (eq fn 'logcons*))
                    (int= (len pat) 3)
                    (gl-object-case x :g-integer)))
         (b* ((bits (g-integer->bits x))
              ((mv first rest end) (first/rest/end (acl2::list-fix bits)))
              ((when (and end (not (eq fn 'logcons*))))
               (mv nil nil))
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
