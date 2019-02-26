; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(include-book "bvar-db-equivs")
(include-book "bfr-arithmetic")
(include-book "glcp-unify-defs")
(include-book "centaur/meta/bindinglist" :dir :system)

;; (define glcp-unify-alist-bfrlist ((x glcp-unify-alist-p))
;;   :measure (len (glcp-unify-alist-fix x))
;;   (b* ((x (glcp-unify-alist-fix x))
;;        ((when (atom x)) nil)
;;        ((cons key val) (car x)))
;;     (append (gl-object-bfrlist val)
;;             (glcp-unify-alist-bfrlist (cdr x))))
;;   ///
;;   (defthm member-bfrlist-of-glcp-unify-alist-lookup
;;     (implies (and (not (member bfr (glcp-unify-alist-bfrlist x)))
;;                   (acl2::pseudo-var-p v))
;;              (not (member bfr (cdr (hons-assoc-equal v x))))))
  
;;   (defthm member-glcp-unify-alist-bfrlist-of-cons
;;     (implies (and (not (member bfr (glcp-unify-alist-bfrlist x)))
;;                   (not (member bfr (gl-object-bfrlist val))))
;;              (not (member bfr (glcp-unify-alist-bfrlist (cons (cons key val) x)))))))

(define glcp-interp-error (msg &key (interp-st 'interp-st)
                               (state 'state))
  :returns (mv errmsg
               result
               new-interp-st
               new-state)
  (mv msg nil interp-st state))

(defmacro glcp-value (obj)
  `(mv nil ,obj interp-st state))


;; should we look for equivalence assumptions for this object?
(define glcp-term-obj-p ((x gl-object-p))
  (declare (xargs :guard t))
  (gl-object-case x
    :g-ite t
    :g-var t
    :g-apply t
    :otherwise nil))

(define interp-st->stack-top (interp-st)
  :enabled t
  (car (interp-st->stack interp-st)))


(defines gl-interp
  (define gl-interp-test ((x pseudo-termp)
                          interp-st
                          state)
    ;; Translate a term to a GL object under the given alist substitution, preserving IFF.
    :measure (list (pos-fix (interp-st->reclimit interp-st))
                   12 0 0)
    :well-founded-relation acl2::nat-list-<
    :guard (bfr-listp (glcp-unify-alist-bfrlist alist) (interp-st->bfrstate interp-st))
    (b* ((interp-st (interp-st-decrement-reclimit interp-st))
         (current-equiv-contexts (interp-st->equiv-contexts interp-st))
         (interp-st (interp-st-update-equiv-contexts '(iff) interp-st))
         ((mv err xobj interp-st state)
          (gl-interp-term-equivs x interp-st state))
         (interp-st (interp-st-update-equiv-contexts current-equiv-contexts interp-st))
         (interp-st (interp-st-increment-reclimit interp-st))
         ((when err)
          (mv err nil interp-st state)))
      (simplify-if-test xobj interp-st state)))

  (define gl-interp-term-equivs ((x pseudo-termp)
                                 interp-st
                                 state)
    :measure (list (interp-st->reclimit interp-st) 2020 (pseudo-term-count x) 40)
    (b* (((when (zp (interp-st->reclimit interp-st)))
          (glcp-interp-error "The recursion limit ran out."))
         ((mv err xobj interp-st state)
          (gl-interp-term x interp-st state))
         ((when err) (mv err nil interp-st state))
         ((unless (glcp-term-obj-p xobj))
          (glcp-value xobj))
         (contexts (interp-st->equiv-contexts interp-st)))
      (stobj-let ((pathcond (interp-st->pathcond interp-st))
                  (logicman (interp-st->logicman interp-st))
                  (bvar-db (interp-st->bvar-db interp-st)))
                 (replacedp val pathcond)
                 (try-equivalences-loop
                  xobj contexts 100 ;; bozo, configure reclimit for try-equivalences-loop?
                  pathcond bvar-db logicman state)
                 (glcp-value val))))

  (define gl-interp-term ((x pseudo-termp)
                          interp-st
                          state)
    :measure (list (pos-fix (interp-st->reclimit interp-st))
                   2020 (pseudo-term-count x) 20)
    (b* ((interp-st (interp-st-fix interp-st)))
      (pseudo-term-case x
        :const (glcp-value (g-concrete x.val))
        :var (b* ((alist (interp-st->stack-top interp-st)))
               (glcp-value (cdr (hons-assoc-equal x.name alist))))
        :lambda
        (b* (((mv bindings body) (cmr::lambda-nest-to-bindinglist x))
             (interp-st (interp-st-duplicate-stack-top interp-st))
             (contexts (interp-st->equiv-contexts interp-st))
             (interp-st (update-interp-st->contexts nil interp-st))
             ((mv err interp-st state)
              ;; replaces the top of stack with the bindings
              (gl-interp-bindinglist bindings interp-st state))
             (interp-st (upate-interp-st->equiv-contexts contexts interp-st))
             ((when err)
              (b* ((interp-st (interp-st-pop-stack interp-st)))
                (mv err nil interp-st state)))
             ((mv err val interp-st state)
              (gl-interp-term-equivs body interp-st state))
             (interp-st (interp-st-pop-stack interp-st)))
          (mv err val interp-st state))
        :fncall 
        
         
    
