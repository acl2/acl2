; GLMC -- Hardware model checking interface
; Copyright (C) 2017 Centaur Technology
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

(include-book "glmc-generic-defs")
(include-book "centaur/gl/gl-generic-clause-proc" :dir :system)
(include-book "centaur/gl/gl-generic-interp" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/alists/alistp" :dir :system))
(local (include-book "clause-processors/just-expand" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))

(local (in-theory (disable w)))
(local (in-theory (disable acl2::cons-car-cdr)))
  ;; (local (defthm bfr-hyp-eval-of-car-env-hack
  ;;          (implies (and (bfr-hyp-eval hyp (car env))
  ;;                        (not (consp env)))
  ;;                   (bfr-eval hyp nil))))

(local (fty::deflist nat-list :pred nat-listp :elt-type natp :true-listp t :elementp-of-nil nil))

(local (defthm glcp-generic-bvar-db-env-ok-of-base-bvar
           (implies (equal bb (base-bvar$a bvar-db))
                    (glcp-generic-bvar-db-env-ok bvar-db p bb env))
           :hints(("Goal" :in-theory (enable glcp-generic-bvar-db-env-ok)))))

(local (defthm shape-specp-lookup-in-bindings
         (implies (shape-spec-bindingsp x)
                  (shape-specp (cadr (hons-assoc-equal k x))))
         :hints(("Goal" :in-theory (enable shape-spec-bindingsp hons-assoc-equal)))))

(local (acl2::use-trivial-ancestors-check))

(std::make-returnspec-config :hints-sub-returnnames t)



(local
 (defsection glcp-generic-geval
   (local (in-theory (enable glcp-generic-geval)))
   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-shape-spec-oblig-term-correct
   ;;   shape-spec-oblig-term-correct
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-shape-spec-list-oblig-term-correct
   ;;   shape-spec-list-oblig-term-correct
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))

   (acl2::def-functional-instance
     glcp-generic-geval-gobj-to-param-space-correct
     gobj-to-param-space-correct
     ((generic-geval-ev glcp-generic-geval-ev)
      (generic-geval-ev-lst glcp-generic-geval-ev-lst)
      (generic-geval glcp-generic-geval)
      (generic-geval-list glcp-generic-geval-list))
     :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                 glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                                (glcp-generic-geval-apply))
               :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))

   (acl2::def-functional-instance
     glcp-generic-geval-gobj-to-param-space-correct-with-unparam-env
     gobj-to-param-space-correct-with-unparam-env
     ((generic-geval-ev glcp-generic-geval-ev)
      (generic-geval-ev-lst glcp-generic-geval-ev-lst)
      (generic-geval glcp-generic-geval)
      (generic-geval-list glcp-generic-geval-list))
     :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                 glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                                (glcp-generic-geval-apply))
               :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))


   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-indices-of-shape-spec-env-term
   ;;   indices-of-shape-spec-env-term
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-indices-of-shape-spec-env-term-iff
   ;;   indices-of-shape-spec-env-term-iff
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-indices-of-shape-spec-list-env-term
   ;;   indices-of-shape-spec-list-env-term
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-vars-of-shape-spec-env-term
   ;;   vars-of-shape-spec-env-term
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-vars-of-shape-spec-env-term-iff
   ;;   vars-of-shape-spec-env-term-iff
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-vars-of-shape-spec-list-env-term
   ;;   vars-of-shape-spec-list-env-term
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-alistp-car-shape-spec-env-term
   ;;   alistp-car-shape-spec-env-term
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-alistp-car-shape-spec-env-term-iff
   ;;   alistp-car-shape-spec-env-term-iff
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-alistp-car-shape-spec-list-env-term
   ;;   alistp-car-shape-spec-list-env-term
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   
   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-alistp-cdr-shape-spec-env-term
   ;;   alistp-cdr-shape-spec-env-term
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-alistp-cdr-shape-spec-env-term-iff
   ;;   alistp-cdr-shape-spec-env-term-iff
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))

   ;; (acl2::def-functional-instance
   ;;   glcp-generic-geval-alistp-cdr-shape-spec-list-env-term
   ;;   alistp-cdr-shape-spec-list-env-term
   ;;   ((sspec-geval-ev glcp-generic-geval-ev)
   ;;    (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
   ;;    (sspec-geval glcp-generic-geval)
   ;;    (sspec-geval-list glcp-generic-geval-list))
   ;;   :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
   ;;                               glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
   ;;                              (glcp-generic-geval-apply))
   ;;             :expand ((:with glcp-generic-geval (glcp-generic-geval x
   ;;                                                                    env))))))


   (acl2::def-functional-instance
     glcp-generic-geval-shape-spec-invert-correct
     shape-spec-invert-correct
     ((sspec-geval-ev glcp-generic-geval-ev)
      (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
      (sspec-geval glcp-generic-geval)
      (sspec-geval-list glcp-generic-geval-list)
      (sspec-geval-ev-alist glcp-generic-geval-ev-alist))
     :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                 glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                                (glcp-generic-geval-apply))
               :expand ((:with glcp-generic-geval (glcp-generic-geval x
                                                                      env))))))

   (acl2::def-functional-instance
     glcp-generic-geval-shape-spec-invert-iff-correct
     shape-spec-invert-iff-correct
     ((sspec-geval-ev glcp-generic-geval-ev)
      (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
      (sspec-geval glcp-generic-geval)
      (sspec-geval-list glcp-generic-geval-list)
      (sspec-geval-ev-alist glcp-generic-geval-ev-alist))
     :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                 glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                                (glcp-generic-geval-apply))
               :expand ((:with glcp-generic-geval (glcp-generic-geval x
                                                                      env))))))

   (acl2::def-functional-instance
     glcp-generic-geval-shape-spec-list-invert-correct
     shape-spec-list-invert-correct
     ((sspec-geval-ev glcp-generic-geval-ev)
      (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
      (sspec-geval glcp-generic-geval)
      (sspec-geval-list glcp-generic-geval-list)
      (sspec-geval-ev-alist glcp-generic-geval-ev-alist))
     :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                 glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                                (glcp-generic-geval-apply))
               :expand ((:with glcp-generic-geval (glcp-generic-geval x
                                                                      env))))))))

;; (define obligs-extension-p (x y)
;;   (acl2::suffixp y x)
;;   ///
;;   (defthm obligs-extension-p-transitive
;;     (implies (and (obligs-extension-p x y)
;;                   (obligs-extension-p y z))
;;              (obligs-extension-p x z))
;;     :hints(("Goal" :in-theory (enable acl2::suffixp))))

;;   (defthm obligs-extension-p-refl
;;     (obligs-extension-p x x)
;;     :hints(("Goal" :in-theory (enable acl2::suffixp))))

;;   (defthm obligs-extension-p-of-interp-function-lookup
;;     (b* (((mv err ?body ?formals new-defs)
;;           (acl2::interp-function-lookup fn defs overrides wrld)))
;;       (implies (not err)
;;                (obligs-extension-p new-defs defs)))
;;     :hints(("Goal" :in-theory (enable acl2::interp-function-lookup acl2::suffixp))))

;;   (defthm not-theoremp-when-obligs-extension-p
;;     (implies (and (not (glcp-generic-geval-ev-theoremp (acl2::interp-defs-alist-clauses y)))
;;                   (obligs-extension-p x y))
;;              (not (glcp-generic-geval-ev-theoremp (acl2::interp-defs-alist-clauses x))))
;;     :hints(("Goal" :in-theory (enable acl2::interp-defs-alist-clauses acl2::suffixp)))))

(defmacro bind-interp-st-extension (new old-var)
  `(and (bind-free (acl2::prev-stobj-binding ,new ',old-var mfc state))
        (interp-st-obligs-extension-p ,new ,old-var)))

(acl2::set-prev-stobjs-correspondence update-nth :stobjs-out (x) :formals (n v x))

(local (in-theory (disable nth update-nth)))

(define interp-st-obligs-extension-p (x y)
  :non-executable t
  :verify-guards nil
  (acl2::suffixp (nth *is-obligs* y)
                 (nth *is-obligs* x))
  ///
  (defthm interp-st-obligs-extension-p-of-interp-function-lookup
    (b* (((mv er ?body ?formals new-defs)
          (acl2::interp-function-lookup fn (nth *is-obligs* x) overrides wrld)))
      (implies (not er)
               (interp-st-obligs-extension-p (update-nth *is-obligs* new-defs x) x)))
    :hints(("Goal" :in-theory (enable acl2::interp-function-lookup acl2::suffixp))))

  (defthm interp-st-obligs-extension-p-refl
    (interp-st-obligs-extension-p x x)
    :hints(("Goal" :in-theory (enable acl2::suffixp))))

  (local (defthm suffixp-transitive
           (implies (and (acl2::suffixp x y)
                         (acl2::suffixp y z))
                    (acl2::suffixp x z))
           :hints(("Goal" :in-theory (enable acl2::suffixp)))))

  (defthm interp-st-obligs-extension-p-transitive-bind-prev
    (implies (and (bind-interp-st-extension x y)
                  (interp-st-obligs-extension-p y z))
             (interp-st-obligs-extension-p x z)))

  (local (defthm not-theoremp-when-suffixp
           (implies (and (acl2::suffixp old new)
                         (not (glcp-generic-geval-ev-theoremp
                               (conjoin-clauses
                                (acl2::interp-defs-alist-clauses old)))))
                    (not (glcp-generic-geval-ev-theoremp
                          (conjoin-clauses
                           (acl2::interp-defs-alist-clauses new)))))
           :hints(("Goal" :in-theory (enable acl2::interp-defs-alist-clauses acl2::suffixp conjoin-clauses)))))

  (defthm not-theoremp-when-obligs-extension-p
    (implies (and (bind-interp-st-extension new old)
                  (not (glcp-generic-geval-ev-theoremp
                        (conjoin-clauses
                         (acl2::interp-defs-alist-clauses (nth *is-obligs* old))))))
             (not (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::interp-defs-alist-clauses (nth *is-obligs* new)))))))

  (defthm theoremp-when-obligs-extension-p
    (implies (and (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::interp-defs-alist-clauses (nth *is-obligs* new))))
                  (interp-st-obligs-extension-p new old))
             (glcp-generic-geval-ev-theoremp
              (conjoin-clauses
               (acl2::interp-defs-alist-clauses (nth *is-obligs* old))))))

  (defthm interp-st-obligs-extension-p-of-update-non-obligs
    (implies (not (equal (nfix n) *is-obligs*))
             (and (equal (interp-st-obligs-extension-p (update-nth n v x) y)
                         (interp-st-obligs-extension-p x y))
                  (equal (interp-st-obligs-extension-p x (update-nth n v y))
                         (interp-st-obligs-extension-p x y)))))

  (defthm interp-st-obligs-extension-p-of-is-decrement-backchain-limit
    (implies (not (equal (nfix n) *is-obligs*))
             (and (equal (interp-st-obligs-extension-p (update-nth n v x) y)
                         (interp-st-obligs-extension-p x y))
                  (equal (interp-st-obligs-extension-p x (update-nth n v y))
                         (interp-st-obligs-extension-p x y))))))

(define interp-st-obligs-diff (x y)
  :non-executable t
  :verify-guards nil
  (take (- (len (nth *is-obligs* x))
           (len (nth *is-obligs* y)))
        (nth *is-obligs* x))
  ///

  (local (defthm len-when-suffixp
           (implies (acl2::suffixp x y)
                    (<= (len x) (len y)))
           :hints(("Goal" :in-theory (enable acl2::suffixp)))
           :rule-classes :linear))

  (local (in-theory (disable pseudo-termp-symbolp-car-x
                             glcp-generic-geval-ev-of-variable
                             pseudo-termp alistp
                             acl2::take-of-len-free
                             acl2::car-of-take
                             acl2::consp-of-car-when-alistp
                             acl2::consp-when-member-equal-of-atom-listp
                             acl2::consp-of-take
                             acl2::take-of-too-many
                             equal-of-booleans-rewrite)))


  (local (defthm theoremp-when-suffixp
           (implies (acl2::suffixp old new)
                    (iff (glcp-generic-geval-ev-theoremp
                          (conjoin-clauses
                           (acl2::interp-defs-alist-clauses new)))
                         (and (glcp-generic-geval-ev-theoremp
                               (conjoin-clauses
                                (acl2::interp-defs-alist-clauses old)))
                              (glcp-generic-geval-ev-theoremp
                               (conjoin-clauses
                                (acl2::interp-defs-alist-clauses
                                 (take (- (len new) (len old)) new)))))))
           :hints(("Goal" :in-theory (enable acl2::interp-defs-alist-clauses acl2::suffixp)))))

  (defthm obligs-clauses-theoremp-when-extension
    (implies (and ;; (acl2::rewriting-negative-literal
                  ;;  `(GLCP-GENERIC-GEVAL-EV
                  ;;    (CONJOIN-CLAUSES (ACL2::INTERP-DEFS-ALIST-CLAUSES (NTH '0 ,INTERP-ST)))
                  ;;    (GLCP-GENERIC-GEVAL-EV-FALSIFY
                  ;;     (CONJOIN-CLAUSES (ACL2::INTERP-DEFS-ALIST-CLAUSES (NTH '0 ,INTERP-ST))))))
                  (bind-interp-st-extension interp-st old-interp-st))
             (iff (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses (acl2::interp-defs-alist-clauses (nth *is-obligs* interp-st))))
                  (and (glcp-generic-geval-ev-theoremp
                        (conjoin-clauses (acl2::interp-defs-alist-clauses
                                          (interp-st-obligs-diff interp-st old-interp-st))))
                       (glcp-generic-geval-ev-theoremp
                        (conjoin-clauses (acl2::interp-defs-alist-clauses (nth *is-obligs* old-interp-st)))))))
    :hints(("Goal" :in-theory (enable interp-st-obligs-extension-p)))))



(encapsulate nil
  (local (acl2::use-trivial-ancestors-check))
  (local (in-theory (disable update-nth nth
                             pseudo-termp pseudo-term-listp
                             pseudo-termp-symbolp-car-x
                             alistp hons-assoc-equal
                             general-concretep-def
                             equal-of-booleans-rewrite)))
  (def-glcp-interp-thm glcp-generic-interp-produces-interp-st-obligs-extension
    :body (interp-st-obligs-extension-p interp-st1 interp-st)
    :expand-calls t))



(local (defthm glcp-generic-interp-correct-equivs-with-equal
         (b* (((mv ?val ?erp ?pathcond1 ?interp-st1 ?bvar-db1 ?state1)
               (glcp-generic-interp-term-equivs
                x alist nil pathcond clk config interp-st bvar-db st)))
           (implies (and (bfr-hyp-eval (nth *is-constraint* interp-st)
                                       (car env))
                         (glcp-generic-geval-ev-meta-extract-global-facts
                          :state state0)
                         (case-split (glcp-interp-accs-ok interp-st1 bvar-db1 config env))
                         (equal (w state0) (w st))
                         (not erp)
                         (bdd-mode-or-p-true (glcp-config->param-bfr config) (car env))
                         (bfr-hyp-eval pathcond (car env)))
                    (equal (glcp-generic-geval val env)
                           (glcp-generic-geval-ev
                            x
                            (glcp-generic-geval-alist alist env)))))
         :hints (("goal" :use ((:instance glcp-generic-interp-correct-equivs
                                (contexts nil)))))))

(local (in-theory (disable nth (force))))

(encapsulate nil
  (local (in-theory nil))
  (with-output :off (prove event)
    (verify-guards glcp-generic-interp-term
      :hints (("Goal" :by glcp-generic-interp-guards-ok
               :do-not '(preprocess simplify)
               :do-not-induct t)))))



(defthm bvar-db-vars-bounded-of-parametrize-bvar-db
  (implies (and (bvar-db-vars-bounded k t n bvar-db1)
                (<= (nfix n) (next-bvar$a bvar-db1)))
           (bvar-db-vars-bounded k pathcond-bfr n (parametrize-bvar-db pathcond-bfr bvar-db1 bvar-db)))
  :hints(("Goal" :in-theory (enable bvar-db-vars-bounded))))

(Defsection bvar-db-env-ok-normalize-cons-car-cdr-env
  (defthm-gobj-flag
    (defthm glcp-generic-geval-normalize-cons-car-cdr-env
      (equal (glcp-generic-geval x (cons (car env) (cdr env)))
             (glcp-generic-geval x env))
      :hints ('(:expand ((:free (env) (:with glcp-generic-geval (glcp-generic-geval x env))))
                :in-theory (enable default-car default-cdr)))
      :flag gobj)
    (defthm glcp-generic-geval-list-normalize-cons-car-cdr-env
      (equal (glcp-generic-geval-list x (cons (car env) (cdr env)))
             (glcp-generic-geval-list x env))
      :hints ('(:expand ((:free (env) (glcp-generic-geval-list x env)))))
      :flag list))

  (defthm glcp-generic-geval-alist-normalize-cons-car-cdr-env
    (equal (glcp-generic-geval-alist x (cons (car env) (cdr env)))
           (glcp-generic-geval-alist x env))
    :hints(("Goal" :in-theory (enable glcp-generic-geval-alist))))

  (in-theory (disable glcp-generic-geval-list-normalize-cons-car-cdr-env
                      glcp-generic-geval-normalize-cons-car-cdr-env))

  (defthm glcp-generic-bvar-db-env-ok-normalize-cons-car-cdr-env
    (equal (glcp-generic-bvar-db-env-ok bvar-db p bound (cons (car env) (cdr env)))
           (glcp-generic-bvar-db-env-ok bvar-db p bound env))
    :hints (("goal" :cases ((glcp-generic-bvar-db-env-ok bvar-db p bound (cons (car env) (cdr env)))))
            (and stable-under-simplificationp
                 (b* ((expand-lit (assoc 'glcp-generic-bvar-db-env-ok clause))
                      (expand-env (nth 4 expand-lit))
                      (other-env (if (eq expand-env 'env) '(cons (car env) (cdr env)) 'env)))
                   `(:expand (,expand-lit)
                     :use ((:instance glcp-generic-bvar-db-env-ok-necc
                            (n (glcp-generic-bvar-db-env-ok-witness . ,(cdr expand-lit)))
                            (env ,other-env)))
                     :in-theory (e/d (glcp-generic-geval-normalize-cons-car-cdr-env default-car)
                                     (glcp-generic-bvar-db-env-ok-necc))))))))

(defsection bvar-db-stuff
  ;; (defthm fal-extract-of-glcp-generic-geval-alist
  ;;   (equal (acl2::fal-extract vars (glcp-generic-geval-alist alist env))
  ;;          (glcp-generic-geval-alist (acl2::fal-extract vars alist) env))
  ;;   :hints(("Goal" :in-theory (enable acl2::fal-extract glcp-generic-geval-alist))))

  (local (in-theory (disable gobj-alist-to-param-space
                             gobj-to-param-space)))

  (defthm bvar-db-fix-env-of-nfix-min
    (equal (bvar-db-fix-env max (nfix min) bvar-db p bfr-env var-env)
           (bvar-db-fix-env max min bvar-db p bfr-env var-env))
    :hints(("Goal" :in-theory (enable bvar-db-fix-env))))

  (defthm bvar-db-fix-env-of-nfix-max
    (equal (bvar-db-fix-env (nfix max) min bvar-db p bfr-env var-env)
           (bvar-db-fix-env max min bvar-db p bfr-env var-env))
    :hints(("Goal" :in-theory (enable bvar-db-fix-env))))


  (defsection vars-bounded-in-aig-mode
    (defthm pbfr-depends-on-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (pbfr-depends-on k p x)
                    (pbfr-depends-on k t x)))
      :hints(("Goal" :in-theory (enable bfr-from-param-space pbfr-depends-on))))

    (defthm pbfr-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (pbfr-vars-bounded k p x)
                    (pbfr-vars-bounded k t x)))
      :hints((and stable-under-simplificationp
                  (b* ((lit (assoc 'pbfr-vars-bounded clause)))
                    `(:expand (,lit)
                      :use ((:instance pbfr-vars-bounded-necc
                             (m ,(cons 'pbfr-vars-bounded-witness (cdr lit)))
                             (n k))
                            (:instance pbfr-vars-bounded-necc
                             (m ,(cons 'pbfr-vars-bounded-witness (cdr lit)))
                             (n k) (p t)))
                      :in-theory (disable pbfr-vars-bounded-necc))))))

    (defthm pbfr-list-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (pbfr-list-vars-bounded k p x)
                    (pbfr-list-vars-bounded k t x)))
      :hints(("Goal" :in-theory (enable pbfr-list-vars-bounded))))

    (defthm-gobj-flag
      (defthm gobj-vars-bounded-in-aig-mode
        (implies (and (syntaxp (not (equal p ''t)))
                      (bfr-mode))
                 (iff (gobj-vars-bounded k p x)
                      (gobj-vars-bounded k t x)))
        :hints ('(:expand ((:free (p) (gobj-vars-bounded k p x)))))
        :flag gobj)
      (defthm gobj-list-vars-bounded-in-aig-mode
        (implies (and (syntaxp (not (equal p ''t)))
                      (bfr-mode))
                 (iff (gobj-list-vars-bounded k p x)
                      (gobj-list-vars-bounded k t x)))
        :hints ('(:expand ((:free (p) (gobj-list-vars-bounded k p x)))))
        :flag list))

    (defthm gobj-alist-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (gobj-alist-vars-bounded k p x)
                    (gobj-alist-vars-bounded k t x)))
      :hints(("Goal" :in-theory (enable gobj-alist-vars-bounded))))

    (defthm bvar-db-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (bvar-db-vars-bounded k p n x)
                    (bvar-db-vars-bounded k t n x)))
      :hints(("Goal" :in-theory (enable bvar-db-vars-bounded))))

    (defthm glcp-generic-geval-of-set-var-when-gobj-vars-bounded-aig-mode
      (implies (and (gobj-vars-bounded m p x)
                    (b* ((k (bfr-varname-fix k)))
                      (or (not (natp k))
                          (<= (nfix m) k)))
                    (bfr-mode))
               (equal (glcp-generic-geval x (cons (bfr-set-var k v env) var-env))
                      (glcp-generic-geval x (cons env var-env))))
      :hints (("goal" :use ((:instance GLCP-GENERIC-GEVAL-OF-SET-VAR-WHEN-GOBJ-VARS-BOUNDED
                             (p t)))
               :in-theory (enable bfr-param-env))))
    
    (defthm gobj-alist-list-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (gobj-alist-list-vars-bounded k p x)
                    (gobj-alist-list-vars-bounded k t x)))
      :hints(("Goal" :in-theory (enable gobj-alist-list-vars-bounded))))

    (defthm gbc-sigtable-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (gbc-sigtable-vars-bounded k p x)
                    (gbc-sigtable-vars-bounded k t x)))
      :hints(("Goal" :in-theory (enable gbc-sigtable-vars-bounded))))

    (defthm gbc-tuples-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (gbc-tuples-vars-bounded k p x)
                    (gbc-tuples-vars-bounded k t x)))
      :hints(("Goal" :in-theory (enable gbc-tuples-vars-bounded))))

    (defthm gbc-db-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (gbc-db-vars-bounded k p x)
                    (gbc-db-vars-bounded k t x)))
      :hints(("Goal" :in-theory (enable gbc-db-vars-bounded))))

    (defthm bfr-constr-depends-on-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (bfr-constr-depends-on k p x)
                    (bfr-constr-depends-on k t x)))
      :hints(("Goal" :in-theory (enable bfr-from-param-space bfr-constr-depends-on))))

    (defthm bfr-constr-vars-bounded-in-aig-mode
      (implies (and (syntaxp (not (equal p ''t)))
                    (bfr-mode))
               (iff (bfr-constr-vars-bounded k p x)
                    (bfr-constr-vars-bounded k t x)))
      :hints((and stable-under-simplificationp
                  (b* ((lit (assoc 'bfr-constr-vars-bounded clause)))
                    `(:expand (,lit)
                      :use ((:instance bfr-constr-vars-bounded-necc
                             (m ,(cons 'bfr-constr-vars-bounded-witness (cdr lit)))
                             (n k))
                            (:instance bfr-constr-vars-bounded-necc
                             (m ,(cons 'bfr-constr-vars-bounded-witness (cdr lit)))
                             (n k) (p t)))
                      :in-theory (disable bfr-constr-vars-bounded-necc)))))))
      

  (defthm bvar-db-orderedp-aig-mode-normalize-param
    (implies (and (syntaxp (not (equal p ''t)))
                  (bfr-mode))
             (iff (bvar-db-orderedp p bvar-db)
                  (bvar-db-orderedp t bvar-db)))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'bvar-db-orderedp clause)))
                   `(:expand (,lit)
                     :use ((:instance bvar-db-orderedp-necc
                            (n ,(cons 'bvar-db-orderedp-witness (cdr lit))))
                           (:instance bvar-db-orderedp-necc
                            (n ,(cons 'bvar-db-orderedp-witness (cdr lit)))
                            (p t)))
                     :in-theory (disable bvar-db-orderedp-necc))))))

  (local (defthm bvar-db-orderedp-necc-aig-mode
           (implies (and (bvar-db-orderedp t bvar-db)
                         (bfr-mode)
                         (<= (base-bvar$a bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$a bvar-db))
                         (<= (nfix n) (nfix m)))
                    (gobj-vars-bounded m q (get-bvar->term$a n bvar-db)))
           :hints (("goal" :use ((:instance bvar-db-orderedp-necc
                                  (n (nfix n))))
                    :in-theory (disable bvar-db-orderedp-necc)))))

  (local (defthm bvar-db-fix-env-normalize-param-aig-mode
           (implies (and (syntaxp (not (equal p ''t)))
                         (bfr-mode))
                    (equal (bvar-db-fix-env n min bvar-db p bfr-env var-env)
                           (bvar-db-fix-env n min bvar-db t bfr-env var-env)))
           :hints(("Goal" :in-theory (enable bvar-db-fix-env bfr-unparam-env bfr-param-env)))))
  

  

  (defsection bvar-db-env-fix-lookup-is-geval-when-ordered

    (local (defthm bvar-db-fix-env-eval-gobj-vars-bounded-remove
             (implies (and ; (bvar-db-orderedp p bvar-db)
                       (bfr-mode)
                       ;; (bfr-vars-bounded min p)
                       (gobj-vars-bounded m t gobj)
                       (<= (nfix m) (nfix min))
                       (<= (nfix n) (next-bvar$a bvar-db)))
                      (let* ((env-n (bvar-db-fix-env n min bvar-db p env
                                                     var-env)))
                        (equal (glcp-generic-geval gobj (cons env-n var-env))
                               (glcp-generic-geval gobj (cons env var-env)))))
             :hints (("goal" :induct (bvar-db-fix-env n min bvar-db p env var-env)
                      :in-theory (enable bfr-unparam-env bfr-param-env)))))

    (defthm bvar-db-bvar-term-eval-remove-bvar-db-fix-env
      (implies (and (bvar-db-orderedp t bvar-db)
                    (bfr-mode)
                    (<= (base-bvar$a bvar-db) (nfix k))
                    (< (nfix k) (next-bvar$a bvar-db))
                    (<= (nfix k) (nfix min))
                    (<= (nfix n) (next-bvar$a bvar-db)))
               (let* ((env-n (bvar-db-fix-env n min bvar-db p env
                                              var-env)))
                 (equal (glcp-generic-geval (get-bvar->term$a k bvar-db) (cons env-n var-env))
                        (glcp-generic-geval (get-bvar->term$a k bvar-db) (cons env var-env)))))
      :hints (("goal" :use ((:instance bvar-db-fix-env-eval-gobj-vars-bounded-remove
                             (m k) (gobj (get-bvar->term$a k bvar-db))))
               :in-theory (disable bvar-db-fix-env-eval-gobj-vars-bounded-remove)
               :do-not-induct t)))

    (defthm bvar-db-bvar-term-eval-remove-bvar-db-fix-env-extension
      (implies (and (bvar-db-orderedp t bvar-db)
                    (bvar-db-extension-p bvar-db old-bvar-db)
                    (bfr-mode)
                    (<= (base-bvar$a bvar-db) (nfix k))
                    (< (nfix k) (next-bvar$a old-bvar-db))
                    (<= (nfix k) (nfix min))
                    (<= (nfix n) (next-bvar$a bvar-db)))
               (let* ((env-n (bvar-db-fix-env n min bvar-db p env
                                              var-env)))
                 (equal (glcp-generic-geval (get-bvar->term$a k old-bvar-db) (cons env-n var-env))
                        (glcp-generic-geval (get-bvar->term$a k old-bvar-db) (cons env var-env)))))
      :hints (("goal" :use ((:instance bvar-db-bvar-term-eval-remove-bvar-db-fix-env))
               :in-theory (disable bvar-db-bvar-term-eval-remove-bvar-db-fix-env)
               :do-not-induct t)))
    
    (local (defthmd bvar-db-fix-env-eval-gobj-vars-bounded-lemma-aig-mode
             (implies (and ; (bvar-db-orderedp p bvar-db)
                       (bfr-mode)
                       ;; (bfr-vars-bounded min p)
                       (gobj-vars-bounded m t gobj)
                       (< (nfix m) (nfix n))
                       (<= (nfix n) (next-bvar$a bvar-db)))
                      (let* ((env-n (bvar-db-fix-env n min bvar-db p env
                                                     var-env))
                             (env-m (bvar-db-fix-env m min bvar-db p env
                                                     var-env)))
                        (equal (glcp-generic-geval gobj (cons env-n var-env))
                               (glcp-generic-geval gobj (cons env-m var-env)))))
             :hints (("goal" :induct (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                                      var-env)
                      :in-theory (enable bfr-unparam-env bfr-param-env)))))

    (local (defthmd bvar-db-fix-env-eval-gobj-vars-bounded-aig-mode
             (implies (and ; (bvar-db-orderedp p bvar-db)
                       (bfr-mode)
                       ;; (bfr-vars-bounded min p)
                       (gobj-vars-bounded min t gobj)
                       (<= (nfix n) (next-bvar$a bvar-db)))
                      (let* ((env-n (bvar-db-fix-env n min bvar-db p env
                                                     var-env)))
                        (equal (glcp-generic-geval gobj (cons env-n var-env))
                               (glcp-generic-geval gobj (cons env var-env)))))
             :hints (("goal" :induct (bvar-db-fix-env n min bvar-db p (bfr-param-env p env)
                                                      var-env)
                      :in-theory (enable bfr-unparam-env bfr-param-env)))))

    (defthm glcp-generic-geval-alist-of-bvar-db-fix-env-vars-bounded-aig-mode
      (implies (and ; (bvar-db-orderedp p bvar-db)
                (bfr-mode)
                ;; (bfr-vars-bounded min p)
                (gobj-alist-vars-bounded min t al)
                (<= (nfix n) (next-bvar$a bvar-db)))
               (let* ((env-n (bvar-db-fix-env n min bvar-db p env
                                              var-env)))
                 (equal (glcp-generic-geval-alist al (cons env-n var-env))
                        (glcp-generic-geval-alist al (cons env var-env)))))
      :hints(("Goal" :in-theory (e/d (glcp-generic-geval-alist)
                                     (bvar-db-fix-env)))))


    (local (defthm bfr-lookup-in-bvar-db-fix-env-lemma
             (implies (bfr-mode)
                      (equal (bfr-lookup k (bvar-db-fix-env max min bvar-db p bfr-env var-env))
                             (let ((k (bfr-varname-fix k)))
                               (if (and (natp k)
                                        (< k (nfix max))
                                        (<= (nfix min) k)
                                        (<= (base-bvar$a bvar-db) k))
                                   (bool-fix
                                    (glcp-generic-geval
                                     (get-bvar->term$a k bvar-db)
                                     (cons (bvar-db-fix-env k min bvar-db p bfr-env var-env) var-env)))
                                 (bfr-lookup k bfr-env)))))
             :hints(("Goal" :in-theory (enable bfr-unparam-env bfr-param-env)
                     :induct (bvar-db-fix-env max min bvar-db p bfr-env var-env)))))

    (local (defthm bfr-varname-fix-when-natp-bfr-varname-fix
             (implies (natp (bfr-varname-fix x))
                      (equal (nfix x) (bfr-varname-fix x)))
             :hints(("Goal" :in-theory (enable bfr-varname-fix aig-var-fix)))))

    (local (in-theory (disable ACL2::INEQUALITY-WITH-NFIX-HYP-1
                               acl2::natp-when-gte-0)))
    
    (defthm bfr-lookup-in-bvar-db-fix-env
      (implies (and (bfr-mode)
                    (bvar-db-orderedp t bvar-db)
                    (<= (nfix max) (next-bvar$a bvar-db)))
               (equal (bfr-lookup k (bvar-db-fix-env max min bvar-db p bfr-env var-env))
                      (let ((k (bfr-varname-fix k)))
                        (if (and (natp k)
                                 (< k (nfix max))
                                 (<= (nfix min) k)
                                 (<= (base-bvar$a bvar-db) k))
                            (bool-fix
                             (glcp-generic-geval
                              (get-bvar->term$a k bvar-db)
                              (cons (bvar-db-fix-env max min bvar-db p bfr-env var-env) var-env)))
                          (bfr-lookup k bfr-env)))))
      :hints (("goal" :use ((:instance bfr-lookup-in-bvar-db-fix-env-lemma)
                            (:instance bvar-db-fix-env-eval-gobj-vars-bounded-lemma-aig-mode
                             (m (bfr-varname-fix k)) (n max) (env bfr-env) (gobj (get-bvar->term$a k bvar-db)))
                            (:instance bvar-db-orderedp-necc (n (bfr-varname-fix k))))
               :in-theory (disable bfr-lookup-in-bvar-db-fix-env-lemma
                                   bvar-db-orderedp-necc
                                   bvar-db-fix-env-eval-gobj-vars-bounded-lemma-aig-mode)
               :do-not-induct t)))

    (defthm bfr-lookup-in-bvar-db-fix-env-out-of-range
      (implies (and (bfr-mode)
                    (not (and (natp (bfr-varname-fix k))
                              (< (bfr-varname-fix k) (nfix max))
                              (<= (nfix min) (bfr-varname-fix k)))))
               (equal (bfr-lookup k (bvar-db-fix-env max min bvar-db p bfr-env var-env))
                      (bfr-lookup k bfr-env)))
      :hints(("Goal" :in-theory (enable bfr-unparam-env bfr-param-env bvar-db-fix-env)
              :induct (bvar-db-fix-env max min bvar-db p bfr-env var-env))))

    (defthm bfr-lookup-in-bvar-db-fix-env-unparam
      (implies (and (bfr-mode)
                    (bvar-db-orderedp t bvar-db)
                    (<= (nfix max) (next-bvar$a bvar-db)))
               (equal (bfr-lookup k (bfr-unparam-env q (bvar-db-fix-env max min bvar-db p bfr-env var-env)))
                      (let ((k (bfr-varname-fix k)))
                        (if (and (natp k)
                                 (< k (nfix max))
                                 (<= (nfix min) k)
                                 (<= (base-bvar$a bvar-db) k))
                            (bool-fix
                             (glcp-generic-geval
                              (get-bvar->term$a k bvar-db)
                              (cons (bvar-db-fix-env max min bvar-db p bfr-env var-env) var-env)))
                          (bfr-lookup k bfr-env)))))
      :hints (("goal" :in-theory (enable bfr-unparam-env)))))


  (defthm bvar-db-env-ok-normalize-param
    (implies (and (syntaxp (not (equal p ''t)))
                  (bfr-mode))
             (iff (glcp-generic-bvar-db-env-ok
                   bvar-db p bound env)
                  (glcp-generic-bvar-db-env-ok
                   bvar-db t bound env)))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'glcp-generic-bvar-db-env-ok clause)))
                   `(:expand (,lit)
                     :use ((:instance glcp-generic-bvar-db-env-ok-necc
                            (n ,(cons 'glcp-generic-bvar-db-env-ok-witness (cdr lit)))
                            (p t))
                           (:instance glcp-generic-bvar-db-env-ok-necc
                            (n ,(cons 'glcp-generic-bvar-db-env-ok-witness (cdr lit)))))
                     :in-theory (e/d (bfr-unparam-env) (glcp-generic-bvar-db-env-ok-necc)))))))

  (defthm bvar-db-env-fix-of-extension
    (implies (and (bvar-db-extension-p bvar-db old-bvar-db)
                  (bvar-db-orderedp t bvar-db)
                  (glcp-generic-bvar-db-env-ok old-bvar-db t (next-bvar$a old-bvar-db) (cons bfr-env var-env))
                  (bfr-mode))
             (glcp-generic-bvar-db-env-ok
              bvar-db p (next-bvar$a bvar-db)
              (cons (bvar-db-fix-env (next-bvar$a bvar-db)
                                     (next-bvar$a old-bvar-db)
                                     bvar-db q bfr-env var-env)
                    var-env)))
    :hints (("goal" :expand ((glcp-generic-bvar-db-env-ok
                              bvar-db p (next-bvar$a bvar-db)
                              (cons (bvar-db-fix-env (next-bvar$a bvar-db)
                                                     (next-bvar$a old-bvar-db)
                                                     bvar-db p bfr-env var-env)
                                    var-env)))
             :use ((:instance glcp-generic-bvar-db-env-ok-necc
                    (n (glcp-generic-bvar-db-env-ok-witness
                        bvar-db p (next-bvar$a bvar-db)
                        (cons (bvar-db-fix-env (next-bvar$a bvar-db)
                                               (next-bvar$a old-bvar-db)
                                               bvar-db p bfr-env var-env)
                              var-env)))
                    (bvar-db old-bvar-db) (bound (next-bvar$a old-bvar-db))
                    (env (cons bfr-env var-env)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable bfr-unparam-env)))))

  (defthm bvar-db-orderedp-of-extension
    (implies (and (bvar-db-orderedp p bvar-db)
                  (bvar-db-extension-p bvar-db old-bvar-db))
             (bvar-db-orderedp p old-bvar-db))
    :hints (("goal" :expand ((bvar-db-orderedp p old-bvar-db))
             :use ((:instance bvar-db-orderedp-necc
                    (n (bvar-db-orderedp-witness p old-bvar-db)))
                   (:instance bvar-db-extension-increases
                    (new bvar-db) (old old-bvar-db)))
             :in-theory (disable bvar-db-orderedp-necc
                                 bvar-db-extension-increases))))

  (defthm bvar-db-env-fix-of-extension2
    (implies (and (bind-bvar-db-extension bvar-db old-bvar-db)
                  (bvar-db-orderedp t bvar-db)
                  (<= (nfix min) (next-bvar$a old-bvar-db))
                  (glcp-generic-bvar-db-env-ok old-bvar-db t (next-bvar$a old-bvar-db)
                                               (cons (bvar-db-fix-env
                                                      (next-bvar$a old-bvar-db)
                                                      min old-bvar-db t bfr-env var-env)
                                                     var-env))
                  (bfr-mode))
             (glcp-generic-bvar-db-env-ok
              bvar-db p (next-bvar$a bvar-db)
              (cons (bvar-db-fix-env (next-bvar$a bvar-db) min bvar-db q bfr-env var-env)
                    var-env)))
    :hints (("goal" :expand ((glcp-generic-bvar-db-env-ok
                              bvar-db t (next-bvar$a bvar-db)
                              (cons (bvar-db-fix-env (next-bvar$a bvar-db) min bvar-db t bfr-env var-env)
                                    var-env)))
             :use ((:instance glcp-generic-bvar-db-env-ok-necc
                    (n (glcp-generic-bvar-db-env-ok-witness
                        bvar-db t (next-bvar$a bvar-db)
                        (cons (bvar-db-fix-env (next-bvar$a bvar-db) min bvar-db t bfr-env var-env)
                                    var-env)))
                    (bvar-db old-bvar-db) (bound (next-bvar$a old-bvar-db))
                    (env (cons (bvar-db-fix-env
                                (next-bvar$a old-bvar-db)
                                min old-bvar-db t bfr-env var-env)
                               var-env)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable bfr-unparam-env)))))

  (local (defthm glcp-generic-geval-bvar-db-term-of-set-bvar-out-of-bounds
           (implies (and (bvar-db-orderedp t bvar-db)
                         (<= (base-bvar$a bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$a bvar-db))
                         (not (and (natp (bfr-varname-fix k))
                                   (< (bfr-varname-fix k) (nfix n))))
                         (bfr-mode))
                    (equal (glcp-generic-geval (get-bvar->term$a n bvar-db)
                                               (cons (bfr-set-var k v bfr-env) var-env))
                           (glcp-generic-geval (get-bvar->term$a n bvar-db) (cons bfr-env var-env))))
           :hints (("goal" :use ((:instance bvar-db-orderedp-necc
                                  (p t) (n (nfix n))))
                    :in-theory (disable bvar-db-orderedp-necc
                                        BVAR-DB-ORDEREDP-NECC-AIG-MODE
                                        GOBJ-VARS-BOUNDED-OF-GET-BVAR->TERM-WHEN-BVAR-DB-ORDEREDP)))))

  (local (defthm bvar-db-env-ok-of-set-bvar-out-of-bounds
           (implies (and (glcp-generic-bvar-db-env-ok bvar-db t bound (cons bfr-env var-env))
                         (bvar-db-orderedp t bvar-db)
                         (bfr-mode)
                         (not (and (natp (bfr-varname-fix k))
                                   (< (bfr-varname-fix k) bound))))
                    (glcp-generic-bvar-db-env-ok bvar-db t bound
                                                 (cons (bfr-set-var k val bfr-env)
                                                       var-env)))
           :hints(("Goal" :in-theory (enable bvar-db-fix-env bfr-param-env bfr-unparam-env))
                  (and stable-under-simplificationp
                       (b* ((lit (car (last clause))))
                         `(:expand (,lit)
                           :use ((:instance glcp-generic-bvar-db-env-ok-necc
                                  (n ,(cons 'glcp-generic-bvar-db-env-ok-witness (cdr lit)))
                                  (p t) (env (cons bfr-env var-env))))))))))
                                  


  (defthm bvar-db-env-ok-of-fix-env-disjoint
    (implies (and (glcp-generic-bvar-db-env-ok bvar-db t bound (cons bfr-env var-env))
                  (bfr-mode)
                  (bvar-db-orderedp t bvar-db)
                  (natp bound))
             (glcp-generic-bvar-db-env-ok bvar-db t bound
                                          (cons (bvar-db-fix-env max bound other-bvar-db t bfr-env var-env)
                                                var-env)))
    :hints(("Goal" :in-theory (enable bvar-db-fix-env bfr-param-env bfr-unparam-env))))

  (defthm bvar-db-env-ok-of-extension-over-bound
    (implies (and (bind-bvar-db-extension bvar-db old-bvar-db)
                  (<= bound (next-bvar$a old-bvar-db))
                  (glcp-generic-bvar-db-env-ok old-bvar-db t bound env))
             (glcp-generic-bvar-db-env-ok bvar-db t bound env))
    :hints (("goal" :expand ((glcp-generic-bvar-db-env-ok bvar-db t bound env))
             :use ((:instance glcp-generic-bvar-db-env-ok-necc
                    (n (glcp-generic-bvar-db-env-ok-witness bvar-db t bound env))
                    (p t) (bvar-db old-bvar-db))))))

)

(defsection glcp-parametrize-interp-state
  (local (in-theory (enable glcp-parametrize-interp-state)))
  (local (std::set-define-current-function glcp-parametrize-interp-state))

;; (define glcp-parametrize-interp-state (pathcond-bfr
;;                                        interp-st)
;;   :returns (mv contra new-interp-st)
;;   (b* (((mv contra constraint &)
;;         (bfr-constr-assume
;;          (bfr-to-param-space pathcond-bfr
;;                              (bfr-constr->bfr (is-constraint interp-st)))
;;          (bfr-constr-init)))

;;        (interp-st (update-is-constraint constraint interp-st))
;;        (constraint-db (parametrize-constraint-db pathcond-bfr (is-constraint-db interp-st)))
;;        (interp-st (update-is-constraint-db constraint-db interp-st)))
;;     (mv contra interp-st))
;;   ///
  (std::defret glcp-parametrize-interp-state-contra-correct-under-pathcond-bfr
    (implies (and (acl2::rewriting-negative-literal
                   `(mv-nth '0 (glcp-parametrize-interp-state ,pathcond-bfr ,interp-st)))
                  (bfr-eval pathcond-bfr env))
             (iff contra
                  (and (not (bfr-hyp-eval (is-constraint interp-st) env))
                       (hide contra))))
    :hints (("goal" :expand ((:free (x) (hide x))))
            (and stable-under-simplificationp
                 '(:expand ((bfr-equiv pathcond-bfr nil))
                   :in-theory (disable bfr-constr-assume-correct)
                   :use ((:instance bfr-constr-assume-correct
                          (x (bfr-to-param-space pathcond-bfr
                                                 (bfr-constr->bfr (is-constraint interp-st))))
                          (hyp (bfr-constr-init))
                          (env (bfr-param-env pathcond-bfr env))))))))

  (std::defret glcp-parametrize-interp-state-contra-correct-under-constraint
    (implies (and (acl2::rewriting-negative-literal
                   `(mv-nth '0 (glcp-parametrize-interp-state ,pathcond-bfr ,interp-st)))
                  (bfr-hyp-eval (nth *is-constraint* interp-st) env))
             (iff contra
                  (and (not (bfr-eval pathcond-bfr env))
                       (hide contra))))
    :hints (("goal" :expand ((:free (x) (hide x))))
            (and stable-under-simplificationp
                 '(:expand ((bfr-equiv pathcond-bfr nil))
                   :in-theory (disable bfr-constr-assume-correct)
                   :use ((:instance bfr-constr-assume-correct
                          (x (bfr-to-param-space pathcond-bfr
                                                 (bfr-constr->bfr (is-constraint interp-st))))
                          (hyp (bfr-constr-init))
                          (env (bfr-param-env pathcond-bfr env))))))))

  (std::defret glcp-parametrize-interp-state-new-constraint
    (implies (and (not contra)
                  (bfr-eval pathcond-bfr env)
                  (bfr-mode))
             (equal (bfr-hyp-eval (nth *is-constraint* new-interp-st) env)
                    (bfr-hyp-eval (nth *is-constraint* interp-st) env)))
    :hints(("Goal" :in-theory (enable bfr-unparam-env))))

  (std::defret glcp-parametrize-interp-state-new-constraint-false
    (implies (and (acl2::rewriting-positive-literal
                   `(bfr-hyp-eval (nth '1 (mv-nth '1 (glcp-parametrize-interp-state ,pathcond-bfr ,interp-st)))
                                  ,env))
                  (bfr-eval pathcond-bfr env)
                  (bfr-mode))
             (equal (bfr-hyp-eval (nth *is-constraint* new-interp-st) env)
                    (or (bfr-hyp-eval (nth *is-constraint* interp-st) env)
                        (hide (bfr-hyp-eval (nth *is-constraint* new-interp-st) env)))))
    :hints (("Goal" :Expand ((:free (x) (hide x)))
             :in-theory (disable bfr-constr-assume-false))
            (and stable-under-simplificationp
                 '(:expand nil :in-theory (enable bfr-unparam-env)))))

  (std::defret gbc-db-vars-bounded-of-glcp-parametrize-interp-st
    (implies (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
             (gbc-db-vars-bounded k pathcond-bfr (nth *is-constraint-db* new-interp-st))))

  (std::defret glcp-parametrize-interp-st-preserves-obligs
    (equal (nth *is-obligs* new-interp-st)
           (nth *is-obligs* interp-st)))

  (std::defret glcp-parametrize-interp-st-preserves-add-bvars-allowed
    (equal (nth *is-add-bvars-allowed* new-interp-st)
           (nth *is-add-bvars-allowed* interp-st)))

  (std::defret bfr-constr-vars-bounded-of-glcp-parametrize-interp-st
    (implies (bfr-constr-vars-bounded k t (nth *is-constraint* interp-st))
             (bfr-constr-vars-bounded k pathcond-bfr (nth *is-constraint* new-interp-st))))

  (defthm interp-st-obligs-extension-p-of-glcp-parametrize-interp-st
    (and (equal (interp-st-obligs-extension-p x (mv-nth 1 (glcp-parametrize-interp-state pathcond y)))
                (interp-st-obligs-extension-p x y))
         (equal (interp-st-obligs-extension-p (mv-nth 1 (glcp-parametrize-interp-state pathcond y)) x)
                (interp-st-obligs-extension-p y x)))
    :hints(("Goal" :in-theory (disable nth update-nth))))

  (defthm glcp-interp-accs-ok-normalize-config
    (implies (and (syntaxp (not (equal config ''nil)))
                  (bfr-mode))
             (equal (glcp-interp-accs-ok interp-st bvar-db config env)
                    (glcp-interp-accs-ok interp-st bvar-db 'nil env)))
    :hints(("Goal" :in-theory (enable glcp-interp-accs-ok)))))





(defsection glcp-parametrize-accs
  (local (in-theory (enable glcp-parametrize-accs)))
  (local (std::set-define-current-function glcp-parametrize-accs))
                                              
;; (define glcp-parametrize-accs (pathcond-bfr interp-st bvar-db1 bvar-db)
;;   :returns (mv contra new-interp-st new-bvar-db)
;;   (b* ((bvar-db (init-bvar-db (base-bvar bvar-db1) bvar-db))
;;        (bvar-db (parametrize-bvar-db pathcond-bfr bvar-db1 bvar-db))
;;        ((mv contra1 interp-st)
;;         (glcp-parametrize-interp-state pathcond-bfr interp-st)))
;;     (mv contra1 interp-st bvar-db))
;;   ///
  (defthm normalize-glcp-parametrize-accs
    (implies (syntaxp (not (equal bvar-db ''nil)))
             (equal (glcp-parametrize-accs pathcond-bfr interp-st bvar-db1 bvar-db)
                    (glcp-parametrize-accs pathcond-bfr interp-st bvar-db1 nil))))

  (std::defret next-bvar-of-glcp-parametrize-accs
    (equal (next-bvar$a new-bvar-db)
           (next-bvar$a bvar-db1)))

  (std::defret base-bvar-of-glcp-parametrize-accs
    (equal (base-bvar$a new-bvar-db)
           (base-bvar$a bvar-db1)))

  (std::defret get-bvar->term-of-glcp-parametrize-accs
    (implies (and (<= (base-bvar$a bvar-db1) (nfix n))
                  (< (nfix n) (next-bvar$a bvar-db1)))
             (equal (get-bvar->term$a n new-bvar-db)
                    (gobj-to-param-space
                     (get-bvar->term$a n bvar-db1) pathcond-bfr))))

  (std::defret bvar-db-orderedp-of-glcp-parametrize-accs
    (implies (bvar-db-orderedp t bvar-db1)
             (bvar-db-orderedp pathcond-bfr new-bvar-db)))

  (std::defret bvar-db-orderedp-of-glcp-parametrize-accs-aig-mode
    (implies (And (bvar-db-orderedp t bvar-db1)
                  (bfr-mode))
             (bvar-db-orderedp t new-bvar-db))
    :hints (("goal" :use bvar-db-orderedp-of-glcp-parametrize-accs
             :in-theory (disable bvar-db-orderedp-of-glcp-parametrize-accs
                                 glcp-parametrize-accs))))


  (std::defret glcp-generic-bvar-db-env-ok-of-glcp-parametrize-accs
    (implies (and (bfr-eval pathcond-bfr (car env))
                  (bfr-mode))
             (equal (glcp-generic-bvar-db-env-ok
                     new-bvar-db t bound env)
                    (glcp-generic-bvar-db-env-ok
                     bvar-db1 t bound env)))
    :hints(("Goal" :in-theory (e/d (bfr-unparam-env
                                      glcp-generic-bvar-db-env-ok-normalize-cons-car-cdr-env)
                                   (glcp-generic-bvar-db-env-ok-of-parametrize-bvar-db))
            :use ((:instance glcp-generic-bvar-db-env-ok-of-parametrize-bvar-db
                   (p pathcond-bfr) (bvar-db1 bvar-db) (bvar-db bvar-db1))))))

  (std::defret glcp-parametrize-accs-contra-correct-under-pathcond-bfr
    (implies (and (acl2::rewriting-negative-literal
                   `(mv-nth '0 (glcp-parametrize-accs ,pathcond-bfr ,interp-st ,bvar-db1 ,bvar-db)))
                  (bfr-eval pathcond-bfr env))
             (iff contra
                  (and (not (bfr-hyp-eval (is-constraint interp-st) env))
                       (hide contra))))
    :hints (("goal" :expand ((:free (x) (hide x))))
            (and stable-under-simplificationp
                 '(:expand ((bfr-equiv pathcond-bfr nil))
                   :in-theory (disable bfr-constr-assume-correct)
                   :use ((:instance bfr-constr-assume-correct
                          (x (bfr-to-param-space pathcond-bfr
                                                 (bfr-constr->bfr (is-constraint interp-st))))
                          (hyp (bfr-constr-init))
                          (env (bfr-param-env pathcond-bfr env))))))))

  (std::defret glcp-parametrize-accs-contra-correct-under-constraint
    (implies (and (acl2::rewriting-negative-literal
                   `(mv-nth '0 (glcp-parametrize-accs ,pathcond-bfr ,interp-st ,bvar-db1 ,bvar-db)))
                  (bfr-hyp-eval (nth *is-constraint* interp-st) env))
             (iff contra
                  (and (not (bfr-eval pathcond-bfr env))
                       (hide contra))))
    :hints (("goal" :expand ((:free (x) (hide x))))
            (and stable-under-simplificationp
                 '(:expand ((bfr-equiv pathcond-bfr nil))
                   :in-theory (disable bfr-constr-assume-correct)
                   :use ((:instance bfr-constr-assume-correct
                          (x (bfr-to-param-space pathcond-bfr
                                                 (bfr-constr->bfr (is-constraint interp-st))))
                          (hyp (bfr-constr-init))
                          (env (bfr-param-env pathcond-bfr env))))))))

  (std::defret glcp-parametrize-accs-new-constraint
    (implies (and (not contra)
                  (bfr-eval pathcond-bfr env)
                  (bfr-mode))
             (equal (bfr-hyp-eval (nth *is-constraint* new-interp-st) env)
                    (bfr-hyp-eval (nth *is-constraint* interp-st) env))))

  (std::defret glcp-parametrize-accs-new-constraint-false
    (implies (and (acl2::rewriting-positive-literal
                   `(bfr-hyp-eval (nth '1 (mv-nth '1 (glcp-parametrize-accs ,pathcond-bfr ,interp-st ,bvar-db1 ,bvar-db)))
                                  ,env))
                  
                  (bfr-eval pathcond-bfr env)
                  (bfr-mode))
             (equal (bfr-hyp-eval (nth *is-constraint* new-interp-st) env)
                    (or (bfr-hyp-eval (nth *is-constraint* interp-st) env)
                        (hide (bfr-hyp-eval (nth *is-constraint* new-interp-st) env)))))
    :hints (("Goal" :Expand ((:free (x) (hide x))))))

  (std::defret gbc-db-vars-bounded-of-glcp-parametrize-accs
    (implies (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
             (gbc-db-vars-bounded k pathcond-bfr (nth *is-constraint-db* new-interp-st))))

  (std::defret bvar-db-vars-bounded-of-glcp-parametrize-accs
    (implies (and (bvar-db-vars-bounded k t n bvar-db1)
                  (<= (nfix n) (next-bvar$a bvar-db1)))
             (bvar-db-vars-bounded k pathcond-bfr n new-bvar-db)))

  ;; (std::defret bvar-db-vars-bounded-of-glcp-parametrize-accs-aig-mode
  ;;   (implies (and (bvar-db-vars-bounded k t n bvar-db1)
  ;;                 (<= (nfix n) (next-bvar$a bvar-db1))
  ;;                 (bfr-mode))
  ;;            (bvar-db-vars-bounded k t n new-bvar-db))
  ;;   :hints (("goal" :use bvar-db-vars-bounded-of-glcp-parametrize-accs
  ;;            :in-theory (disable glcp-parametrize-accs
  ;;                                bvar-db-vars-bounded-of-glcp-parametrize-accs))))

  (std::defret glcp-parametrize-accs-preserves-obligs
    (equal (nth *is-obligs* new-interp-st)
           (nth *is-obligs* interp-st)))

  (std::defret glcp-parametrize-accs-preserves-add-bvars-allowed
    (equal (nth *is-add-bvars-allowed* new-interp-st)
           (nth *is-add-bvars-allowed* interp-st)))

  (std::defret glcp-interp-accs-ok-of-glcp-parametrize-accs
    (implies (and (bfr-eval pathcond-bfr (car env))
                  (bfr-mode))
             (iff (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
                  (glcp-interp-accs-ok interp-st bvar-db1 config env)))
    :hints(("Goal" :in-theory (e/d (glcp-interp-accs-ok bfr-unparam-env
                                      glcp-generic-bvar-db-env-ok-normalize-cons-car-cdr-env)
                                   (glcp-parametrize-accs)))))

  ;; this probably isn't a good forward-chaining rule
  (std::defret glcp-interp-accs-ok-of-glcp-parametrize-accs-forward
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
                  (bfr-eval pathcond-bfr (car env))
                  (bfr-mode))
             (glcp-interp-accs-ok interp-st bvar-db1 config env))
    :hints(("Goal" :in-theory (disable glcp-parametrize-accs)))
    :rule-classes :forward-chaining)

  (std::defret bfr-constr-vars-bounded-of-glcp-parametrize-accs
    (implies (bfr-constr-vars-bounded k t (nth *is-constraint* interp-st))
             (bfr-constr-vars-bounded k pathcond-bfr (nth *is-constraint* new-interp-st))))

  

  (std::defret interp-st-obligs-extension-p-of-glcp-parametrize-accs
    (and (implies (interp-st-obligs-extension-p x new-interp-st)
                  (interp-st-obligs-extension-p x interp-st))
         (implies (interp-st-obligs-extension-p x interp-st)
                  (interp-st-obligs-extension-p x new-interp-st))
         (equal (interp-st-obligs-extension-p new-interp-st x)
                (interp-st-obligs-extension-p interp-st x)))))

(defsection glcp-bfr-to-pathcond
  (local (in-theory (enable glcp-bfr-to-pathcond)))
  (local (std::set-define-current-function glcp-bfr-to-pathcond))
;; (define glcp-bfr-to-pathcond (bfr pathcond)
;;   :returns (mv contra new-pathcond)
;;   (b* ((pathcond-bfr (bfr-to-param-space bfr bfr))
;;        (pathcond (bfr-hyp-init pathcond))
;;        ((mv contra pathcond ?undo) (bfr-assume pathcond-bfr pathcond)))
;;     (mv contra pathcond))
;;   ///
  (local (in-theory (disable (bfr-hyp-init$a))))
  (std::defret glcp-bfr-to-pathcond-contradiction
    (implies (acl2::rewriting-negative-literal `(mv-nth '0 (glcp-bfr-to-pathcond ,bfr ,pathcond)))
             (iff contra
                  (and (bfr-equiv bfr nil)
                       (hide contra))))
    :hints (("goal" :expand ((:free (x) (hide x))))
            (and stable-under-simplificationp
                 '(:use ((:instance bfr-assume-correct
                          (x (bfr-to-param-space bfr bfr))
                          (hyp (bfr-hyp-init pathcond))
                          (env (bfr-param-env bfr (bfr-equiv-witness bfr nil)))))
                   :expand ((bfr-equiv bfr nil))
                   :in-theory (disable bfr-assume-correct)))))

  (std::defret glcp-bfr-to-pathcond-new-pathcond
    (implies (and (not contra)
                  (bfr-mode)
                  (bfr-eval bfr env))
             (bfr-hyp-eval new-pathcond env))
    :hints(("Goal" :in-theory (enable bfr-unparam-env))))

  (std::defret glcp-bfr-to-pathcond-new-pathcond-when-eval
    (implies (and (bfr-eval bfr env)
                  (bfr-mode))
             (bfr-hyp-eval new-pathcond env))
    :hints(("Goal" :in-theory (enable bfr-unparam-env))))

  (local (defthm bfr-constr-depends-on-of-bfr-hyp-init$a
           (not (bfr-constr-depends-on k p (bfr-hyp-init$a hyp)))
           :hints(("Goal" :in-theory (enable bfr-constr-depends-on bfr-hyp-init$a
                                             constr-alist-depends-on)))))

  (defthm bfr-constr-vars-bounded-of-bfr-hyp-init$a
    (bfr-constr-vars-bounded k p (bfr-hyp-init$a hyp))
    :hints(("Goal" :in-theory (enable bfr-constr-vars-bounded))))

  (defthm bfr-constr-vars-bounded-of-bfr-hyp-fix
    (iff (bfr-constr-vars-bounded k p (bfr-hyp-fix pathcond))
         (bfr-constr-vars-bounded k p pathcond))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'bfr-constr-vars-bounded clause))
                      (other (if (eq (fourth lit) 'pathcond)
                                 '(bfr-hyp-fix pathcond)
                               'pathcond)))
                   `(:expand (,lit)
                     :use ((:instance bfr-constr-vars-bounded-necc
                            (n k) (x ,other)
                            (m ,(cons 'bfr-constr-vars-bounded-witness (cdr lit))))))))))

  (std::defret bfr-constr-vars-bounded-of-glcp-bfr-to-pathcond
    (implies (pbfr-vars-bounded k t bfr)
             (bfr-constr-vars-bounded k bfr new-pathcond))
    :hints(("Goal" :in-theory (enable bfr-assume$a))))

  (std::defret bfr-constr-vars-bounded-of-glcp-bfr-to-pathcond-aig-mode
    (implies (and (pbfr-vars-bounded k t bfr)
                  (bfr-mode))
             (bfr-constr-vars-bounded k t new-pathcond))
    :hints (("goal" :use bfr-constr-vars-bounded-of-glcp-bfr-to-pathcond
             :in-theory (disable bfr-constr-vars-bounded-of-glcp-bfr-to-pathcond
                                 glcp-bfr-to-pathcond)))))


   
  

    







(defthm symbol-listp-alist-keys-of-shape-spec-bindingsp
  (implies (shape-spec-bindingsp x)
           (symbol-listp (alist-keys x)))
  :hints(("Goal" :in-theory (enable alist-keys))))

(defthm pseudo-term-listp-strip-cars-of-shape-spec-bindingsp
  (implies (shape-spec-bindingsp x)
           (pseudo-term-listp (alist-keys x)))
  :hints(("Goal" :in-theory (enable alist-keys))))




(local (defthm alistp-when-shape-spec-bindingsp
         (implies (shape-spec-bindingsp x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable shape-spec-bindingsp)))
         :rule-classes :forward-chaining))

(local (defthm all->=-len-when-shape-spec-bindingsp
         (implies (shape-spec-bindingsp x)
                  (acl2::all->=-len x 2))
         :hints(("Goal" :in-theory (enable shape-spec-bindingsp)))))

(defsection glcp-generic-geval-ev-of-extract-subset

  (local (defthm assoc-when-key
           (implies x
                    (equal (assoc x env)
                           (hons-assoc-equal x env)))
           :hints(("Goal" :in-theory (enable acl2::fal-extract member hons-assoc-equal)))))


  (acl2::defthm-simple-term-vars-flag
    (defthm glcp-generic-geval-ev-of-extract-variable-subset
      (implies (and (subsetp (simple-term-vars x) vars)
                    (pseudo-termp x))
               (equal (glcp-generic-geval-ev x (acl2::fal-extract vars env))
                      (glcp-generic-geval-ev x env)))
      :hints ('(:expand ((simple-term-vars x)
                         (pseudo-termp x))
                :in-theory (enable glcp-generic-geval-ev-of-fncall-args)))
      :flag simple-term-vars)
    (defthm glcp-generic-geval-ev-lst-of-extract-variable-subset
      (implies (and (subsetp (simple-term-vars-lst x) vars)
                    (pseudo-term-listp x))
               (equal (glcp-generic-geval-ev-lst x (acl2::fal-extract vars env))
                      (glcp-generic-geval-ev-lst x env)))
      :hints ('(:expand ((simple-term-vars-lst x)
                         (pseudo-term-listp x))))
      :flag simple-term-vars-lst)))




(defthm eval-of-dumb-negate-lit
  (iff (glcp-generic-geval-ev (dumb-negate-lit x) a)
       (not (glcp-generic-geval-ev x a)))
  :hints(("Goal" :in-theory (enable dumb-negate-lit))))



(defsection glcp-cov-clause
  (local (in-theory (enable glcp-cov-clause)))
  (local (std::set-define-current-function glcp-cov-clause))
;; (define glcp-cov-clause ((hypo pseudo-termp) (bindings shape-spec-bindingsp))
;;   :returns (cov-clause pseudo-term-listp :hyp :guard)
;;   (list '(not (gl-cp-hint 'coverage))
;;         (dumb-negate-lit hypo)
;;         (shape-spec-list-oblig-term (shape-spec-bindings->sspecs bindings) (alist-keys bindings)))
;;   ///
  (local (in-theory (disable shape-spec-bindingsp pseudo-term-listp pseudo-termp alistp
                             glcp-generic-geval-alt-def
                             GLCP-GENERIC-GEVAL-GENERAL-CONCRETE-OBJ-CORRECT)))
  (std::defret glcp-cov-clause-implies-coverage
    (b* (((mv bvars gvars) (shape-spec-list-invert (shape-spec-bindings->sspecs bindings)
                                                        (alist-keys bindings)))
         (env (cons (slice-to-bdd-env (glcp-generic-geval-ev-alist bvars a) nil)
                    (glcp-generic-geval-ev-alist gvars a))))
      (implies (and (glcp-generic-geval-ev (disjoin cov-clause) a)
                    (glcp-generic-geval-ev hypo a)
                    (shape-spec-bindingsp bindings)
                    (no-duplicatesp (shape-spec-list-indices (shape-spec-bindings->sspecs bindings)))
                    (no-duplicatesp (shape-spec-list-vars (shape-spec-bindings->sspecs bindings))))
               (equal (glcp-generic-geval-list (shape-spec-to-gobj-list (shape-spec-bindings->sspecs bindings)) env)
                      (glcp-generic-geval-ev-lst (alist-keys bindings) a))))
    :hints (("goal" :do-not-induct t
             :use ((:instance (:functional-instance shape-spec-list-oblig-term-correct
                               (sspec-geval-ev glcp-generic-geval-ev)
                               (sspec-geval glcp-generic-geval)
                               (sspec-geval-list glcp-generic-geval-list)
                               (sspec-geval-ev-lst glcp-generic-geval-ev-lst))
                    (x (shape-spec-bindings->sspecs bindings))
                    (obj-terms (alist-keys bindings)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable glcp-generic-geval-ev-of-fncall-args)
                   :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))))

(defsection glmc-cov-clause
  (local (in-theory (enable glmc-cov-clause)))
;; (define glmc-cov-clause ((config glmc-config-p))
;;   :returns (cov-clause pseudo-term-listp :hyp :guard)
;;   (b* (((glmc-config+ config)))
;;     (glcp-cov-clause `(if ,config.st-hyp ,config.in-hyp 'nil) config.shape-spec-alist))
;;   ///
  (define glmc-cov-env ((config glmc-config-p) (a alistp))
    :verify-guards nil
    (b* (((glmc-config+ config))
         ((mv bvars gvars)
          (shape-spec-list-invert (shape-spec-bindings->sspecs config.shape-spec-alist)
                                  (alist-keys config.shape-spec-alist))))
      (cons (slice-to-bdd-env (glcp-generic-geval-ev-alist bvars a) nil)
            (glcp-generic-geval-ev-alist gvars a))))

  (defthm glmc-cov-clause-implies-coverage
    (b* ((env (glmc-cov-env config a))
         ((glmc-config+ config))
         (bindings config.shape-spec-alist))
      (implies (and (glcp-generic-geval-ev (disjoin (glmc-cov-clause config)) a)
                    (glcp-generic-geval-ev config.in-hyp a)
                    (glcp-generic-geval-ev config.st-hyp a)
                    (glmc-config-p config)
                    (no-duplicatesp (shape-spec-list-indices (shape-spec-bindings->sspecs bindings)))
                    (no-duplicatesp (shape-spec-list-vars (shape-spec-bindings->sspecs bindings))))
               (equal (glcp-generic-geval-list (shape-spec-to-gobj-list (shape-spec-bindings->sspecs bindings)) env)
                      (glcp-generic-geval-ev-lst (alist-keys bindings) a))))
    :hints(("Goal" :in-theory (e/d (glmc-cov-env)
                                   (glcp-cov-clause-implies-coverage))
           :use ((:instance glcp-cov-clause-implies-coverage
                  (hypo (b* (((glmc-config+ config)))
                          `(if ,config.st-hyp ,config.in-hyp 'nil)))
                  (bindings (b* (((glmc-config+ config))) config.shape-spec-alist)))))))

  (defthm glmc-cov-clause-implies-oblig-term
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp (disjoin (glmc-cov-clause config)))
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist))
               (glcp-generic-geval-ev
                (shape-spec-list-oblig-term
                 (shape-spec-bindings->sspecs config.shape-spec-alist)
                 (alist-keys config.shape-spec-alist))
                alist)))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-falsify-sufficient
                           (x (disjoin (glmc-cov-clause config)))
                           (a alist)))
             :in-theory (enable glcp-cov-clause)))))
        

(defsection glmc-generic-interp-hyp
;; (define glmc-generic-interp-hyp ((hyp-name stringp)
;;                                  (hypo pseudo-termp)
;;                                  (alist)
;;                                  pathcond
;;                                  (config glcp-config-p)
;;                                  interp-st
;;                                  bvar-db
;;                                  state)
;;   :guard (and (acl2::interp-defs-alistp (glcp-config->overrides config))
;;               (acl2::interp-defs-alistp (is-obligs interp-st)))
;;   :returns (mv hyp-bfr er new-pathcond new-interp-st new-bvar-db new-state)
;;   (b* (((glcp-config config))
;;        ((mv hyp-bfr er pathcond interp-st bvar-db state)
;;         (glcp-generic-interp-test hypo alist pathcond config.hyp-clk config interp-st bvar-db state))
;;        ((when er)
;;         (mv nil
;;             (msg "Error interpreting ~s0 hyp: ~@1" hyp-name er)
;;             pathcond interp-st bvar-db state))
;;        (er (glcp-vacuity-check hyp-bfr config))
;;        ((when er)
;;         (mv nil
;;             (msg "Vacuity check for ~s0 hyp failed: ~@1" hyp-name er)
;;             pathcond interp-st bvar-db state)))
;;     (mv hyp-bfr nil pathcond interp-st bvar-db state))
;;   ///
  (local (in-theory (enable glmc-generic-interp-hyp)))
  (local (std::set-define-current-function glmc-generic-interp-hyp))

  (verify-guards glmc-generic-interp-hyp)

  (std::defret interp-defs-of-glmc-generic-interp-hyp
    (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                  (acl2::interp-defs-alistp (glcp-config->overrides config))
                  (pseudo-termp hypo))
             (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st))))

  (std::defret glmc-generic-interp-hyp-hyp-bfr-correct
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (equal bfr-env (car env))
                  (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                  (bfr-hyp-eval pathcond bfr-env)
                  (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                  (equal (w state0) (w state))
                  (not er)
                  (bfr-eval (glcp-config->param-bfr config) bfr-env)
                  ;; this hyp is so that we can match the glcp-interp-accs-ok
                  ;; with arbitrary config.
                  (or (bfr-mode)
                      (equal config1 config)))
             (equal (bfr-eval hyp-bfr bfr-env)
                    (bool-fix (glcp-generic-geval-ev hypo (glcp-generic-geval-alist alist env))))))

  (std::defret glmc-generic-interp-hyp-constraint-correct
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (equal bfr-env (car env))
                  (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                  (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                  (equal (w state0) (w state))
                  (bfr-eval (glcp-config->param-bfr config) bfr-env)
                  (or (bfr-mode) (equal config1 config)))
             (bfr-hyp-eval (nth *is-constraint* new-interp-st) bfr-env)))

  (std::defret glmc-generic-interp-hyp-accs-ok
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (bfr-mode))
             (glcp-interp-accs-ok interp-st bvar-db config1 env))
    :hints (("goal" :use ((:instance GLCP-GENERIC-INTERP-ACCS-OK-FINAL-IMPLIES-START-TEST
                           (X hypo) (CLK (glcp-config->hyp-clk config))
                           (ST state)))
             :in-theory (disable glcp-generic-interp-accs-ok-final-implies-start-test)))
    :rule-classes :forward-chaining)
  
  (std::defret w-state-preserved-of-glmc-generic-interp-hyp
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glmc-generic-interp-hyp
      (implies (state-p1 state) (state-p1 new-state)))

  (std::defret bvar-db-extension-p-of-glmc-generic-interp-hyp
    (bvar-db-extension-p new-bvar-db bvar-db))

  (std::defret glmc-generic-interp-hyp-vars-bounded
    (b* (((glcp-config config)))
      (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bfr-vars-bounded k p)
                    (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                    (equal nn (next-bvar$a new-bvar-db))
                    (equal p config.param-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k p alist))
               (and (pbfr-vars-bounded k p hyp-bfr)
                    (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                             (bfr-constr-vars-bounded k p (nth *is-constraint* new-interp-st)))
                    (bvar-db-vars-bounded k p nn new-bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* new-interp-st))))))

  (std::defret glmc-generic-interp-hyp-bvar-db-ordered
    (b* (((glcp-config config))
         (k (next-bvar$a bvar-db)))
      (implies (and (gobj-alist-vars-bounded k p alist)
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (equal p config.param-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st)))
               (bvar-db-orderedp p new-bvar-db))))

  (std::defret glmc-generic-interp-hyp-pathcond-preserved
    (equal new-pathcond (bfr-hyp-fix pathcond)))

  (std::defret interp-st-obligs-extension-p-of-glmc-generic-interp-hyp
    (interp-st-obligs-extension-p new-interp-st interp-st)))




(define hyp-tuplelist-alists-bounded ((k natp) p (tuples hyp-tuplelist-p))
  :verify-guards nil
  (b* (((when (atom tuples)) t)
       ((hyp-tuple tuple) (car tuples)))
    (and (gobj-alist-vars-bounded k p tuple.alist)
         (hyp-tuplelist-alists-bounded k p (cdr tuples))))
  ///
  (defthm hyp-tuplelist-alists-bounded-of-cons
    (equal (hyp-tuplelist-alists-bounded k p (cons a b))
           (b* (((hyp-tuple tuple) a))
             (and (gobj-alist-vars-bounded k p tuple.alist)
                  (hyp-tuplelist-alists-bounded k p b)))))

  (defthm hyp-tuplelist-alists-bounded-of-increase
    (implies (and (hyp-tuplelist-alists-bounded k p tuples)
                  (<= (nfix k) (nfix k1)))
             (hyp-tuplelist-alists-bounded k1 p tuples)))

  (Defthm hyp-duplelist-alists-bounded-of-nil
    (equal (hyp-tuplelist-alists-bounded k p nil) t)))

(defsection glmc-generic-interp-hyp-tuples
  (local (in-theory (enable glmc-generic-interp-hyp-tuples)))
  (local (std::set-define-current-function glmc-generic-interp-hyp-tuples))
  (verify-guards glmc-generic-interp-hyp-tuples)
;; (define glmc-generic-interp-hyp-tuples ((tuples hyp-tuplelist-p)
;;                                         pathcond
;;                                         (config glcp-config-p)
;;                                         interp-st
;;                                         bvar-db
;;                                         state)
;;   :guard (and (acl2::interp-defs-alistp (glcp-config->overrides config))
;;               (acl2::interp-defs-alistp (is-obligs interp-st)))
;;   :returns (mv bfr-list er new-pathcond new-interp-st new-bvar-db new-state)
;;   (b* (((when (atom tuples))
;;         (b* ((pathcond (lbfr-hyp-fix pathcond)))
;;           (mv nil nil pathcond interp-st bvar-db state)))
;;        ((hyp-tuple tuple) (car tuples))
;;        ((mv bfr er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-hyp tuple.name tuple.term tuple.alist pathcond config interp-st bvar-db state))
;;        ((when er)
;;         (mv nil er pathcond interp-st bvar-db state))
;;        ((mv rest er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-hyp-tuples (cdr tuples) pathcond config interp-st bvar-db state)))
;;     (mv (and (not er) (cons bfr rest))
;;         er pathcond interp-st bvar-db state))
;;   ///
  (std::defret interp-defs-of-glmc-generic-interp-hyp-tuples
    (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                  (acl2::interp-defs-alistp (glcp-config->overrides config))
                  (hyp-tuplelist-p tuples))
             (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st))))

  

  (std::defret glmc-generic-interp-hyp-tuples-accs-ok
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (bfr-mode))
             (glcp-interp-accs-ok interp-st bvar-db config1 env))
    :rule-classes :forward-chaining)

  (local (defun eval-tuples (tuples env)
           (b* (((when (atom tuples)) nil)
                ((hyp-tuple tuple) (car tuples)))
             (cons (bool-fix (glcp-generic-geval-ev tuple.term (glcp-generic-geval-alist tuple.alist env)))
                   (eval-tuples (cdr tuples) env)))))

  (local (std::defret glmc-generic-interp-hyp-tuples-eval-tuples-correct
           (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                         (bfr-mode)
                         (equal bfr-env (car env))
                         (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                         (bfr-hyp-eval pathcond bfr-env)
                         (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                         (equal (w state0) (w state))
                         (not er)
                         (bfr-eval (glcp-config->param-bfr config) bfr-env))
                    (equal (bfr-eval-list bfr-list bfr-env)
                           (eval-tuples tuples env)))
           :hints(("Goal" :in-theory (enable eval-tuples bfr-eval-list)))))

  (local (defthm nth-of-eval-tuples
           (equal (nth n (eval-tuples tuples env))
                  (b* (((hyp-tuple tuple) (nth n tuples)))
                    (bool-fix (glcp-generic-geval-ev tuple.term (glcp-generic-geval-alist tuple.alist env)))))
           :hints (("goal" :in-theory (enable nth)))))

  (local (defthmd bfr-eval-of-nth
           (equal (bfr-eval (nth n x) env)
                  (nth n (bfr-eval-list x env)))
           :hints(("Goal" :in-theory (enable nth)))))

  ;; (local (defthmd nth-of-atom
  ;;          (implies (atom x)
  ;;                   (equal (nth n x) nil))))

  (std::defret glmc-generic-interp-hyp-tuples-nth-bfr-correct
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (bfr-mode)
                  (equal bfr-env (car env))
                  (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                  (bfr-hyp-eval pathcond bfr-env)
                  (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                  (equal (w state0) (w state))
                  (not er)
                  (bfr-eval (glcp-config->param-bfr config) bfr-env))
             (equal (bfr-eval (nth n bfr-list) bfr-env)
                    (b* (((hyp-tuple tuple) (nth n tuples)))
                      (bool-fix (glcp-generic-geval-ev tuple.term (glcp-generic-geval-alist tuple.alist env))))))
    :hints(("Goal" :in-theory (e/d (bfr-eval-of-nth)
                                   (glmc-generic-interp-hyp-tuples)))))

  (std::defret glmc-generic-interp-hyp-tuples-constraint-correct
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (bfr-mode)
                  (equal bfr-env (car env))
                  (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                  (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                  (equal (w state0) (w state))
                  (bfr-eval (glcp-config->param-bfr config) bfr-env))
             (bfr-hyp-eval (nth *is-constraint* new-interp-st) bfr-env)))

  
  (std::defret w-state-preserved-of-glmc-generic-interp-hyp-tuples
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glmc-generic-interp-hyp-tuples
    (implies (state-p1 state) (state-p1 new-state)))

  (std::defret bvar-db-extension-p-of-glmc-generic-interp-hyp-tuples
    (bvar-db-extension-p new-bvar-db bvar-db))

  (local (in-theory (enable hyp-tuplelist-alists-bounded)))

  (std::defret glmc-generic-interp-hyp-tuples-vars-bounded
    (b* (((glcp-config config)))
      (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bfr-vars-bounded k p)
                    (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                    (equal nn (next-bvar$a new-bvar-db))
                    (equal p config.param-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (hyp-tuplelist-alists-bounded k p tuples))
               (and (pbfr-list-vars-bounded k p bfr-list)
                    (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                             (bfr-constr-vars-bounded k p (nth *is-constraint* new-interp-st)))
                    (bvar-db-vars-bounded k p nn new-bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* new-interp-st))))))

  (std::defret glmc-generic-interp-hyp-tuples-bvar-db-ordered
    (b* (((glcp-config config))
         (k (next-bvar$a bvar-db)))
      (implies (and (hyp-tuplelist-alists-bounded k p tuples)
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (equal p config.param-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st)))
               (bvar-db-orderedp p new-bvar-db))))

  (std::defret glmc-generic-interp-hyp-tuples-bvar-db-ordered-aig-mode
    (b* (((glcp-config config))
         (k (next-bvar$a bvar-db))
         (p config.param-bfr))
      (implies (and (hyp-tuplelist-alists-bounded k p tuples)
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (bfr-mode))
               (bvar-db-orderedp t new-bvar-db)))
    :hints (("goal" :use ((:instance glmc-generic-interp-hyp-tuples-bvar-db-ordered
                           (p (glcp-config->param-bfr config))))
             :in-theory (disable glmc-generic-interp-hyp-tuples-bvar-db-ordered
                                 glmc-generic-interp-hyp-tuples))))

  (std::defret glmc-generic-interp-hyp-tuples-pathcond-preserved
    (equal new-pathcond (bfr-hyp-fix pathcond)))

  (std::defret true-listp-of-glmc-generic-interp-hyp-tuples
    (true-listp bfr-list)
    :rule-classes :type-prescription)

  (std::defret interp-st-obligs-extension-p-of-glmc-generic-interp-hyp-tuples
    (interp-st-obligs-extension-p new-interp-st interp-st)))


(defthm pbfr-vars-bounded-of-nth
  (implies (pbfr-list-vars-bounded k p x)
           (pbfr-vars-bounded k p (nth n x)))
  :hints(("Goal" :in-theory (enable nth))))
           





    


(defthm alist-keys-of-shape-specs-to-interp-al
  (equal (alist-keys (shape-specs-to-interp-al x))
         (alist-keys x))
  :hints(("Goal" :in-theory (enable alist-keys shape-specs-to-interp-al))))

(defthm gobj-alist-vars-bounded-of-fal-extract
  (implies (gobj-alist-vars-bounded k p x)
           (gobj-alist-vars-bounded k p (acl2::fal-extract vars x)))
  :hints(("Goal" :in-theory (enable acl2::fal-extract gobj-alist-vars-bounded))))



(local (in-theory (disable acl2::fal-extract acl2::fal-extract-of-cons)))



(defthm other-fields-of-glcp-config-update-param
  (b* (((glcp-config new-config) (glcp-config-update-param bfr config))
       ((glcp-config config)))
    (and (equal new-config.shape-spec-alist config.shape-spec-alist)
         (equal new-config.overrides config.overrides)))
  :hints(("Goal" :in-theory (enable glcp-config-update-param))))



(local (in-theory (disable (bfr-hyp-fix) (bfr-hyp-init$a))))


(defthm hons-assoc-equal-of-gobj-alist-to-param-space
  (equal (hons-assoc-equal k (gobj-alist-to-param-space x p))
         (and (hons-assoc-equal k x)
              (cons k (gobj-to-param-space (cdr (hons-assoc-equal k x)) p)))))

(defthm car-of-hons-assoc-equal
  (equal (car (hons-assoc-equal k x))
         (and (hons-assoc-equal k x) k)))

(defthm fal-extract-of-gobj-alist-to-param-space
  (equal (acl2::fal-extract vars (gobj-alist-to-param-space x p))
         (gobj-alist-to-param-space (acl2::fal-extract vars x) p))
  :hints(("Goal" :in-theory (enable acl2::fal-extract gobj-alist-to-param-space)
          :induct (acl2::fal-extract vars x))))







(defsection glmc-generic-interp-hyps
  (local (in-theory (enable glmc-generic-interp-hyps)))
  (local (std::set-define-current-function glmc-generic-interp-hyps))
  (verify-guards glmc-generic-interp-hyps)
;; (define glmc-generic-interp-hyps ((config glmc-config-p)
;;                                   ;; pathcond
;;                                   interp-st
;;                                   bvar-db
;;                                   state)
;;   :guard (b* (((glmc-config+ config)))
;;            (and (acl2::interp-defs-alistp config.overrides)
;;                 (acl2::interp-defs-alistp (is-obligs interp-st))
;;                 (non-exec (equal interp-st (create-interp-st)))))
;;   :returns (mv st-hyp-bfr in-hyp-bfr er new-interp-st new-bvar-db new-state)
;;   (b* (((glmc-config+ config) (glmc-config-update-param t config))
;;        ((acl2::local-stobjs pathcond)
;;         (mv st-hyp-bfr in-hyp-bfr er pathcond interp-st bvar-db state))
       
;;        (next-bvar (shape-spec-max-bvar-list (shape-spec-bindings->sspecs config.shape-spec-alist)))
;;        (bvar-db (init-bvar-db next-bvar bvar-db))

;;        ((mv er interp-st) (init-interp-st interp-st state))
;;        ((when er)
;;         (mv nil nil er pathcond interp-st bvar-db state))

;;        (pathcond (bfr-hyp-init pathcond))

;;        (alist (shape-specs-to-interp-al config.shape-spec-alist))

;;        (st-alist (alist-extract (list config.st-var) alist))
;;        (in-alist (acl2::fal-extract (remove-equal config.st-var (alist-keys alist)) alist))

;;        (tuples (list (make-hyp-tuple :name "state" :term config.st-hyp :alist st-alist)
;;                      (make-hyp-tuple :name "input" :term config.in-hyp :alist in-alist)))

;;        ((mv (acl2::nths st-hyp-bfr in-hyp-bfr) er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-hyp-tuples tuples pathcond config.glcp-config interp-st bvar-db state))
;;        ((when er)
;;         (mv nil nil er pathcond interp-st bvar-db state)))

;;     (mv st-hyp-bfr in-hyp-bfr nil pathcond interp-st bvar-db state))

  ;; ///
  (local (Defthm alistp-remove-equal
           (implies (alistp x)
                    (alistp (remove-equal k x)))
           :hints(("Goal" :in-theory (enable remove-equal)))))

  (defthm glmc-generic-interp-hyps-normalize
    (implies (syntaxp (not (and (equal interp-st ''nil)
                                (equal bvar-db ''nil))))
             (equal (glmc-generic-interp-hyps config interp-st bvar-db state)
                    (glmc-generic-interp-hyps config nil nil state))))

  ;; (local (in-theory (enable glcp-config-update-param)))

  (std::defret interp-defs-of-glmc-generic-interp-hyps
    (b* (((glmc-config+ config1) (glmc-config-update-param t config)))
      (implies (and ; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp config1.overrides)
                    (glmc-config-p config))
               (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st)))))

  (std::defret glmc-generic-interp-hyps-bfrs-correct
    (b* (((glmc-config+ config1) (glmc-config-update-param t config))
         (alist (shape-specs-to-interp-al config1.shape-spec-alist))
         ;; (in-alist (acl2::fal-extract (remove config1.st-var (alist-keys config1.shape-spec-alist))
         ;;                              alist))
         (st-alist (acl2::fal-extract (list config1.st-var) alist)))
      (implies (and (bind-free (case-match bfr-env
                                 (('bvar-db-fix-env & & & & & cdr)
                                  `((env . (cons ,bfr-env ,cdr))))
                                 (& '((try-to-bind-by-hyp . try-to-bind-by-hyp)))))
                    (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                    (bfr-mode)
                    (equal bfr-env (car env))
; (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ;; (bfr-hyp-eval pathcond bfr-env)
; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;;(glmc-config-p config)
                    ;; (assoc config1.st-var config1.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er))
               (and 
                (iff (bfr-eval st-hyp-bfr bfr-env)
                     (glcp-generic-geval-ev config1.st-hyp (glcp-generic-geval-alist st-alist env)))
                (iff (bfr-eval in-hyp-bfr bfr-env)
                     (glcp-generic-geval-ev config1.in-hyp (glcp-generic-geval-alist alist env)))))))

  (std::defret glmc-generic-interp-hyps-constraint-correct
    (b* (((glmc-config+ config1) (glmc-config-update-param t config)))
      (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                    (bfr-mode)
                    (equal bfr-env (car env))
                    ; (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (glmc-config-p config)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) bfr-env))))

  ;; (std::defret glmc-generic-interp-hyps-accs-ok
  ;;   (b* (((glmc-config+ config))
  ;;        (config1.glcp-config  (glcp-config-update-param t config.glcp-config)))
  ;;     (implies (glcp-interp-accs-ok new-interp-st new-bvar-db config1.glcp-config env)
  ;;              (glcp-interp-accs-ok interp-st bvar-db config1.glcp-config env)))
  ;;   :rule-classes :forward-chaining)

  
  (std::defret w-state-preserved-of-glmc-generic-interp-hyps
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glmc-generic-interp-hyps
      (implies (state-p1 state) (state-p1 new-state)))

  ;; (std::defret bvar-db-extension-p-of-glmc-generic-interp-hyps
  ;;   (bvar-db-extension-p new-bvar-db bvar-db))

  (std::defret glmc-generic-interp-hyps-vars-bounded
    (b* (((glmc-config+ config1) (glmc-config-update-param t config)))
      (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                    ;; (bvar-db-vars-bounded k t (next-bvar$a bvar-db) bvar-db)
                    (equal nn (next-bvar$a new-bvar-db))
                    ;; (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
                    ;; (<= (shape-spec-max-bvar-list
                    ;;      (shape-spec-bindings->sspecs config1.shape-spec-alist))
                    ;;     (nfix k))
                    )
               (and (pbfr-vars-bounded k t in-hyp-bfr)
                    (pbfr-vars-bounded k t st-hyp-bfr)
                    ; (implies (bfr-constr-vars-bounded k t (nth *is-constraint* interp-st))
                    (bfr-constr-vars-bounded k t (nth *is-constraint* new-interp-st))
                    (bvar-db-vars-bounded k t nn new-bvar-db)
                    (implies (not er)
                             (gbc-db-vars-bounded k t (nth *is-constraint-db* new-interp-st))))))
    :hints(("Goal" :in-theory (enable gbc-db-empty-implies-gbc-db-vars-bounded))))

  (std::defret glmc-generic-interp-hyps-bvar-db-ordered
    (b* (((glmc-config+ config1) (glmc-config-update-param t config))
         ;; (k (next-bvar$a bvar-db))
         )
      ;; (implies (and ;; (<= (shape-spec-max-bvar-list
      ;;               ;;      (shape-spec-bindings->sspecs config1.shape-spec-alist))
      ;;               ;;     (nfix k))
      ;;               ;; (bvar-db-orderedp t bvar-db)
      ;;           ;; (bvar-db-vars-bounded k t k bvar-db)
      ;;               ;; (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
      ;;               )
               (bvar-db-orderedp t new-bvar-db))
    :hints(("Goal" :in-theory (enable gbc-db-empty-implies-gbc-db-vars-bounded))))

  ;; (std::defret interp-st-obligs-extension-p-of-glmc-generic-interp-hyps
  ;;   (interp-st-obligs-extension-p new-interp-st interp-st))
  
  (std::defret glmc-generic-interp-hyps-base-bvar
    (b* (((glmc-config+ config)))
      (equal (base-bvar$a new-bvar-db)
             (shape-spec-max-bvar-list
              (shape-spec-bindings->sspecs config.shape-spec-alist)))))


  (std::defret glmc-generic-interp-hyps-fix-env
    (b* (;(glcp-config (glcp-config-update-param t (glmc-config->glcp-config config)))
         ((glmc-config+ config1) (glmc-config-update-param t config))
         (alist (shape-specs-to-interp-al config1.shape-spec-alist))
         ;; (in-alist (acl2::fal-extract (remove config1.st-var (alist-keys config1.shape-spec-alist))
         ;;                              alist))
         (st-alist (acl2::fal-extract (list config1.st-var) alist))
         (fix-bfr-env (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                       base-bvar new-bvar-db t bfr-env var-env)))
      (implies (and (bind-free (case-match bfr-env
                                 (('bvar-db-fix-env & & & & & cdr)
                                  `((env . (cons ,bfr-env ,cdr))))
                                 (& '((try-to-bind-by-hyp . try-to-bind-by-hyp)))))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (equal base-bvar (base-bvar$a new-bvar-db))
; (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ;; (bfr-hyp-eval pathcond bfr-env)
; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (glmc-config-p config)
                    ;; (assoc config1.st-var config1.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode))
               (and 
                (iff (bfr-eval st-hyp-bfr fix-bfr-env)
                     (glcp-generic-geval-ev config1.st-hyp (glcp-generic-geval-alist st-alist (cons bfr-env var-env))))
                (iff (bfr-eval in-hyp-bfr fix-bfr-env)
                     (glcp-generic-geval-ev config1.in-hyp (glcp-generic-geval-alist alist (cons bfr-env var-env)))))))
    :hints (("goal" :in-theory (e/d (glcp-interp-accs-ok) (glmc-generic-interp-hyps))
             :use ((:instance glmc-generic-interp-hyps-bfrs-correct
                    (bfr-env (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                              (base-bvar$a new-bvar-db)
                                              new-bvar-db t bfr-env var-env))
                    (env (cons (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                                  (base-bvar$a new-bvar-db)
                                                  new-bvar-db t bfr-env var-env)
                               var-env)))))))

  (std::defret glmc-generic-interp-hyps-fix-env-constraint-correct
    (b* (((glmc-config+ config1) (glmc-config-update-param t config))
         (fix-bfr-env (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                       base-bvar new-bvar-db t bfr-env var-env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (equal base-bvar (base-bvar$a new-bvar-db))
                    ; (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (glmc-config-p config)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (bfr-mode))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) fix-bfr-env)))
    :hints (("goal" :in-theory (e/d (glcp-interp-accs-ok) (glmc-generic-interp-hyps))
             :use ((:instance glmc-generic-interp-hyps-constraint-correct
                    (bfr-env (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                              (base-bvar$a new-bvar-db)
                                              new-bvar-db t bfr-env var-env))
                    (env (cons (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                                  (base-bvar$a new-bvar-db)
                                                  new-bvar-db t bfr-env var-env)
                               var-env))))))))

(defthm bvar-db-vars-bounded-when-ordered
  (implies (and (<= (nfix n) (nfix k))
                (<= (nfix n) (next-bvar$a bvar-db))
                (bvar-db-orderedp p bvar-db))
           (bvar-db-vars-bounded k p n bvar-db))
  :hints(("Goal" :in-theory (enable bvar-db-vars-bounded)
          :induct t)
         (and stable-under-simplificationp
              '(:use ((:instance bvar-db-orderedp-necc
                       (n (+ -1 n))))
                :in-theory (disable bvar-db-orderedp-necc)))))


;; (defsection glcp-generic-geval-alist-of-shape-specs-to-interp-al-in-terms-of-list
;;   (local (defthm glcp-generic-geval-alist-is-pairlis$
;;            (equal (glcp-generic-geval-alist x env)
;;                   (pairlis$ (alist-keys x) (glcp-generic-geval-list (alist-vals x) env)))
;;            :hints(("Goal" :in-theory (enable glcp-generic-geval-list
;;                                              glcp-generic-geval-alist
;;                                              alist-keys alist-vals)))))

;;   (local (defthm shape-specs-to-interp-al-is-pairlis$
;;            (equal (shape-specs-to-interp-al x)
;;                   (pairlis$ (alist-keys x) (shape-spec-to-gobj-list (shape-spec-bindings->sspecs x))))
;;            :hints(("Goal" :in-theory (enable shape-spec-bindings->sspecs alist-keys
;;                                              shape-specs-to-interp-al
;;                                              shape-spec-to-gobj-list)))))

;;   )

;; (local (defthm-gobj-flag
;;          (defthm glcp-generic-geval-of-bvar-db-fix-env-when-bounded



(defthm lookup-in-pairlis$-of-eval-keys
  (implies k
           (equal (assoc k (pairlis$ keys (glcp-generic-geval-ev-lst keys alist)))
                  (and (member k keys)
                       (cons k (glcp-generic-geval-ev k alist))))))

(acl2::defthm-simple-term-vars-flag
  (defthm glcp-generic-geval-ev-of-pairlis$-eval-keys
    (implies (and (subsetp (simple-term-vars x) vars))
             (equal (glcp-generic-geval-ev x (pairlis$ vars (glcp-generic-geval-ev-lst vars alist)))
                    (glcp-generic-geval-ev x alist)))
    :hints ('(:expand ((simple-term-vars x)
                       (pseudo-termp x))
              :in-theory (enable glcp-generic-geval-ev-of-fncall-args
                                 glcp-generic-geval-ev-of-nonsymbol-atom)))
    :flag simple-term-vars)
  (defthm glcp-generic-geval-ev-lst-of-pairlis$-eval-keys
    (implies (and (subsetp (simple-term-vars-lst x) vars))
             (equal (glcp-generic-geval-ev-lst x (pairlis$ vars (glcp-generic-geval-ev-lst vars alist)))
                    (glcp-generic-geval-ev-lst x alist)))
    :hints ('(:expand ((simple-term-vars-lst x)
                       (pseudo-term-listp x))))
    :flag simple-term-vars-lst))


(defsection glcp-generic-geval-alist-of-shape-specs-to-interp-al
  (local (defthm glcp-generic-geval-alist-is-pairlis$
           (equal (glcp-generic-geval-alist x env)
                  (pairlis$ (alist-keys x) (glcp-generic-geval-list (alist-vals x) env)))
           :hints(("Goal" :in-theory (enable glcp-generic-geval-list
                                             glcp-generic-geval-alist
                                             alist-keys alist-vals)))))

  (local (defthm shape-specs-to-interp-al-is-pairlis$
           (equal (shape-specs-to-interp-al x)
                  (pairlis$ (alist-keys x) (shape-spec-to-gobj-list (shape-spec-bindings->sspecs x))))
           :hints(("Goal" :in-theory (enable shape-spec-bindings->sspecs alist-keys
                                             shape-specs-to-interp-al
                                             shape-spec-to-gobj-list)))))

  (local (defthm alist-vals-of-pairlis$
           (equal (alist-vals (pairlis$ x y))
                  (take (len x) y))
           :hints(("Goal" :in-theory (enable alist-vals pairlis$)))))

  (local (defthm take-of-same-len
           (implies (equal (nfix n) (len x))
                    (equal (take n x) (list-fix x)))))

  (local (defthm len-of-shape-spec-to-gobj-list
           (Equal (len (shape-spec-to-gobj-list x)) (len x))
           :hints(("Goal" :in-theory (enable shape-spec-to-gobj-list)))))

  (local (defthm len-of-shape-spec-bindings->sspecs
           (Equal (len (shape-spec-bindings->sspecs x))
                  (len (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys shape-spec-bindings->sspecs)))))

  (defthm glcp-generic-geval-alist-of-shape-specs-to-interp-al
    (b* (((mv bvars gvars) (shape-spec-list-invert (shape-spec-bindings->sspecs shape-spec-alist)
                                                   (alist-keys shape-spec-alist)))
         (env (cons (slice-to-bdd-env (glcp-generic-geval-ev-alist bvars alist) nil)
                    (glcp-generic-geval-ev-alist gvars alist))))
      (implies (and (glcp-generic-geval-ev (shape-spec-list-oblig-term
                                            (shape-spec-bindings->sspecs shape-spec-alist)
                                            (alist-keys shape-spec-alist))
                                           alist)
                    (shape-spec-bindingsp shape-spec-alist)
                    (no-duplicatesp (shape-spec-list-indices
                                     (shape-spec-bindings->sspecs shape-spec-alist)))
                    (no-duplicatesp (shape-spec-list-vars
                                     (shape-spec-bindings->sspecs shape-spec-alist))))
               (equal (glcp-generic-geval-alist (shape-specs-to-interp-al shape-spec-alist) env)
                      (pairlis$ (alist-keys shape-spec-alist)
                                (glcp-generic-geval-ev-lst (alist-keys shape-spec-alist) alist))))))

  (defthm glcp-generic-geval-alist-of-glmc-cov-env
    (b* (((glmc-config+ config))
         (env (glmc-cov-env config alist)))
      (implies (and (glcp-generic-geval-ev (shape-spec-list-oblig-term
                                            (shape-spec-bindings->sspecs config.shape-spec-alist)
                                            (alist-keys config.shape-spec-alist))
                                           alist)
                    (glmc-config-p config)
                    (no-duplicatesp (shape-spec-list-indices
                                     (shape-spec-bindings->sspecs config.shape-spec-alist)))
                    (no-duplicatesp (shape-spec-list-vars
                                     (shape-spec-bindings->sspecs config.shape-spec-alist))))
               (equal (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist) env)
                      (pairlis$ (alist-keys config.shape-spec-alist)
                                (glcp-generic-geval-ev-lst (alist-keys config.shape-spec-alist) alist)))))
    :hints(("Goal" :in-theory (enable glmc-cov-env)))))




                                                      
;; (define glmc-generic-interp-hyps-env ((env consp)
;;                                       (config glmc-config-p)
;;                                       state)
;;   :non-executable t
;;   :verify-guards nil
;;   :returns (new-env consp :rule-classes :type-prescription)
;;   (b* (((glmc-config+ config))
;;        ((mv & & & & new-bvar-db &)
;;         (glmc-generic-interp-hyps config nil nil state))

;;        ;; (env-term (shape-spec-list-env-term (shape-spec-bindings->sspecs config.shape-spec-alist)
;;        ;;                                     (alist-keys config.shape-spec-alist)))
;;        ;; (env1 (glcp-generic-geval-ev env-term alist))
;;        (bfr-env (bvar-db-fix-env (next-bvar new-bvar-db)
;;                                  (base-bvar new-bvar-db)
;;                                  new-bvar-db
;;                                  t (car env)
;;                                  (cdr env))))
;;     (cons bfr-env (cdr env)))
;;   ///
;;   (local (in-theory (disable bvar-db-fix-env alistp
;;                              equal-of-booleans-rewrite)))

  
  
;;   (std::defret glmc-generic-interp-hyps-env-bvar-db-env-ok
;;     ;; (implies (bvar-db-orderedp t new-bvar-db)
;;     (b* (((mv & & & & new-bvar-db &)
;;           (glmc-generic-interp-hyps config interp-st bvar-db state)))
;;       (glcp-generic-bvar-db-env-ok new-bvar-db t (next-bvar$a new-bvar-db) new-env)))


;;   ;; (std::defret glmc-generic-interp-hyps-env-eval-bounded
;;   ;;   (b* (((glmc-config+ config)))
;;   ;;     (implies (pbfr-vars-bounded 
;;   ;;               (shape-spec-max-bvar-list
;;   ;;                (shape-spec-bindings->sspecs config.shape-spec-alist))
;;   ;;               t bfr)
;;   ;;              (equal (bfr-eval bfr (car new-env))
;;   ;;                     (bfr-eval bfr (car env)))))
;;   ;;   :hints(("Goal" :in-theory (enable glmc-generic-interp-hyps))))

;;   (std::defret glmc-generic-interp-hyps-env-eval-bounded-bfr
;;     (b* (((glmc-config+ config)))
;;       (implies (pbfr-vars-bounded
;;                 (shape-spec-max-bvar-list
;;                  (shape-spec-bindings->sspecs config.shape-spec-alist))
;;                 t x)
;;                (equal (bfr-eval x (car new-env))
;;                       (bfr-eval x (car env)))))
;;     :hints(("Goal" :in-theory (enable glmc-generic-interp-hyps))))


;;   (std::defret glmc-generic-interp-hyps-env-eval-bounded-gobj
;;     (b* (((glmc-config+ config)))
;;       (implies (gobj-vars-bounded
;;                 (shape-spec-max-bvar-list
;;                  (shape-spec-bindings->sspecs config.shape-spec-alist))
;;                 t x)
;;                (equal (glcp-generic-geval x new-env)
;;                       (glcp-generic-geval x env))))
;;     :hints(("Goal" :in-theory (enable glmc-generic-interp-hyps
;;                                       glcp-generic-geval-normalize-cons-car-cdr-env))))

;;   (std::defret glmc-generic-interp-hyps-env-eval-bounded-alist
;;     (b* (((glmc-config+ config)))
;;       (implies (gobj-alist-vars-bounded
;;                 (shape-spec-max-bvar-list
;;                  (shape-spec-bindings->sspecs config.shape-spec-alist))
;;                 t alist)
;;                (equal (glcp-generic-geval-alist alist new-env)
;;                       (glcp-generic-geval-alist alist env))))
;;     :hints(("Goal" :in-theory (enable glmc-generic-interp-hyps
;;                                       glcp-generic-geval-alist-normalize-cons-car-cdr-env)))))

;;   ;; (std::defret glmc-generic-interp-hyps-env-correct
;;   ;;   (b* (((glmc-config+ config)))
;;   ;;   (implies (and (<= (SHAPE-SPEC-MAX-BVAR-LIST (SHAPE-SPEC-BINDINGS->SSPECS config.shape-spec-alist))
;;   ;;                     (base-bvar$a new-BVAR-DB))
;;   ;;                 (glcp-generic-geval-ev (shape-spec-list-oblig-term
;;   ;;                                           (shape-spec-bindings->sspecs config.shape-spec-alist)
;;   ;;                                           (alist-keys config.shape-spec-alist))
;;   ;;                                          alist)
;;   ;;                 (shape-spec-bindingsp config.shape-spec-alist)
;;   ;;                 (not (glmc-syntax-checks config)))
;;   ;;            (equal (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist) env)
;;   ;;                   (pairlis$ (alist-keys config.shape-spec-alist)
;;   ;;                             (glcp-generic-geval-ev-lst (alist-keys config.shape-spec-alist) alist)))))))


(local (defthm glcp-generic-geval-alist-of-fal-extract
         (equal (GLCP-GENERIC-GEVAL-ALIST (ACL2::FAL-EXTRACT VARS ALIST) ENV)
                (ACL2::FAL-EXTRACT VARS (GLCP-GENERIC-GEVAL-ALIST ALIST ENV)))
         :hints(("Goal" :in-theory (enable acl2::fal-extract
                                           glcp-generic-geval-alist)))))

;; (local (in-theory (disable fal-extract-of-glcp-generic-geval-alist)))



;; (defthm glmc-generic-interp-hyps-correct-with-env
;;   (b* (((mv ?st-hyp-bfr ?in-hyp-bfr ?er ?new-interp-st ?new-bvar-db ?new-state)
;;         (glmc-generic-interp-hyps config interp-st bvar-db state))
;;        (env (glmc-generic-interp-hyps-env alist config new-bvar-db))
;;        ;; (glcp-config (glcp-config-update-param t (glmc-config->glcp-config config)))
;;        ((glmc-config+ config1) (glmc-config-update-param t config)))
;;     (implies (and (glcp-generic-geval-ev-theoremp
;;                    (conjoin-clauses
;;                     (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
;;                   ;; (equal bfr-env (car env))
;;                   (bfr-hyp-eval (is-constraint interp-st) (car env))
;;                   ;; (bfr-hyp-eval pathcond bfr-env)
;;                   (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
;;                   (acl2::interp-defs-alistp config1.overrides)
;;                   (glmc-config-p config)
;;                   ;; (assoc config1.st-var config1.shape-spec-alist)
;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
;;                   (equal (w state0) (w state))
;;                   (not er)
;;                   (glcp-generic-geval-ev (shape-spec-list-oblig-term
;;                                           (shape-spec-bindings->sspecs config1.shape-spec-alist)
;;                                           (alist-keys config1.shape-spec-alist))
;;                                          alist)
;;                   (<=
;;                    (SHAPE-SPEC-MAX-BVAR-LIST
;;                     (SHAPE-SPEC-BINDINGS->SSPECS
;;                      config1.shape-spec-alist))
;;                    (base-bvar$a BVAR-DB))
;;                   (bvar-db-orderedp t bvar-db)
;;                   (gbc-db-vars-bounded (base-bvar$a bvar-db) t (is-constraint-db interp-st))
;;                   (not (glmc-syntax-checks config)))
;;              (and (equal (bfr-eval st-hyp-bfr (car env))
;;                          (bool-fix (glcp-generic-geval-ev config1.st-hyp alist)))
;;                   (equal (bfr-eval in-hyp-bfr (car env))
;;                          (bool-fix (glcp-generic-geval-ev config1.in-hyp alist))))))
;;   :hints ((b* ((new-bvar-db '(mv-nth 4 (glmc-generic-interp-hyps config interp-st bvar-db state)))
;;                (env `(glmc-generic-interp-hyps-env alist config ,new-bvar-db)))
;;             `(:use ((:instance glmc-generic-interp-hyps-in-hyp-bfr-correct
;;                      (env ,env) (bfr-env (car ,env)))
;;                     (:instance glmc-generic-interp-hyps-st-hyp-bfr-correct
;;                      (env ,env) (bfr-env (car ,env))))
;;               :in-theory (e/d (glcp-interp-accs-ok)
;;                               (glmc-generic-interp-hyps-in-hyp-bfr-correct
;;                                glmc-generic-interp-hyps-st-hyp-bfr-correct))))))



(defthm bfr-eval-of-bvar-db-fix-env-when-vars-bounded-aig-mode
  (implies (and (pbfr-vars-bounded min q x)
                (bfr-mode))
           (equal (bfr-eval x (bvar-db-fix-env max min bvar-db p bfr-env var-env))
                  (bfr-eval x bfr-env)))
  :hints(("Goal" :in-theory (enable bvar-db-fix-env bfr-unparam-env bfr-param-env))))

(defthm bfr-hyp-eval-of-bvar-db-fix-env-when-vars-bounded-aig-mode
  (implies (and (bfr-constr-vars-bounded min q hyp)
                (bfr-mode))
           (equal (bfr-hyp-eval hyp (bvar-db-fix-env max min bvar-db p bfr-env var-env))
                  (bfr-hyp-eval hyp bfr-env)))
  :hints(("Goal" :use ((:instance bfr-eval-of-bvar-db-fix-env-when-vars-bounded-aig-mode
                        (x (bfr-constr->bfr hyp))))
          :in-theory (disable bfr-eval-of-bvar-db-fix-env-when-vars-bounded-aig-mode
                              pbfr-vars-bounded-in-aig-mode))))


(defthm GOBJ-ALIST-VARS-BOUNDED-OF-GOBJ-ALIST-TO-PARAM-SPACE-aig-mode
  (implies (and (gobj-alist-vars-bounded k t x)
                (bfr-mode))
           (gobj-alist-vars-bounded k t (gobj-alist-to-param-space x p)))
  :hints (("goal" :use GOBJ-ALIST-VARS-BOUNDED-OF-GOBJ-ALIST-TO-PARAM-SPACE
           :in-theory (disable gobj-alist-vars-bounded-of-gobj-alist-to-param-space))))


(DEFTHM BVAR-DB-ORDERED-OF-GLCP-GENERIC-INTERP-EQUIVS-aig-mode
  (B* (((MV ?VAL ?ERP ?PATHCOND1
            ?INTERP-ST1 ?BVAR-DB1 ?STATE1)
        (GLCP-GENERIC-INTERP-TERM-EQUIVS
         X ALIST CONTEXTS PATHCOND
         CLK CONFIG INTERP-ST BVAR-DB ST))
       (K (NEXT-BVAR$A BVAR-DB)))
    (IMPLIES
     (and (EQUAL P (GLCP-CONFIG->PARAM-BFR CONFIG))
          (GOBJ-ALIST-VARS-BOUNDED K P ALIST))
     (AND
      (IMPLIES
       (AND (BFR-VARS-BOUNDED K P)
            (BVAR-DB-ORDEREDP P BVAR-DB)
            (BVAR-DB-VARS-BOUNDED K P K BVAR-DB)
            (GBC-DB-VARS-BOUNDED
             K P (NTH *IS-CONSTRAINT-DB* INTERP-ST))
            (bfr-mode))
       (BVAR-DB-ORDEREDP t BVAR-DB1)))))
  :hints (("goal" :use ((:instance bvar-db-ordered-of-glcp-generic-interp-equivs
                         (p (glcp-config->param-bfr config))))
           :in-theory (disable bvar-db-ordered-of-glcp-generic-interp-equivs))))

(DEFTHM VARS-BOUNDED-OF-GLCP-GENERIC-INTERP-EQUIVS-aig-mode
  (B* (((MV ?VAL ?ERP ?PATHCOND1 ?INTERP-ST1 ?BVAR-DB1 ?STATE1)
        (GLCP-GENERIC-INTERP-TERM-EQUIVS
         X ALIST CONTEXTS PATHCOND
         CLK CONFIG INTERP-ST BVAR-DB ST)))
    (IMPLIES
     (AND (AND (EQUAL NN (NEXT-BVAR$A BVAR-DB1))
               (EQUAL P (GLCP-CONFIG->PARAM-BFR CONFIG))
               (<= (NEXT-BVAR$A BVAR-DB1) (NFIX K))
               (BFR-VARS-BOUNDED K P)
               (BVAR-DB-VARS-BOUNDED K P (NEXT-BVAR$A BVAR-DB)
                                     BVAR-DB)
               (GBC-DB-VARS-BOUNDED
                K P (NTH *IS-CONSTRAINT-DB* INTERP-ST)))
          (GOBJ-ALIST-VARS-BOUNDED K P ALIST)
          (bfr-mode))
     (AND (GOBJ-VARS-BOUNDED K t VAL)
          (IMPLIES (BFR-CONSTR-VARS-BOUNDED
                    K p (NTH *IS-CONSTRAINT* INTERP-ST))
                   (BFR-CONSTR-VARS-BOUNDED
                    K t (NTH *IS-CONSTRAINT* INTERP-ST1)))
          (BVAR-DB-VARS-BOUNDED K t NN BVAR-DB1)
          (GBC-DB-VARS-BOUNDED
           K t
           (NTH *IS-CONSTRAINT-DB* INTERP-ST1)))))
  :hints (("goal" :use ((:instance vars-bounded-of-glcp-generic-interp-equivs
                         (p (glcp-config->param-bfr config))))
           :in-theory (disable vars-bounded-of-glcp-generic-interp-equivs))))


(defthm glcp-generic-interp-equivs-correct-fix-env
  (b* (((mv val ?er ?new-pathcond ?new-interp-st ?new-bvar-db state)
        (glcp-generic-interp-term-equivs x alist nil pathcond clk config interp-st bvar-db state))
       (p (glcp-config->param-bfr config))
       (fix-bfr-env (bvar-db-fix-env
                     last-bvar first-bvar new-bvar-db t bfr-env var-env)))
    (implies (and (bfr-hyp-eval (nth *is-constraint* interp-st) bfr-env)
                  (bfr-eval p bfr-env)
                  (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                  (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) (cons bfr-env var-env))
                  (equal last-bvar (next-bvar$a new-bvar-db))
                  (equal first-bvar (next-bvar$a bvar-db))
                  ;; (equal pp p)
                  (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                  (equal (w state0) (w state))
                  (not er)
                  (bvar-db-orderedp p bvar-db)
                  (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                  (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                  (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                  (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                  (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                  (bfr-mode)
                  )
             (and (implies (bfr-hyp-eval pathcond bfr-env)
                           (equal (glcp-generic-geval val (cons fix-bfr-env var-env))
                                  (glcp-generic-geval-ev x (glcp-generic-geval-alist alist (cons bfr-env var-env)))))
                  (bfr-hyp-eval (nth *is-constraint* new-interp-st) fix-bfr-env))))
  :hints (("goal" :use ((:instance glcp-generic-interp-correct-equivs
                         (st state)
                         (env (cons (bvar-db-fix-env
                                     last-bvar first-bvar
                                     (mv-nth 4 (glcp-generic-interp-term-equivs x alist nil pathcond clk config interp-st bvar-db state))
                                     t bfr-env var-env)
                                    var-env))
                         (contexts nil)))
           :in-theory (e/d (bdd-mode-or-p-true glcp-interp-accs-ok iff*)
                           (glcp-generic-interp-correct-equivs)))))


(DEFTHM BVAR-DB-ORDERED-OF-GLCP-GENERIC-INTERP-LIST-aig-mode
  (B* (((MV ?VAL ?ERP ?PATHCOND1
            ?INTERP-ST1 ?BVAR-DB1 ?STATE1)
        (GLCP-GENERIC-INTERP-LIST
         X ALIST PATHCOND
         CLK CONFIG INTERP-ST BVAR-DB ST))
       (K (NEXT-BVAR$A BVAR-DB)))
    (IMPLIES
     (and (EQUAL P (GLCP-CONFIG->PARAM-BFR CONFIG))
          (GOBJ-ALIST-VARS-BOUNDED K P ALIST))
     (AND
      (IMPLIES
       (AND (BFR-VARS-BOUNDED K P)
            (BVAR-DB-ORDEREDP P BVAR-DB)
            (BVAR-DB-VARS-BOUNDED K P K BVAR-DB)
            (GBC-DB-VARS-BOUNDED
             K P (NTH *IS-CONSTRAINT-DB* INTERP-ST))
            (bfr-mode))
       (BVAR-DB-ORDEREDP t BVAR-DB1)))))
  :hints (("goal" :use ((:instance bvar-db-ordered-of-glcp-generic-interp-list
                         (p (glcp-config->param-bfr config))))
           :in-theory (disable bvar-db-ordered-of-glcp-generic-interp-list))))

(DEFTHM VARS-BOUNDED-OF-GLCP-GENERIC-INTERP-LIST-aig-mode
  (B* (((MV ?VAL ?ERP ?PATHCOND1 ?INTERP-ST1 ?BVAR-DB1 ?STATE1)
        (GLCP-GENERIC-INTERP-LIST
         X ALIST PATHCOND
         CLK CONFIG INTERP-ST BVAR-DB ST)))
    (IMPLIES
     (AND (AND (EQUAL NN (NEXT-BVAR$A BVAR-DB1))
               (EQUAL P (GLCP-CONFIG->PARAM-BFR CONFIG))
               (<= (NEXT-BVAR$A BVAR-DB1) (NFIX K))
               (BFR-VARS-BOUNDED K P)
               (BVAR-DB-VARS-BOUNDED K P (NEXT-BVAR$A BVAR-DB)
                                     BVAR-DB)
               (GBC-DB-VARS-BOUNDED
                K P (NTH *IS-CONSTRAINT-DB* INTERP-ST)))
          (GOBJ-ALIST-VARS-BOUNDED K P ALIST)
          (bfr-mode))
     (AND (GOBJ-list-VARS-BOUNDED K t VAL)
          (IMPLIES (BFR-CONSTR-VARS-BOUNDED
                    K p (NTH *IS-CONSTRAINT* INTERP-ST))
                   (BFR-CONSTR-VARS-BOUNDED
                    K t (NTH *IS-CONSTRAINT* INTERP-ST1)))
          (BVAR-DB-VARS-BOUNDED K t NN BVAR-DB1)
          (GBC-DB-VARS-BOUNDED
           K t
           (NTH *IS-CONSTRAINT-DB* INTERP-ST1)))))
  :hints (("goal" :use ((:instance vars-bounded-of-glcp-generic-interp-list
                         (p (glcp-config->param-bfr config))))
           :in-theory (disable vars-bounded-of-glcp-generic-interp-list))))


(defthm glcp-generic-interp-correct-list-fix-env
  (b* (((mv ?vals ?er ?new-pathcond ?new-interp-st ?new-bvar-db ?new-state)
        (glcp-generic-interp-list
         x alist pathcond clk config interp-st bvar-db st))
       (p (glcp-config->param-bfr config))
       (fix-bfr-env (bvar-db-fix-env
                     last-bvar first-bvar new-bvar-db t bfr-env var-env)))
    (implies
     (and
      (bfr-hyp-eval (nth *is-constraint* interp-st) fix-bfr-env)
      (bfr-eval p bfr-env)
      (glcp-generic-geval-ev-theoremp
       (conjoin-clauses
        (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
      (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) (cons bfr-env var-env))
      (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
      (equal (w state0) (w st))
      (equal last-bvar (next-bvar$a new-bvar-db))
      (equal first-bvar (next-bvar$a bvar-db))
      (not er)
      (bvar-db-orderedp p bvar-db)
      (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
      (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
      (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
      (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
      (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
      (bfr-mode))
     (and
      (implies
       (bfr-hyp-eval pathcond bfr-env)
       (equal (glcp-generic-geval-list vals (cons fix-bfr-env var-env))
              (glcp-generic-geval-ev-lst
               x
               (glcp-generic-geval-alist alist (cons fix-bfr-env var-env)))))
      (bfr-hyp-eval (nth *is-constraint* new-interp-st) fix-bfr-env))))
  :hints (("goal" :use ((:instance glcp-generic-interp-correct-list
                         (st st)
                         (env (cons (bvar-db-fix-env
                                     last-bvar first-bvar
                                     (mv-nth 4 (glcp-generic-interp-list x alist pathcond clk config interp-st bvar-db st))
                                     t bfr-env var-env)
                                    var-env))))
           :in-theory (e/d (bdd-mode-or-p-true glcp-interp-accs-ok iff*)
                           (glcp-generic-interp-correct-list)))))


(defthm alistp-of-glcp-generic-geval-alist
  (alistp (glcp-generic-geval-alist x env))
  :hints(("Goal" :in-theory (enable glcp-generic-geval-alist))))

(defsection true-listp-of-glcp-generic-interp-list
  (local (defun-sk true-listp-of-glcp-generic-interp-list-sk (x)
           (forall (alist pathcond clk config interp-st bvar-db st)
                   (true-listp (mv-nth 0 (glcp-generic-interp-list x alist pathcond clk config interp-st bvar-db st))))
           :rewrite :direct))
  (local (in-theory (disable true-listp-of-glcp-generic-interp-list-sk)))
  (local (defthm true-listp-of-glcp-generic-interp-list-lemma
           (true-listp-of-glcp-generic-interp-list-sk x)
           :hints (("goal" :induct (len x))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause))
                                   (:free (alist pathcond clk config interp-st bvar-db st)
                                    (glcp-generic-interp-list x alist pathcond clk config interp-st bvar-db st))))))))

  (defthm true-listp-of-glcp-generic-interp-list
    (true-listp (mv-nth 0 (glcp-generic-interp-list x alist pathcond clk config interp-st bvar-db state)))
    :rule-classes :type-prescription))


                  
  
(defthm glcp-generic-interp-accs-ok-equivs-forward-bfr-mode
  (b* (((mv & & & new-interp-st new-bvar-db)
        (glcp-generic-interp-term-equivs x alist contexts pathcond clk config interp-st bvar-db st)))
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (bfr-mode))
             (glcp-interp-accs-ok interp-st bvar-db config1 env)))
  :hints (("goal" :use GLCP-GENERIC-INTERP-ACCS-OK-EQUIVS
           :in-theory (disable GLCP-GENERIC-INTERP-ACCS-OK-EQUIVS)))
  :rule-classes :forward-chaining)

(defthm glcp-generic-interp-accs-ok-list-forward-bfr-mode
  (b* (((mv & & & new-interp-st new-bvar-db)
        (glcp-generic-interp-list x alist pathcond clk config interp-st bvar-db st)))
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (bfr-mode))
             (glcp-interp-accs-ok interp-st bvar-db config1 env)))
  :hints (("goal" :use GLCP-GENERIC-INTERP-ACCS-OK-LIST
           :in-theory (disable GLCP-GENERIC-INTERP-ACCS-OK-LIST)))
  :rule-classes :forward-chaining)


(defthm true-listp-of-glcp-generic-geval-ev-lst
  (true-listp (Glcp-generic-geval-ev-lst x a))
  :hints (("goal" :induct (len x))))

(verify-guards glmc-generic-ev-bindinglist)

(defsection glmc-generic-interp-bindinglist
  (local (in-theory (enable (:i glmc-generic-interp-bindinglist))))
  (local (std::set-define-current-function glmc-generic-interp-bindinglist))
  (local (in-theory (disable pseudo-term-listp pseudo-termp)))

  (std::defret interp-defs-of-<fn>
    (b* (((glcp-config config)))
      (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp config.overrides)
                    (acl2::bindinglist-p x))
               (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st))))
    :hints (("goal" :induct <call> :expand (<call>))))

  (local (defthm glcp-generic-geval-alist-of-append
           (equal (glcp-generic-geval-alist (append a b) env)
                  (append (glcp-generic-geval-alist a env)
                          (glcp-generic-geval-alist b env)))
           :hints(("Goal" :in-theory (enable glcp-generic-geval-alist)))))

  (local (defthm glcp-generic-geval-alist-of-pairlis$
           (equal (glcp-generic-geval-alist (pairlis$ a b) env)
                  (pairlis$ a
                            (glcp-generic-geval-list b env)))
           :hints(("Goal" :in-theory (enable glcp-generic-geval-alist pairlis$
                                             glcp-generic-geval-list)))))

  (std::defret glcp-interp-accs-ok-of-<fn>
    (implies (not (glcp-interp-accs-ok interp-st bvar-db config env))
             (not (glcp-interp-accs-ok new-interp-st new-bvar-db config env)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret glcp-interp-accs-ok-of-<fn>-fwd
    (implies (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
             (glcp-interp-accs-ok interp-st bvar-db config env))
    :rule-classes :forward-chaining)

  (std::defret glcp-interp-accs-ok-of-<fn>-bfr-mode
    (implies (and (not (glcp-interp-accs-ok interp-st bvar-db config1 env))
                  (bfr-mode))
             (not (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret glcp-interp-accs-ok-of-<fn>-bfr-mode-fwd
    (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config1 env)
                  (bfr-mode))
             (glcp-interp-accs-ok interp-st bvar-db config1 env))
    :rule-classes :forward-chaining)

  (std::defret alistp-new-alist-of-<fn>
    (implies (alistp alist)
             (alistp new-alist))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret <fn>-correct
    (b* (((glcp-config config))
         (p (glcp-config->param-bfr config)))
      (implies (and (bfr-hyp-eval (nth *is-constraint* interp-st) (car env))
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
                    (bdd-mode-or-p-true p (car env)))
               (and (implies (and (not err)
                                  (bfr-hyp-eval pathcond (car env)))
                             (equal (glcp-generic-geval-alist new-alist env)
                                    (glmc-generic-ev-bindinglist x
                                                                 (glcp-generic-geval-alist alist env))))
                    (bfr-hyp-eval (nth *is-constraint* new-interp-st) (car env))
                    (implies (equal err :unreachable)
                             (not (bfr-hyp-eval pathcond (car env)))))))
    :hints (("goal" :induct <call> :expand (<call>))
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (glmc-generic-ev-bindinglist x a)))))))

  (std::defret w-state-of-<fn>
    (equal (w new-state) (w state))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret pathcond-preserved-of-<fn>
    (equal new-pathcond (bfr-hyp-fix pathcond))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret state-p1-preserved-of-<fn>
    (implies (state-p1 state)
             (state-p1 new-state))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret base-bvar-preserved-of-<fn>
    (equal (base-bvar$a new-bvar-db)
           (base-bvar$a bvar-db))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret next-bvar-of-<fn>
    (>= (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))
    :hints (("goal" :induct <call> :expand (<call>)))
    :rule-classes :linear)

  (std::defret get-bvar->term-of-<fn>
    (implies (and (<= (base-bvar$a bvar-db) (nfix n))
                  (< (nfix n) (next-bvar$a bvar-db)))
             (equal (get-bvar->term$a n new-bvar-db)
                    (get-bvar->term$a n bvar-db)))
    :hints (("goal" :induct <call> :expand (<call>))))


  (defthm gobj-alist-vars-bounded-of-append
    (implies (and (gobj-alist-vars-bounded k p a)
                  (gobj-alist-vars-bounded k p b))
             (gobj-alist-vars-bounded k p (append a b)))
    :hints(("Goal" :in-theory (enable gobj-alist-vars-bounded))))

  (std::defret <fn>-vars-bounded
    (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                  (equal p (glcp-config->param-bfr config))
                  (bfr-vars-bounded k p)
                  (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                  (equal nn (next-bvar$a new-bvar-db))
                  (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                  (gobj-alist-vars-bounded k p alist))
             (and (gobj-alist-vars-bounded k p new-alist)
                  (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                           (bfr-constr-vars-bounded k p (nth *is-constraint* new-interp-st)))
                  (bvar-db-vars-bounded k p nn new-bvar-db)
                  (gbc-db-vars-bounded k p (nth *is-constraint-db* new-interp-st))))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret <fn>-vars-bounded-aig-mode
    (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                  (equal p (glcp-config->param-bfr config))
                  (bfr-vars-bounded k p)
                  (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                  (equal nn (next-bvar$a new-bvar-db))
                  (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                  (gobj-alist-vars-bounded k p alist)
                  (bfr-mode))
             (and (gobj-alist-vars-bounded k t new-alist)
                  (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                           (bfr-constr-vars-bounded k t (nth *is-constraint* new-interp-st)))
                  (bvar-db-vars-bounded k t nn new-bvar-db)
                  (gbc-db-vars-bounded k t (nth *is-constraint-db* new-interp-st))))
    :hints (("goal" :use ((:instance glmc-generic-interp-bindinglist-vars-bounded))
             :in-theory (disable glmc-generic-interp-bindinglist-vars-bounded))))

  (std::defret <fn>-bvar-db-ordered
    (b* ((k (next-bvar$a bvar-db)))
      (implies (and (equal p (glcp-config->param-bfr config))
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k p alist))
               (bvar-db-orderedp p new-bvar-db)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret <fn>-bvar-db-ordered-aig-mode
    (b* ((k (next-bvar$a bvar-db)))
      (implies (and (equal p (glcp-config->param-bfr config))
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k p alist)
                    (bfr-mode))
               (bvar-db-orderedp t new-bvar-db)))
    :hints (("Goal" :use ((:instance glmc-generic-interp-bindinglist-bvar-db-ordered))
             :in-theory (disable glmc-generic-interp-bindinglist-bvar-db-ordered)
             :do-not-induct t)))

  (std::defret interp-st-obligs-extension-p-of-<fn>
    (interp-st-obligs-extension-p new-interp-st interp-st)
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret bvar-db-extension-p-of-<fn>
    (bvar-db-extension-p new-bvar-db bvar-db)
    :hints (("goal" :induct <call> :expand (<call>))))

  (verify-guards glmc-generic-interp-bindinglist))


(defsection glmc-generic-interp-nonhyps
  (local (in-theory (enable glmc-generic-interp-nonhyps)))
  (local (std::set-define-current-function glmc-generic-interp-nonhyps))

  (local (in-theory (disable gobj-to-param-space
                             gobj-alist-to-param-space
                             equal-of-booleans-rewrite)))

  (verify-guards glmc-generic-interp-nonhyps)
;; (define glmc-generic-interp-nonhyps ((config glmc-config-p)
;;                                      hyp-bfr
;;                                      interp-st
;;                                      bvar-db
;;                                      hyp-bvar-db
;;                                      state)
;;   :guard (b* (((glmc-config+ config)))
;;            (and (acl2::interp-defs-alistp config.overrides)
;;                 (acl2::interp-defs-alistp (is-obligs interp-st))))

;;   :returns (mv initst-bfr constr-bfr prop-bfr st-hyp-next-bfr nextst er new-interp-st new-bvar-db new-state)
;;   (b* (((glmc-config+ config) (glmc-config-update-param hyp-bfr config))
;;        ((acl2::local-stobjs pathcond)
;;         (mv initst-bfr constr-bfr prop-bfr st-hyp-next-bfr nextst-obj er pathcond interp-st bvar-db state))

;;        ((mv contra pathcond interp-st bvar-db)
;;         (glcp-prepare-param-inputs hyp-bfr pathcond interp-st hyp-bvar-db bvar-db))

;;        ((when contra)
;;         (mv nil nil nil nil nil
;;             "Contradiction in constraints or hypothesis"
;;             pathcond interp-st bvar-db state))

;;        (alist (gobj-alist-to-param-space (shape-specs-to-interp-al config.shape-spec-alist) hyp-bfr))

;;        ((mv nextst er pathcond interp-st bvar-db state)
;;         (glcp-generic-interp-term-equivs config.nextst alist nil pathcond config.concl-clk config.glcp-config interp-st bvar-db state))
;;        ((when er)
;;         (mv nil nil nil nil nil er pathcond interp-st bvar-db state))
       
;;        (st-alist (alist-extract (list config.st-var) alist))
;;        (nextst-alist (list (cons config.st-var nextst)))

;;        (tuples (list (make-hyp-tuple :name "initst" :term config.initstp :alist st-alist)
;;                      (make-hyp-tuple :name "constraint" :term config.constr :alist alist)
;;                      (make-hyp-tuple :name "prop" :term config.prop :alist alist)
;;                      (make-hyp-tuple :name "st-hyp-next" :term config.st-hyp :alist nextst-alist)))
       
;;        ((mv (acl2::nths initst-bfr constr-bfr prop-bfr st-hyp-next-bfr) er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-hyp-tuples tuples pathcond config.glcp-config interp-st bvar-db state))
;;        ((when er)
;;         (mv nil nil nil nil nil er pathcond interp-st bvar-db state)))

;;     (mv initst-bfr constr-bfr prop-bfr st-hyp-next-bfr nextst nil pathcond interp-st bvar-db state))
;;   ///

  (defthm glmc-generic-interp-nonhyps-normalize
    (implies (syntaxp (not (equal bvar-db ''nil)))
             (equal (glmc-generic-interp-nonhyps config hyp-bfr interp-st bvar-db hyp-bvar-db state)
                    (glmc-generic-interp-nonhyps config hyp-bfr interp-st nil hyp-bvar-db state))))

  (std::defret interp-defs-of-glmc-generic-interp-nonhyps
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config)))
      (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp config1.overrides)
                    (glmc-config-p config))
               (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st)))))


  (std::defret glmc-generic-interp-nonhyps-nextst-correct
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config1.shape-spec-alist)
                                          env)))
      (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db nil env)
                    (equal bfr-env (car env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    ;; (assoc config1.st-var config1.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode)
                    (bfr-eval hyp-bfr bfr-env))
               (equal (glcp-generic-geval nextst env)
                      (glcp-generic-geval-ev config1.nextst
                                             (glmc-generic-ev-bindinglist
                                              config1.bindings alist)))))
    :hints(("Goal" :in-theory (enable bfr-unparam-env genv-unparam))))


  (local (in-theory (enable default-car default-cdr)))
  ;; (local (defthm bfr-eval-of-car-env-hack
  ;;          (implies (and (bfr-eval hyp (car env))
  ;;                        (not (consp env)))
  ;;                   (bfr-eval hyp nil))))

  (std::defret glmc-generic-interp-nonhyps-st-bfrs-correct
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config1.shape-spec-alist)
                                          env))
         ;; (st-alist (acl2::fal-extract (list config1.st-var) alist))
         )
      (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db nil env)
                    (equal bfr-env (car env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    ;; (assoc config1.st-var config1.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode)
                    (bfr-eval hyp-bfr bfr-env))
               (b* ((new-alist (glmc-generic-ev-bindinglist
                                              config1.bindings alist)))
                 (and (iff (bfr-eval initst-bfr bfr-env)
                           (glcp-generic-geval-ev config1.initstp new-alist))
                      (iff (bfr-eval constr-bfr bfr-env)
                           (glcp-generic-geval-ev config1.constr new-alist))
                      (iff (bfr-eval prop-bfr bfr-env)
                           (glcp-generic-geval-ev config1.prop new-alist))
                      (iff (bfr-eval st-hyp-next-bfr bfr-env)
                           (glcp-generic-geval-ev config1.st-hyp
                                                  (list (cons config1.st-var
                                                              (glcp-generic-geval-ev config1.nextst new-alist)))))))))

    :hints (("goal" :expand ((glcp-generic-geval-alist nil env))
             :in-theory (enable bfr-unparam-env genv-unparam
                                ;; glcp-generic-geval-alist-normalize-cons-car-cdr-env
                                ))))

  
  (local (defthm GLCP-GENERIC-INTERP-ACCS-OK-FINAL-IMPLIES-START-EQUIVS-aig-mode
           (B* (((MV ?VAL ?ERP ?PATHCOND1
                     ?INTERP-ST1 ?BVAR-DB1 ?STATE1)
                 (GLCP-GENERIC-INTERP-TERM-EQUIVS
                  X ALIST CONTEXTS PATHCOND
                  CLK CONFIG INTERP-ST BVAR-DB ST)))
             (IMPLIES
              (and (GLCP-INTERP-ACCS-OK INTERP-ST1 BVAR-DB1 nil ENV)
                   (bfr-mode))
              (AND (GLCP-INTERP-ACCS-OK INTERP-ST BVAR-DB nil ENV))))
           :hints (("goal" :use glcp-generic-interp-accs-ok-final-implies-start-equivs
                    :in-theory (disable glcp-generic-interp-accs-ok-final-implies-start-equivs)))
           :rule-classes :forward-chaining))


  (std::defret glmc-generic-interp-nonhyps-constraint-correct
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config)))
      (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db nil env)
                    (equal bfr-env (car env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-eval hyp-bfr bfr-env)
                    (bfr-mode)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) bfr-env)))
    :hints(("Goal" :in-theory (enable  bfr-unparam-env genv-unparam))))

  (std::defret glmc-generic-interp-nonhyps-accs-ok
      (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db nil env)
                    (bfr-mode)
                    (bfr-eval hyp-bfr (car env)))
               (glcp-interp-accs-ok interp-st hyp-bvar-db nil env))
    :hints(("Goal" :in-theory (enable genv-unparam)))
    :rule-classes :forward-chaining)
  
  (std::defret w-state-preserved-of-glmc-generic-interp-nonhyps
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glmc-generic-interp-nonhyps
      (implies (state-p1 state) (state-p1 new-state)))

  (std::defret base-bvar-of-glmc-generic-interp-nonhyps
    (equal (base-bvar$a new-bvar-db) (base-bvar$a hyp-bvar-db)))

  (std::defret next-bvar-of-glmc-generic-interp-nonhyps
    (>= (next-bvar$a new-bvar-db) (next-bvar$a hyp-bvar-db))
    :rule-classes :linear)

  (std::defret get-bvar->term-of-glcp-generic-run-nextst-and-prop
      (implies (and (<= (base-bvar$a hyp-bvar-db) (nfix n))
                    (< (nfix n) (next-bvar$a hyp-bvar-db)))
               (equal (get-bvar->term$a n new-bvar-db)
                      (gobj-to-param-space (get-bvar->term$a n hyp-bvar-db)
                                           hyp-bfr))))

  (std::defret glmc-generic-interp-nonhyps-vars-bounded
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config)))
      (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bvar-db-vars-bounded k t (next-bvar$a hyp-bvar-db) hyp-bvar-db)
                    (bfr-vars-bounded k hyp-bfr)
                    (equal nn (next-bvar$a new-bvar-db))
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
                    (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config1.shape-spec-alist))
                        (nfix k)))
               (and (pbfr-vars-bounded k hyp-bfr initst-bfr)
                    (pbfr-vars-bounded k hyp-bfr constr-bfr)
                    (pbfr-vars-bounded k hyp-bfr prop-bfr)
                    (pbfr-vars-bounded k hyp-bfr st-hyp-next-bfr)
                    (gobj-vars-bounded k hyp-bfr nextst)
                    (implies (bfr-constr-vars-bounded k t (nth *is-constraint* interp-st))
                             (bfr-constr-vars-bounded k hyp-bfr (nth *is-constraint* new-interp-st)))
                    (bvar-db-vars-bounded k hyp-bfr nn new-bvar-db)
                    (gbc-db-vars-bounded k hyp-bfr (nth *is-constraint-db* new-interp-st))))))

  (std::defret glmc-generic-interp-nonhyps-vars-bounded-aig-mode
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config)))
      (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bvar-db-vars-bounded k t (next-bvar$a hyp-bvar-db) hyp-bvar-db)
                    (bfr-vars-bounded k hyp-bfr)
                    (equal nn (next-bvar$a new-bvar-db))
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
                    (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config1.shape-spec-alist))
                        (nfix k))
                    (bfr-mode))
               (and (pbfr-vars-bounded k t initst-bfr)
                    (pbfr-vars-bounded k t constr-bfr)
                    (pbfr-vars-bounded k t prop-bfr)
                    (pbfr-vars-bounded k t st-hyp-next-bfr)
                    (gobj-vars-bounded k t nextst))))
    :hints (("goal" :use ((:instance glmc-generic-interp-nonhyps-vars-bounded))
             :in-theory (disable glmc-generic-interp-nonhyps-vars-bounded
                                 glmc-generic-interp-nonhyps))))

  (std::defret glmc-generic-interp-nonhyps-bvar-db-ordered
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
         (k (next-bvar$a hyp-bvar-db)))
      (implies (and (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config1.shape-spec-alist))
                        (nfix k))
                    (bfr-vars-bounded k hyp-bfr)
                    (bvar-db-orderedp t hyp-bvar-db)
                    (bvar-db-vars-bounded k t k hyp-bvar-db)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st)))
               (bvar-db-orderedp hyp-bfr new-bvar-db))))

  (std::defret glmc-generic-interp-nonhyps-bvar-db-ordered-aig-mode
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
         (k (next-bvar$a hyp-bvar-db)))
      (implies (and (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config1.shape-spec-alist))
                        (nfix k))
                    (bfr-vars-bounded k hyp-bfr)
                    (bvar-db-orderedp t hyp-bvar-db)
                    (bvar-db-vars-bounded k t k hyp-bvar-db)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st))
                    (bfr-mode))
               (bvar-db-orderedp t new-bvar-db)))
    :hints (("Goal" :use ((:instance glmc-generic-interp-nonhyps-bvar-db-ordered))
             :in-theory (disable glmc-generic-interp-nonhyps-bvar-db-ordered
                                 glmc-generic-interp-nonhyps))))
  
  (local (acl2::use-trivial-ancestors-check))

  (std::defret interp-st-obligs-extension-p-of-glcp-generic-interp-nonhyps
    (interp-st-obligs-extension-p new-interp-st interp-st))
                    
                         
                    

  ;; (std::defret bvar-db-env-ok-of-glcp-generic-interp-nonhyps-reduce
  ;;   (implies (and (glcp-generic-bvar-db-env-ok hyp-bvar-db t (next-bvar$a hyp-bvar-db) 
  ;;                                              env)
  ;;                 (bfr-mode))
  ;;            (glcp-generic-bvar-db-env-ok new-bvar-db t (next-bvar$a hyp-bvar-db) env))
  ;;   :hints(("Goal" :in-theory (enable genv-unparam)))
  ;;   :otf-flg t)

  (std::defret glmc-generic-interp-nonhyps-bvar-db-extends
    (bvar-db-extension-p new-bvar-db
                         (parametrize-bvar-db hyp-bfr hyp-bvar-db nil))
    :hints(("Goal" :in-theory (enable glcp-parametrize-accs))))

  (local (defthm bvar-db-fix-env-base
           (equal (Bvar-db-fix-env n n bvar-db p bfr-env var-env)
                  bfr-env)
           :hints(("Goal" :in-theory (enable bvar-db-fix-env)))))

  
  (std::defret env-ok-of-glmc-generic-interp-nonhyps
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
         (fix-bfr-env (bvar-db-fix-env last-bvar
                                       base-bvar
                                       new-bvar-db t bfr-env var-env))
         (k (next-bvar$a hyp-bvar-db)))
      (implies (and (equal last-bvar (next-bvar$a new-bvar-db))
                    (equal base-bvar (next-bvar$a hyp-bvar-db))
                    (pbfr-vars-bounded (next-bvar$a hyp-bvar-db) t hyp-bfr)
                    (bfr-mode)
                    (bfr-eval hyp-bfr bfr-env)
                    (glcp-generic-bvar-db-env-ok
                     hyp-bvar-db t (next-bvar$a hyp-bvar-db) (cons bfr-env var-env))
                    (not er)
                    (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config1.shape-spec-alist))
                        (nfix k))
                    (pbfr-vars-bounded k t hyp-bfr)
                    (bvar-db-orderedp t hyp-bvar-db)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st)))
               (glcp-generic-bvar-db-env-ok
                new-bvar-db t (next-bvar$a new-bvar-db)
                (cons fix-bfr-env var-env)))))

  ;; (std::defret env-ok-of-glmc-generic-interp-nonhyps-hyp-bound
  ;;   (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
  ;;        (fix-bfr-env (bvar-db-fix-env last-bvar
  ;;                                      base-bvar
  ;;                                      new-bvar-db t bfr-env var-env))
  ;;        (k (next-bvar$a hyp-bvar-db)))
  ;;     (implies (and (equal last-bvar (next-bvar$a new-bvar-db))
  ;;                   (equal base-bvar (next-bvar$a hyp-bvar-db))
  ;;                   (pbfr-vars-bounded (next-bvar$a hyp-bvar-db) t hyp-bfr)
  ;;                   (bfr-mode)
  ;;                   (glcp-generic-bvar-db-env-ok
  ;;                    hyp-bvar-db t (next-bvar$a hyp-bvar-db) (cons bfr-env var-env))
  ;;                   (not er)
  ;;                   (<= (shape-spec-max-bvar-list
  ;;                        (shape-spec-bindings->sspecs config1.shape-spec-alist))
  ;;                       (nfix k))
  ;;                   (pbfr-vars-bounded k t hyp-bfr)
  ;;                   (bvar-db-orderedp t hyp-bvar-db)
  ;;                   (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st)))
  ;;              (glcp-generic-bvar-db-env-ok
  ;;               new-bvar-db t (next-bvar$a hyp-bvar-db)
  ;;               (cons fix-bfr-env var-env)))))

  
  (std::defret glmc-generic-interp-nonhyps-nextst-correct-fix-env
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config1.shape-spec-alist)
                                          (cons bfr-env var-env)))
         (fix-bfr-env (bvar-db-fix-env last-bvar
                                       base-bvar
                                       new-bvar-db t bfr-env var-env))
         (k (next-bvar$a hyp-bvar-db)))
      (implies (and (equal last-bvar (next-bvar$a new-bvar-db))
                    (equal base-bvar (next-bvar$a hyp-bvar-db))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok
                     hyp-bvar-db t (next-bvar$a hyp-bvar-db) (cons bfr-env var-env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-constr-vars-bounded (next-bvar$a hyp-bvar-db) t (nth *is-constraint* interp-st))
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    ;; (assoc config1.st-var config1.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode)
                    (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config1.shape-spec-alist))
                        (nfix k))
                    (bfr-eval hyp-bfr bfr-env)
                    (pbfr-vars-bounded k t hyp-bfr)
                    (bvar-db-orderedp t hyp-bvar-db)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st)))
               (equal (glcp-generic-geval nextst (cons fix-bfr-env var-env))
                      (glcp-generic-geval-ev config1.nextst
                                             (glmc-generic-ev-bindinglist
                                              config1.bindings alist)))))
    :hints (("goal" :in-theory (e/d (glcp-interp-accs-ok)
                                    (glmc-generic-interp-nonhyps
                                     glmc-generic-interp-nonhyps-nextst-correct))
             :use ((:instance glmc-generic-interp-nonhyps-nextst-correct
                    (bfr-env (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                                (next-bvar$a hyp-bvar-db)
                                                new-bvar-db t bfr-env var-env))
                    (env (cons (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                                  (next-bvar$a hyp-bvar-db)
                                                  new-bvar-db t bfr-env var-env)
                               var-env)))))))

  (std::defret glmc-generic-interp-nonhyps-st-bfrs-correct-fix-env
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config1.shape-spec-alist)
                                          (cons bfr-env var-env)))
         (fix-bfr-env (bvar-db-fix-env last-bvar
                                       base-bvar
                                       new-bvar-db t bfr-env var-env))
         (k (next-bvar$a hyp-bvar-db)))
      (implies (and (equal last-bvar (next-bvar$a new-bvar-db))
                    (equal base-bvar (next-bvar$a hyp-bvar-db))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok
                     hyp-bvar-db t (next-bvar$a hyp-bvar-db) (cons bfr-env var-env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-constr-vars-bounded (next-bvar$a hyp-bvar-db) t (nth *is-constraint* interp-st))
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    ;; (assoc config1.st-var config1.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode)
                    (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config1.shape-spec-alist))
                        (nfix k))
                    (bfr-eval hyp-bfr bfr-env)
                    (pbfr-vars-bounded k t hyp-bfr)
                    (bvar-db-orderedp t hyp-bvar-db)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st)))
               (b* ((new-alist (glmc-generic-ev-bindinglist config1.bindings alist)))
                 (and (iff (bfr-eval initst-bfr fix-bfr-env)
                           (glcp-generic-geval-ev config1.initstp new-alist))
                      (iff (bfr-eval constr-bfr fix-bfr-env)
                           (glcp-generic-geval-ev config1.constr new-alist))
                      (iff (bfr-eval prop-bfr fix-bfr-env)
                           (glcp-generic-geval-ev config1.prop new-alist))
                      (iff (bfr-eval st-hyp-next-bfr fix-bfr-env)
                           (glcp-generic-geval-ev config1.st-hyp
                                                  (list (cons config1.st-var
                                                              (glcp-generic-geval-ev config1.nextst new-alist)))))))))
    :hints (("goal" :in-theory (e/d (glcp-interp-accs-ok)
                                    (glmc-generic-interp-nonhyps
                                     glmc-generic-interp-nonhyps-st-bfrs-correct))
             :use ((:instance glmc-generic-interp-nonhyps-st-bfrs-correct
                    (bfr-env (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                                (next-bvar$a hyp-bvar-db)
                                                new-bvar-db t bfr-env var-env))
                    (env (cons (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                                  (next-bvar$a hyp-bvar-db)
                                                  new-bvar-db t bfr-env var-env)
                               var-env)))))))

  (std::defret glmc-generic-interp-nonhyps-constraint-correct-fix-env
    (b* (((glmc-config+ config1) (glmc-config-update-param hyp-bfr config))
         (fix-bfr-env (bvar-db-fix-env last-bvar
                                       base-bvar
                                       new-bvar-db t bfr-env var-env))
         (k (next-bvar$a hyp-bvar-db)))
      (implies (and (equal last-bvar (next-bvar$a new-bvar-db))
                    (equal base-bvar (next-bvar$a hyp-bvar-db))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok
                     hyp-bvar-db t (next-bvar$a hyp-bvar-db) (cons bfr-env var-env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-constr-vars-bounded (next-bvar$a hyp-bvar-db) t (nth *is-constraint* interp-st))
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    ;; (assoc config1.st-var config1.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode)
                    (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config1.shape-spec-alist))
                        (nfix k))
                    (bfr-eval hyp-bfr bfr-env)
                    (pbfr-vars-bounded k t hyp-bfr)
                    (bvar-db-orderedp t hyp-bvar-db)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* interp-st)))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) fix-bfr-env)))
    :hints (("goal" :in-theory (e/d (glcp-interp-accs-ok)
                                    (glmc-generic-interp-nonhyps
                                     glmc-generic-interp-nonhyps-constraint-correct))
             :use ((:instance glmc-generic-interp-nonhyps-constraint-correct
                    (bfr-env (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                                (next-bvar$a hyp-bvar-db)
                                                new-bvar-db t bfr-env var-env))
                    (env (cons (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                                  (next-bvar$a hyp-bvar-db)
                                                  new-bvar-db t bfr-env var-env)
                               var-env))))))))

(defthm glcp-generic-geval-alist-bfr-env-equiv-congruence
  (implies (bfr-env-equiv bfr-env1 bfr-env2)
           (equal (glcp-generic-geval-alist x (cons bfr-env1 var-env))
                  (glcp-generic-geval-alist x (cons bfr-env2 var-env))))
  :hints(("Goal" :in-theory (enable glcp-generic-geval-alist)))
  :rule-classes :congruence)

(defthm glcp-generic-bvar-db-env-ok-bfr-env-equiv-congruence
  (implies (bfr-env-equiv bfr-env1 bfr-env2)
           (equal (glcp-generic-bvar-db-env-ok bvar-db p bound (cons bfr-env1 var-env))
                  (glcp-generic-bvar-db-env-ok bvar-db p bound (cons bfr-env2 var-env))))
  :hints (("goal" :cases ((glcp-generic-bvar-db-env-ok bvar-db p bound (cons bfr-env1 var-env))))
          (and stable-under-simplificationp
               (b* ((expand-lit (assoc 'glcp-generic-bvar-db-env-ok clause))
                    (expand-bfr-env (nth 1 (nth 4 expand-lit)))
                    (other-bfr-env (if (eq expand-bfr-env 'bfr-env1) 'bfr-env2 'bfr-env1)))
               `(:expand (,expand-lit)
                 :use ((:instance glcp-generic-bvar-db-env-ok-necc
                        (n (glcp-generic-bvar-db-env-ok-witness . ,(cdr expand-lit)))
                        (env (cons ,other-bfr-env var-env))))
                 :in-theory (disable glcp-generic-bvar-db-env-ok-necc)))))
  :rule-classes :congruence)


;; (define glmc-generic-interp-nonhyps-env ((env consp)
;;                                          hyp-bfr
;;                                          (config glmc-config-p)
;;                                          interp-st
;;                                          hyp-bvar-db
;;                                          state)
;;   :non-executable t
;;   :verify-guards nil
;;   :returns (new-env consp :rule-classes :type-prescription)
;;   (b* (((glmc-config+ config))
;;        ((mv & & & & & & new-bvar-db &)
;;         (glmc-generic-interp-nonhyps config hyp-bfr interp-st nil hyp-bvar-db state))

;;        ;; (env-term (shape-spec-list-env-term (shape-spec-bindings->sspecs config.shape-spec-alist)
;;        ;;                                     (alist-keys config.shape-spec-alist)))
;;        ;; (env1 (glcp-generic-geval-ev env-term alist))
;;        (bfr-env (bvar-db-fix-env (next-bvar new-bvar-db)
;;                                  (next-bvar hyp-bvar-db)
;;                                  new-bvar-db
;;                                  hyp-bfr
;;                                  (bfr-param-env hyp-bfr (car env))
;;                                  (cdr env))))
;;     (cons bfr-env (cdr env)))
;;   ///
;;   (local (in-theory (disable bvar-db-fix-env alistp
;;                              equal-of-booleans-rewrite)))

  
;;   (local (defthm bvar-db-fix-env-base
;;            (equal (Bvar-db-fix-env n n bvar-db p bfr-env var-env)
;;                   bfr-env)
;;            :hints(("Goal" :in-theory (enable bvar-db-fix-env)))))

;;   ;; (local (defthm glcp-generic-bvar-db-env-ok-resolve-atom-dumb-thing
;;   ;;          (implies (and (glcp-generic-bvar-db-env-ok bvar-db p n env)
;;   ;;                        (atom env))
;;   ;;                   (glcp-generic-bvar-db-env-ok bvar-db p n '(nil)))))
  
;;   (std::defret glmc-generic-interp-nonhyps-env-bvar-db-env-ok
;;     ;; (implies (bvar-db-orderedp t new-bvar-db)
;;     (b* (((mv & & & & & & new-bvar-db &)
;;           (glmc-generic-interp-nonhyps config hyp-bfr interp-st bvar-db hyp-bvar-db state))
;;          ((glmc-config+ config1) config))
;;       (implies (and (glcp-generic-bvar-db-env-ok hyp-bvar-db t (next-bvar$a hyp-bvar-db) env)
;;                     (bfr-eval hyp-bfr (car env))
;;                     (bfr-vars-bounded (next-bvar$a hyp-bvar-db) hyp-bfr)
;;                     (bvar-db-orderedp t hyp-bvar-db)
;;                     (gbc-db-vars-bounded (next-bvar$a hyp-bvar-db) t (nth *is-constraint-db* interp-st))
;;                     (bfr-hyp-eval (is-constraint interp-st) (car env))
;;                     (<= (shape-spec-max-bvar-list
;;                          (shape-spec-bindings->sspecs config1.shape-spec-alist))
;;                         (next-bvar$a hyp-bvar-db)))
;;                (glcp-generic-bvar-db-env-ok new-bvar-db hyp-bfr (next-bvar$a new-bvar-db) new-env)))
;;     :hints(("Goal" :in-theory (enable glmc-generic-interp-nonhyps
;;                                       glcp-generic-bvar-db-env-ok-normalize-cons-car-cdr-env)
;;             :cases ((atom env)))))

;;   (std::defret glmc-generic-interp-nonhyps-env-eval-bounded-bfr
;;     (b* (((glmc-config+ config)))
;;       (implies (and (pbfr-vars-bounded
;;                      (next-bvar$a hyp-bvar-db)
;;                      hyp-bfr x)
;;                     (bfr-vars-bounded (next-bvar$a hyp-bvar-db) hyp-bfr)
;;                     (bfr-eval hyp-bfr (car env)))
;;                (equal (bfr-eval x (car new-env))
;;                       (bfr-eval x (bfr-param-env hyp-bfr (car env))))))
;;     :hints(("Goal" :in-theory (enable glmc-generic-interp-nonhyps
;;                                       ;; glcp-generic-geval-alist-normalize-cons-car-cdr-env
;;                                       genv-param
;;                                       ))))
  
;;   (std::defret glmc-generic-interp-nonhyps-env-eval-bounded-gobj
;;     (b* (((glmc-config+ config)))
;;       (implies (and (gobj-vars-bounded
;;                      (next-bvar$a hyp-bvar-db)
;;                      hyp-bfr x)
;;                     (bfr-vars-bounded (next-bvar$a hyp-bvar-db) hyp-bfr)
;;                     (bfr-eval hyp-bfr (car env)))
;;                (equal (glcp-generic-geval x new-env)
;;                       (glcp-generic-geval x (genv-param hyp-bfr env)))))
;;     :hints(("Goal" :in-theory (enable glmc-generic-interp-nonhyps
;;                                       ;; glcp-generic-geval-alist-normalize-cons-car-cdr-env
;;                                       genv-param
;;                                       ))))

;;   (std::defret glmc-generic-interp-nonhyps-env-eval-bounded-alist
;;     (b* (((glmc-config+ config)))
;;       (implies (and (gobj-alist-vars-bounded
;;                      (next-bvar$a hyp-bvar-db)
;;                      hyp-bfr alist)
;;                     (bfr-vars-bounded (next-bvar$a hyp-bvar-db) hyp-bfr)
;;                     (bfr-eval hyp-bfr (car env)))
;;                (equal (glcp-generic-geval-alist alist new-env)
;;                       (glcp-generic-geval-alist alist (genv-param hyp-bfr env)))))
;;     :hints(("Goal" :in-theory (enable glmc-generic-interp-nonhyps
;;                                       ;; glcp-generic-geval-alist-normalize-cons-car-cdr-env
;;                                       genv-param
;;                                       )))))




; (std::defret glmc-generic-interp-hyp-dependencies

(local (in-theory (disable gobj-alist-to-param-space
                           hons-assoc-equal
                           alistp
                           remove-equal
                           shape-spec-bindings->sspecs
                           acl2::consp-when-member-equal-of-atom-listp
                           equal-of-booleans-rewrite)))






;; (defthmd glcp-generic-bvar-db-env-ok-normalize-cons-car-cdr-env
;;   (implies (atom env)
;;            (equal (glcp-generic-bvar-db-env-ok bvar-db p bound env)
;;                   (glcp-generic-bvar-db-env-ok bvar-db p bound '(nil))))
;;   :hints (("goal" :cases ((glcp-generic-bvar-db-env-ok bvar-db p bound env))
;;            :in-theory (e/d (glcp-generic-geval-list-normalize-cons-car-cdr-env
;;                             glcp-generic-geval-normalize-cons-car-cdr-env
;;                             default-car)
;;                            (glcp-generic-bvar-db-env-ok-necc)))
;;           (and stable-under-simplificationp
;;                (b* ((look (assoc 'glcp-generic-bvar-db-env-ok clause))
;;                     (env (nth 4 look))
;;                     (other-env (if (eq env 'env) ''(nil) 'env)))
;;                  `(:expand (,look)
;;                    :use ((:instance glcp-generic-bvar-db-env-ok-necc
;;                           (n (glcp-generic-bvar-db-env-ok-witness bvar-db p bound ,env))
;;                           (env ,other-env))))))))

(defthm car-of-genv-unparam
    (equal (car (genv-unparam bfr env))
           (bfr-unparam-env bfr (car env)))
    :hints(("Goal" :in-theory (enable genv-unparam))))


(defthm bfr-vars-bounded-of-binary-and
  (implies (and (bfr-vars-bounded k x)
                (bfr-vars-bounded k y))
           (bfr-vars-bounded k (bfr-binary-and x y)))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defthm pbfr-vars-bounded-of-binary-and
  (implies (and (pbfr-vars-bounded k p x)
                (pbfr-vars-bounded k p y))
           (pbfr-vars-bounded k p (bfr-binary-and x y)))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


(define glmc-generic-mcheck-main-interps-env (env config state)
  :non-executable t
  :verify-guards nil
  :returns (new-env)
  (b* (((std::ret hyps-interp :ignore-stobjs t)
        (glmc-generic-interp-hyps config nil nil state))
       (hyp-bfr-env (bvar-db-fix-env (next-bvar$a hyps-interp.new-bvar-db)
                                     (base-bvar$a hyps-interp.new-bvar-db)
                                     hyps-interp.new-bvar-db
                                     t (car env) (cdr env)))
       (hyp-bfr (bfr-and hyps-interp.in-hyp-bfr
                         hyps-interp.st-hyp-bfr))
       ((std::ret nonhyps-interp :ignore-stobjs t)
        (glmc-generic-interp-nonhyps
         config
         hyp-bfr
         hyps-interp.new-interp-st
         nil
         hyps-interp.new-bvar-db
         hyps-interp.new-state))
       (final-bfr-env (bvar-db-fix-env (next-bvar$a nonhyps-interp.new-bvar-db)
                                       (next-bvar$a hyps-interp.new-bvar-db)
                                       nonhyps-interp.new-bvar-db
                                       t
                                       hyp-bfr-env (cdr env))))
    (cons final-bfr-env (cdr env)))
  ///
  (std::defret glmc-generic-mcheck-main-interps-env-glcp-generic-geval-vars-bounded
    (b* (((glmc-config+ config)))
      (implies (and (gobj-vars-bounded (shape-spec-max-bvar-list
                                        (shape-spec-bindings->sspecs
                                         config.shape-spec-alist))
                                       t x)
                    (bfr-mode))
               (equal (glcp-generic-geval x new-env)
                      (glcp-generic-geval x env))))
    :hints(("Goal" :in-theory (enable GLCP-GENERIC-GEVAL-NORMALIZE-CONS-CAR-CDR-ENV))))

  (std::defret glmc-generic-mcheck-main-interps-env-glcp-generic-geval-alist-vars-bounded
    (b* (((glmc-config+ config)))
      (implies (and (gobj-alist-vars-bounded (shape-spec-max-bvar-list
                                              (shape-spec-bindings->sspecs
                                               config.shape-spec-alist))
                                             t x)
                    (bfr-mode))
               (equal (glcp-generic-geval-alist x new-env)
                      (glcp-generic-geval-alist x env))))
    :hints(("Goal" :in-theory (e/d (gobj-alist-vars-bounded
                                    glcp-generic-geval-alist)
                                   (glmc-generic-mcheck-main-interps-env))))))
                                       

(defthm glmc-syntax-checks-of-glmc-config-update-rewrites
  (equal (glmc-syntax-checks (glmc-config-update-rewrites config rewrites branch-merges))
         (glmc-syntax-checks config))
  :hints(("Goal" :in-theory (e/d (glmc-syntax-checks glmc-config-update-rewrites
                                    glcp-config-update-rewrites)
                                 (not
                                  acl2::subsetp-member
                                  vars-subset-of-bound-by-glmc-syntax-checks
                                  union-equal
                                  append
                                  shape-specs-duplicate-free-by-glmc-syntax-checks))
          :do-not '(preprocess))))

(defsection glmc-generic-mcheck-main-interps
  (local (in-theory (enable glmc-generic-mcheck-main-interps)))
  (local (std::set-define-current-function glmc-generic-mcheck-main-interps))
  (verify-guards glmc-generic-mcheck-main-interps)
;; (define glmc-generic-mcheck-main-interps ((config glmc-config-p)
;;                                           interp-st
;;                                           bvar-db
;;                                           state)
;;   :guard (and (acl2::interp-defs-alistp (glcp-config->overrides (glmc-config->glcp-config config)))
;;               (non-exec (equal interp-st (create-interp-st))))
;;   :returns (mv nextst prop-bfr constr-bfr initst-bfr st-hyp-bfr hyp-bfr st-hyp-next-bfr
;;                (hyp-max-bvar (implies (not er) (natp hyp-max-bvar)) :rule-classes :type-prescription)
;;                er new-interp-st new-bvar-db new-state)
;;   (b* (((acl2::local-stobjs hyp-bvar-db)
;;         (mv nextst prop-bfr constraint-bfr initstp-bfr st-hyp-bfr hyp-bfr st-hyp-next-bfr hyp-max-bvar er interp-st bvar-db hyp-bvar-db state))
       
;;        ((glmc-config+ config))
;;        (bvar-db (init-bvar-db 0 bvar-db)) ;; nonsense

;;        ((mv st-hyp-bfr in-hyp-bfr er interp-st hyp-bvar-db state)
;;         (glmc-generic-interp-hyps config interp-st hyp-bvar-db state))
;;        ((when er)
;;         (mv nil nil nil nil nil nil nil nil er interp-st bvar-db hyp-bvar-db state))

;;        (hyp-bfr (bfr-and in-hyp-bfr st-hyp-bfr))

;;        (hyp-max-bvar (next-bvar hyp-bvar-db))

;;        ((mv initst-bfr constr-bfr prop-bfr st-hyp-next-bfr nextst er interp-st bvar-db state)
;;         (glmc-generic-interp-nonhyps config hyp-bfr interp-st bvar-db hyp-bvar-db state))
;;        ((when er)
;;         (mv nil nil nil nil nil nil nil nil er interp-st bvar-db hyp-bvar-db state)))

;;     (mv nextst prop-bfr constr-bfr initst-bfr st-hyp-bfr hyp-bfr st-hyp-next-bfr hyp-max-bvar nil interp-st bvar-db hyp-bvar-db state))
;;   ///

  (std::defret interp-defs-of-glmc-generic-mcheck-main-interps
    (b* (((glmc-config+ config)))
      (implies (and (acl2::interp-defs-alistp config.overrides)
                    (glmc-config-p config))
               (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st)))))

  (local (defthm glcp-interp-accs-ok-of-unparam-param
           (implies (and (glcp-interp-accs-ok interp-st bvar-db config (genv-unparam bfr (genv-param bfr env)))
                         (bfr-eval bfr (car env)))
                    (glcp-interp-accs-ok interp-st bvar-db config env))
           :hints(("Goal" :in-theory (e/d (glcp-interp-accs-ok genv-unparam genv-param
                                                               glcp-generic-bvar-db-env-ok-normalize-cons-car-cdr-env)
                                          (default-car default-cdr))))
           :rule-classes :forward-chaining))

  ;; (local (defthm glcp-generic-geval-alist-of-fal-extract
  ;;          (equal (GLCP-GENERIC-GEVAL-ALIST (ACL2::FAL-EXTRACT VARS ALIST) ENV)
  ;;                 (ACL2::FAL-EXTRACT VARS (GLCP-GENERIC-GEVAL-ALIST ALIST ENV)))))

  ;; (local (in-theory (disable FAL-EXTRACT-OF-GLCP-GENERIC-GEVAL-ALIST)))

  ;; (std::defret glmc-generic-mcheck-main-interps-hyp-bfrs-correct
  ;;   (b* (((glmc-config+ config))
  ;;        (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist)
  ;;                                         (genv-unparam hyp-bfr env)))
  ;;        (st-alist (acl2::fal-extract (list config.st-var) alist)))
  ;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db
  ;;                                        (glcp-config-update-param hyp-bfr1 config.glcp-config)
  ;;                                        env)
  ;;                   (equal hyp-bfr1 hyp-bfr)
  ;;                   (not (glmc-syntax-checks config))
  ;;                   (equal bfr-env (car env))
  ;;                   (bfr-hyp-eval pathcond bfr-env)
  ;;                   (acl2::interp-defs-alistp config.overrides)
  ;;                   (glmc-config-p config)
  ;;                   (assoc config.st-var config.shape-spec-alist)
  ;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                   (equal (w state0) (w state))
  ;;                   (not er))
  ;;              (and (iff (bfr-eval st-hyp-bfr (bfr-unparam-env hyp-bfr bfr-env))
  ;;                        (glcp-generic-geval-ev config.st-hyp st-alist))
  ;;                   (iff (bfr-eval hyp-bfr (bfr-unparam-env hyp-bfr bfr-env))
  ;;                        (and (glcp-generic-geval-ev config.st-hyp alist)
  ;;                             (glcp-generic-geval-ev config.in-hyp alist)))))))

  ;; (std::defret glmc-generic-mcheck-main-interps-hyp-bfrs-satisfied
  ;;   (b* (((glmc-config+ config))
  ;;        (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist)
  ;;                                         env)))
  ;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db
  ;;                                        (glcp-config-update-param hyp-bfr config.glcp-config)
  ;;                                        env)
  ;;                   (not (glmc-syntax-checks config))
  ;;                   (equal bfr-env (car env))
  ;;                   ;; (bfr-hyp-eval pathcond bfr-env)
  ;;                   (acl2::interp-defs-alistp config.overrides)
  ;;                   (glmc-config-p config)
  ;;                   ;; (assoc config.st-var config.shape-spec-alist)
  ;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                   (equal (w state0) (w state))
  ;;                   (not er)
  ;;                   (glcp-generic-geval-ev config.st-hyp alist)
  ;;                   (glcp-generic-geval-ev config.in-hyp alist))
  ;;              (and (bfr-eval st-hyp-bfr (car env))
  ;;                   (bfr-eval hyp-bfr (car env))))))

  (std::defretd glmc-generic-mcheck-main-interps-hyp-bfrs
    (b* (((mv st-hyp-bfr1 in-hyp-bfr1  & & & &)
          (glmc-generic-interp-hyps config nil nil state)))
      (implies (not er)
               (and (equal hyp-bfr (bfr-and in-hyp-bfr1 st-hyp-bfr1))
                    (equal st-hyp-bfr st-hyp-bfr1)))))

  (std::defret glmc-generic-mcheck-main-interps-env-ok
    (b* (((glmc-config+ config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist) env))
         (fix-env (glmc-generic-mcheck-main-interps-env env config state)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (not (glmc-syntax-checks config))
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (glmc-config-p config)
                    ;; (assoc config.st-var config.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode))
               (glcp-generic-bvar-db-env-ok new-bvar-db t (next-bvar$a new-bvar-db) fix-env)))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps-env))))

  (std::defret glmc-generic-mcheck-main-interps-hyp-env-ok
    (b* (((glmc-config+ config))
         (fix-env (glmc-generic-mcheck-main-interps-env env config state)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (not (glmc-syntax-checks config))
                    (glmc-config-p config)
                    ;; (assoc config.st-var config.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode))
               (glcp-generic-bvar-db-env-ok
                (mv-nth 4 (glmc-generic-interp-hyps config nil nil state))
                t hyp-max-bvar fix-env)))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps-env))))

  (local (defthm glmc-config->bindings-of-glmc-config-update-param
           (equal (glmc-config->bindings (glmc-config-update-param p config))
                  (glmc-config->bindings config))
           :hints(("Goal" :in-theory (enable glmc-config-update-param)))))

  (std::defret glmc-generic-mcheck-main-interps-nextst-correct
    (b* (((glmc-config+ config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist) env))
         (fix-env (glmc-generic-mcheck-main-interps-env env config state)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (not (glmc-syntax-checks config))
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (glmc-config-p config)
                    ;; (assoc config.st-var config.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode))
               (equal (glcp-generic-geval nextst fix-env)
                      (glcp-generic-geval-ev config.nextst
                                             (glmc-generic-ev-bindinglist config.bindings alist)))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps-env))))

  (std::defret glmc-generic-mcheck-main-interps-concl-bfrs-correct
    (b* (((glmc-config+ config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist) env))
         (fix-env (glmc-generic-mcheck-main-interps-env env config state))
         )
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (not (glmc-syntax-checks config))
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (glmc-config-p config)
                    ;; (assoc config.st-var config.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode))
               (b* ((new-alist (glmc-generic-ev-bindinglist config.bindings alist)))
               (and (equal (bfr-eval initst-bfr (car fix-env))
                           (bool-fix (glcp-generic-geval-ev config.initstp new-alist)))
                    (equal (bfr-eval constr-bfr (car fix-env))
                           (bool-fix (glcp-generic-geval-ev config.constr new-alist)))
                    (equal (bfr-eval prop-bfr (car fix-env))
                           (bool-fix (glcp-generic-geval-ev config.prop new-alist)))
                    (equal (bfr-eval st-hyp-next-bfr (car fix-env))
                           (bool-fix (glcp-generic-geval-ev config.st-hyp
                                                            (list (cons config.st-var
                                                                        (glcp-generic-geval-ev config.nextst new-alist))))))))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps-env
                                      equal-of-booleans-rewrite))))

  (std::defret glmc-generic-mcheck-main-interps-hyp-bfrs-correct
    (b* (((glmc-config+ config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist) env))
         (fix-env (glmc-generic-mcheck-main-interps-env env config state))
         )
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (not (glmc-syntax-checks config))
                    (glmc-config-p config)
                    ;; (assoc config.st-var config.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode))
               (and (equal (bfr-eval st-hyp-bfr (car fix-env))
                           (bool-fix (glcp-generic-geval-ev config.st-hyp alist)))
                    (equal (bfr-eval hyp-bfr (car fix-env))
                           (and (glcp-generic-geval-ev config.st-hyp alist)
                                (bool-fix (glcp-generic-geval-ev config.in-hyp alist)))))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps-env
                                      equal-of-booleans-rewrite))))

  (std::defret glmc-generic-mcheck-main-interps-constraint-correct
    (b* (((glmc-config+ config))
         (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist) env))
         (fix-env (glmc-generic-mcheck-main-interps-env env config state)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glmc-config-p config)
                    (not (glmc-syntax-checks config))
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (not er)
                    (bfr-mode))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) (car fix-env))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps-env))))

  ;; (std::defret glmc-generic-mcheck-main-interps-nextst-correct
  ;;   (b* (((glmc-config+ config))
  ;;        (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist)
  ;;                                         (genv-unparam hyp-bfr env))))
  ;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db
  ;;                                        (glcp-config-update-param hyp-bfr1 config.glcp-config)
  ;;                                        env)
  ;;                   (equal hyp-bfr1 hyp-bfr)
  ;;                   (equal bfr-env (car env))
  ;;                   (not (glmc-syntax-checks config))
  ;;                   (glcp-generic-geval-ev config.st-hyp alist)
  ;;                   (glcp-generic-geval-ev config.in-hyp alist)
  ;;                   (acl2::interp-defs-alistp config.overrides)
  ;;                   (glmc-config-p config)
  ;;                   ;; (assoc config.st-var config.shape-spec-alist)
  ;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                   (equal (w state0) (w state))
  ;;                   (not er))
  ;;              (equal (glcp-generic-geval nextst env)
  ;;                     (glcp-generic-geval-ev config.nextst alist)))))

  ;; (std::defret glmc-generic-mcheck-main-interps-concl-bfrs-correct
  ;;   (b* (((glmc-config+ config))
  ;;        (alist (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist)
  ;;                                         (genv-unparam hyp-bfr env)))
  ;;        ;; (st-alist (acl2::fal-extract (list config.st-var) alist))
  ;;        )
  ;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db
  ;;                                        (glcp-config-update-param hyp-bfr1 config.glcp-config)
  ;;                                        env)
  ;;                   (equal hyp-bfr1 hyp-bfr)
  ;;                   (equal bfr-env (car env))
  ;;                   (not (glmc-syntax-checks config))
  ;;                   (glcp-generic-geval-ev config.st-hyp alist)
  ;;                   (glcp-generic-geval-ev config.in-hyp alist)
  ;;                   (acl2::interp-defs-alistp config.overrides)
  ;;                   (glmc-config-p config)
  ;;                   ;; (assoc config.st-var config.shape-spec-alist)
  ;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                   (equal (w state0) (w state))
  ;;                   (not er))
  ;;              (and (iff (bfr-eval initst-bfr bfr-env)
  ;;                        (glcp-generic-geval-ev config.initstp alist))
  ;;                   (iff (bfr-eval constr-bfr bfr-env)
  ;;                        (glcp-generic-geval-ev config.constr alist))
  ;;                   (iff (bfr-eval prop-bfr bfr-env)
  ;;                        (glcp-generic-geval-ev config.prop alist))
  ;;                   (iff (bfr-eval st-hyp-next-bfr bfr-env)
  ;;                        (glcp-generic-geval-ev config.st-hyp
  ;;                                               (list (cons config.st-var
  ;;                                                           (glcp-generic-geval-ev config.nextst alist)))))))))

  ;; (std::defret glmc-generic-mcheck-main-interps-constraint-correct
  ;;   (b* (((glmc-config+ config)))
  ;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db
  ;;                                        (glcp-config-update-param hyp-bfr1 config.glcp-config)
  ;;                                        env)
  ;;                   (equal hyp-bfr1 hyp-bfr)
  ;;                   (equal bfr-env (car env))
  ;;                   (acl2::interp-defs-alistp config.overrides)
  ;;                   (glmc-config-p config)
  ;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                   (equal (w state0) (w state))
  ;;                   (not er))
  ;;              (bfr-hyp-eval (nth *is-constraint* new-interp-st) bfr-env))))
  
  (std::defret w-state-preserved-of-glmc-generic-mcheck-main-interps
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glmc-generic-mcheck-main-interps
    (implies (state-p1 state) (state-p1 new-state)))

  ;; (std::defret base-bvar-of-glmc-generic-mcheck-main-interps
  ;;   (equal (base-bvar$a new-bvar-db) (base-bvar$a hyp-bvar-db)))

  ;; (std::defret next-bvar-of-glmc-generic-mcheck-main-interps
  ;;   (>= (next-bvar$a new-bvar-db) (next-bvar$a hyp-bvar-db))
  ;;   :rule-classes :linear)

  ;; (std::defret get-bvar->term-of-glcp-generic-run-nextst-and-prop
  ;;   (implies (and (<= (base-bvar$a hyp-bvar-db) (nfix n))
  ;;                 (< (nfix n) (next-bvar$a hyp-bvar-db)))
  ;;            (equal (get-bvar->term$a n new-bvar-db)
  ;;                   (gobj-to-param-space (get-bvar->term$a n hyp-bvar-db)
  ;;                                        hyp-bfr))))

  (std::defret glmc-generic-mcheck-main-interps-vars-bounded
    (b* (((glmc-config+ config)))
      (implies (not er)
               (and (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                                  (equal hyp-bfr1 hyp-bfr))
                    ;; (<= (shape-spec-max-bvar-list
                    ;;      (shape-spec-bindings->sspecs config.shape-spec-alist))
                    ;;     (nfix k))

                             (and (pbfr-vars-bounded k hyp-bfr1 initst-bfr)
                                  (pbfr-vars-bounded k hyp-bfr1 constr-bfr)
                                  (pbfr-vars-bounded k hyp-bfr1 prop-bfr)
                                  (pbfr-vars-bounded k hyp-bfr1 st-hyp-next-bfr)
                                  (gobj-vars-bounded k hyp-bfr1 nextst)
                                  (bfr-constr-vars-bounded k hyp-bfr1 (nth *is-constraint* new-interp-st))
                                  (implies (equal nn (next-bvar$a new-bvar-db))
                                           (bvar-db-vars-bounded k hyp-bfr1 nn new-bvar-db))
                                  (gbc-db-vars-bounded k hyp-bfr1 (nth *is-constraint-db* new-interp-st))))
                    (implies (<= hyp-max-bvar (nfix k))
                             (and (pbfr-vars-bounded k t st-hyp-bfr)
                                  (pbfr-vars-bounded k t hyp-bfr))))))
    :hints(("Goal" :in-theory (enable gbc-db-empty-implies-gbc-db-vars-bounded))))

  (std::defret glmc-generic-mcheck-main-interps-vars-bounded-aig-mode
    (b* (((glmc-config+ config)))
      (implies (and (not er) (Bfr-mode))
               (and (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                                  ;; bozo
                                  (equal hyp-bfr1 hyp-bfr))
                    ;; (<= (shape-spec-max-bvar-list
                    ;;      (shape-spec-bindings->sspecs config.shape-spec-alist))
                    ;;     (nfix k))

                             (and (pbfr-vars-bounded k t initst-bfr)
                                  (pbfr-vars-bounded k t constr-bfr)
                                  (pbfr-vars-bounded k t prop-bfr)
                                  (pbfr-vars-bounded k t st-hyp-next-bfr)
                                  (gobj-vars-bounded k t nextst)
                                  (bfr-constr-vars-bounded k t (nth *is-constraint* new-interp-st))
                                  (gbc-db-vars-bounded k t (nth *is-constraint-db* new-interp-st)))))))
    :hints (("goal" :in-theory (disable glmc-generic-mcheck-main-interps-vars-bounded
                                        glmc-generic-mcheck-main-interps)
             :use ((:instance glmc-generic-mcheck-main-interps-vars-bounded)))))

  (std::defret glmc-generic-mcheck-main-interps-bvar-db-ordered
    (b* (((glmc-config+ config)))
      (implies (And (not er)
                    (equal hyp-bfr1 hyp-bfr))
               (bvar-db-orderedp hyp-bfr1 new-bvar-db)))
    :hints(("Goal" :in-theory (enable gbc-db-empty-implies-gbc-db-vars-bounded))))

  (std::defret glmc-generic-mcheck-main-interps-bvar-db-ordered-aig-mode
    (b* (((glmc-config+ config)))
      (implies (And (not er)
                    (bfr-mode)
                    (equal hyp-bfr1 hyp-bfr))
               (bvar-db-orderedp t new-bvar-db)))
    :hints (("goal" :in-theory (disable glmc-generic-mcheck-main-interps-bvar-db-ordered
                                        glmc-generic-mcheck-main-interps)
             :use glmc-generic-mcheck-main-interps-bvar-db-ordered)))

  (defthm glmc-generic-mcheck-main-interps-normalize
    (implies (syntaxp (not (and (equal bvar-db ''nil)
                                (equal interp-st ''nil))))
             (equal (glmc-generic-mcheck-main-interps config interp-st bvar-db state)
                    (glmc-generic-mcheck-main-interps config nil nil state))))

  (std::defret glmc-generic-main-interps-next-bvar-gte-shape-spec-max
    (b* (((glmc-config+ config)))
      (implies (not er)
               (<= (shape-spec-max-bvar-list
                    (shape-spec-bindings->sspecs config.shape-spec-alist))
                   (next-bvar$a new-bvar-db))))
    :rule-classes :linear)

  ;; (std::defret glmc-generic-main-interps-bvar-db-extends-hyp-bvar-db
  ;;   (implies (and (not er)
  ;;                 (equal hyp-bfr1 hyp-bfr))
  ;;            (bvar-db-extension-p new-bvar-db
  ;;                                 (parametrize-bvar-db hyp-bfr1 (mv-nth 4 (glmc-generic-interp-hyps config nil nil state)) nil))))

  ;; (std::defret glmc-generic-main-interp-hyp-max-bvar-lower-bound
  ;;   (b* (((glmc-config+ config)))
  ;;     (implies (not er)
  ;;              (<= (shape-spec-max-bvar-list
  ;;                   (shape-spec-bindings->sspecs config.shape-spec-alist))
  ;;                  hyp-max-bvar)))
  ;;   :rule-classes :linear)

  (std::defret glmc-generic-main-interp-hyp-max-bvar-upper-bound
    (implies (not er)
             (<= hyp-max-bvar
                 (next-bvar$a new-bvar-db)))
    :rule-classes (:rewrite :linear))

  ;; (std::defret glmc-generic-main-interps-hyp-max-bvar-is-hyp-bvar-db-next
  ;;   (implies (not er)
  ;;            (equal hyp-max-bvar
  ;;                   (next-bvar$a (mv-nth 4 (glmc-generic-interp-hyps config nil nil state))))))
  

  ;; (std::defret glmc-generic-mcheck-main-interps-accs-ok
  ;;   (b* (((glmc-config+ config))
  ;;        ((mv st-hyp in-hyp &  hyp-interp-st hyp-bvar-db &)
  ;;         (glmc-generic-interp-hyps config nil nil state))
  ;;        (hyp-bfr  (bfr-and in-hyp st-hyp))
  ;;        (param-config  (glcp-config-update-param hyp-bfr config.glcp-config)))
  ;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db param-config env)
  ;;                   (not er))
  ;;              (glcp-interp-accs-ok hyp-interp-st
  ;;                                   hyp-bvar-db
  ;;                                   (glcp-config-update-param t config.glcp-config)
  ;;                                   (genv-unparam hyp-bfr env))))
  ;;   ;; :hints(("Goal" :in-theory (enable genv-unparam)))
  ;;   :rule-classes :forward-chaining)

  (std::defret glmc-generic-main-interps-interp-st-obligs-extends-hyp
    (INTERP-ST-OBLIGS-EXTENSION-P new-interp-st
                                  (MV-NTH 3
                                          (GLMC-GENERIC-INTERP-HYPS CONFIG NIL NIL STATE))))

  

  (std::defret bfr-lookup-in-glmc-generic-main-interps-env-out-of-range
    (b* (((glmc-config+ config))
         (fix-env (glmc-generic-mcheck-main-interps-env env config state)))
      (implies (and (bfr-mode)
                    (not er)
                    (not (and (integerp (bfr-varname-fix k))
                              (<= (shape-spec-max-bvar-list
                                   (shape-spec-bindings->sspecs
                                    config.shape-spec-alist))
                                  (bfr-varname-fix k))
                              (< (bfr-varname-fix k)
                                 (next-bvar$a new-bvar-db)))))
               (equal (bfr-lookup k (car fix-env))
                      (bfr-lookup k (car env)))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps-env))))

  (std::defret get-bvar->term-below-hyp-bound-of-glcp-generic-main-interps
      (implies (and (<= (base-bvar$a new-bvar-db) (nfix n))
                    (< (nfix n) hyp-max-bvar))
               (equal (get-bvar->term$a n new-bvar-db)
                      (gobj-to-param-space
                       (get-bvar->term$a n
                                         (mv-nth 4 (glmc-generic-interp-hyps config nil nil state)))
                       hyp-bfr)))))

;; (define glmc-generic-main-interps-env ((env consp)
;;                                        (config glmc-config-p)
;;                                        state)
;;   :non-executable t
;;   :verify-guards nil
;;   :returns (new-env consp :rule-classes :type-prescription)
;;   (b* (((glmc-config+ config))

;;        (hyp-env (glmc-generic-interp-hyps-env env config state))
;;        ((mv ?st-hyp-bfr ?in-hyp-bfr ?er ?interp-st hyp-bvar-db state)
;;         (glmc-generic-interp-hyps config nil nil state))
       
;;        (hyp-bfr (bfr-and in-hyp-bfr st-hyp-bfr)))

;;     (glmc-generic-interp-nonhyps-env hyp-env hyp-bfr config interp-st hyp-bvar-db state))
;;   ///
;;   (local (in-theory (disable bvar-db-fix-env alistp
;;                              equal-of-booleans-rewrite)))
  
;;   (std::defret glmc-generic-main-interps-env-bvar-db-env-ok
;;     (b* (((mv ?nextst ?prop-bfr ?constr-bfr ?initst-bfr ?st-hyp-bfr ?hyp-bfr ?hyp-max-bfr ?er ?new-interp-st ?new-bvar-db ?new-state)
;;           (glmc-generic-mcheck-main-interps config interp-st bvar-db state))
;;          ((glmc-config+ config)))
;;       (implies (bfr-eval hyp-bfr (car (glmc-generic-interp-hyps-env env config state)))
;;                (glcp-generic-bvar-db-env-ok new-bvar-db hyp-bfr (next-bvar$a new-bvar-db) new-env)))
;;     :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps)))))
;;       (implies (and (glcp-generic-geval-ev-theoremp
;;                      (conjoin-clauses
;;                       (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
;;                     (equal bfr-env (car env))
;;                     (not (glmc-syntax-checks config))
;;                     (glcp-generic-geval-ev config.st-hyp alist)
;;                     (glcp-generic-geval-ev config.in-hyp alist)
;;                     (acl2::interp-defs-alistp config.overrides)
;;                     (glmc-config-p config)
;;                     (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
;;                     (equal (w state0) (w state))
;;                     (glcp-generic-geval-ev (shape-spec-list-oblig-term
;;                                             (shape-spec-bindings->sspecs config.shape-spec-alist)
;;                                             (alist-keys config.shape-spec-alist))
;;                                            alist)
;;                     (not er))
;;                (and (glcp-generic-bvar-db-env-ok new-bvar-db hyp-bfr (next-bvar$a new-bvar-db) env)
;;                     (bfr-eval hyp-bfr (bfr-unparam-env hyp-bfr bfr-env))
;;                     (bfr-eval st-hyp-bfr (bfr-unparam-env hyp-bfr bfr-env))
;;                     (iff (bfr-eval initst-bfr bfr-env)
;;                          (glcp-generic-geval-ev config.initstp st-alist))
;;                     (iff (bfr-eval constr-bfr bfr-env)
;;                          (glcp-generic-geval-ev config.constr alist))
;;                     (iff (bfr-eval prop-bfr bfr-env)
;;                          (glcp-generic-geval-ev config.prop alist))
;;                     (equal (glcp-generic-geval nextst env)
;;                       (glcp-generic-geval-ev config.nextst alist)))))
;;     :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps
;;                                       gbc-db-empty-implies-gbc-db-vars-bounded
;;                                       genv-unparam)))))

;;   (std::defret glmc-generic-interp-hyps-env-correct
;;     (b* (((glmc-config+ config)))
;;       (implies (and (<= (SHAPE-SPEC-MAX-BVAR-LIST (SHAPE-SPEC-BINDINGS->SSPECS config.shape-spec-alist))
;;                         (base-bvar$a new-BVAR-DB))
;;                     (glcp-generic-geval-ev (shape-spec-list-oblig-term
;;                                             (shape-spec-bindings->sspecs config.shape-spec-alist)
;;                                             (alist-keys config.shape-spec-alist))
;;                                            alist)
;;                     (shape-spec-bindingsp config.shape-spec-alist)
;;                     (not (glmc-syntax-checks config)))
;;                (equal (glcp-generic-geval-alist (shape-specs-to-interp-al config.shape-spec-alist) env)
;;                       (pairlis$ (alist-keys config.shape-spec-alist)
;;                                 (glcp-generic-geval-ev-lst (alist-keys config.shape-spec-alist) alist)))))))






;; To get a Boolean-level state transition function --
;;  - Symbolically execute the transition function and property.
;;  - Analyze (invert) the shape spec for the state variable(s).
;;     - Boolean var -> term alist: symbolic execution of term with state
;;       variable(s) bound to the result of the transition function gives the
;;       update function for the Boolean var.
;;     - Unconstrained var -> term alist: symbolic execution of term gives the
;;       update value of each unconstrained variable.
;; Then we need to analyze the bvar db to get the bits generated from each
;; unconstrained variable.  Start with state_bvars := the set of Boolean
;; variables from the state shape specs.
;; For each bvar in the db
;;   - if the bound object's gvars are a subset of the unconstrained variables
;;     of the state shapespecs and its bvars are a subset of the state_bvars,
;;     compose the object with the updates for those bvars/gvars to get this
;;     bvar's update (we need some new functions for this!); add this bvar to
;;     the state_bvars.
;;   - if the bound object's gvars are disjoint from the state unconstrained
;;     vars and bvars are disjoint from the state_bvars, then this is just a PI
;;     bvar (has no update function)
;;   - otherwise, we have a weird case that we might want to warn about, but
;;     it's sound to consider this bvar a PI as well (just might ruin
;;     completeness).

;; To prove this correct, need to show that every run of the real term-level
;; property maps to a run of the Boolean machine, so that if (we prove) the
;; property always holds of the Boolean machine, it must always hold of the
;; term-level machine.  For a given cycle, the shape-spec-invert-correct thm
;; gives this mapping for shape spec bvars.  Evaluating the bvar-db in
;; numerical order gives the rest of the bvars.  The challenge will be to show
;; that the method above for computing the state transition relation is
;; consistent with this.


(define glcp-generic-geval-ev-bfr-update-alist ((x pseudo-term-alistp)
                                                (a alistp))
  :guard (bfr-varnamelist-p (alist-keys x))
  :verify-guards nil
  :returns (x-eval alistp)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (bfr-varname-p (caar x))))
        (cons (cons (caar x) (bool-fix (glcp-generic-geval-ev (cdar x) a)))
              (glcp-generic-geval-ev-bfr-update-alist (cdr x) a))
      (glcp-generic-geval-ev-bfr-update-alist (cdr x) a)))
  ///
  (std::defret lookup-in-glcp-generic-geval-ev-bfr-update-alist
    (equal (hons-assoc-equal k x-eval)
           (and (bfr-varname-p k)
                (hons-assoc-equal k x)
                (cons k (bool-fix (glcp-generic-geval-ev
                                   (cdr (hons-assoc-equal k x)) a)))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal)))))


(defthm BVAR-DB-ORDERED-OF-GLCP-GENERIC-INTERP-TEST-aig-mode
  (B* (((MV ?VAL ?ERP ?PATHCOND1 ?INTERP-ST1 ?BVAR-DB1 ?STATE1)
        (GLCP-GENERIC-INTERP-TEST X ALIST PATHCOND CLK CONFIG INTERP-ST BVAR-DB ST))
       (K (NEXT-BVAR$A BVAR-DB)))
    (IMPLIES
     (and (EQUAL P (GLCP-CONFIG->PARAM-BFR CONFIG))
          (GOBJ-ALIST-VARS-BOUNDED K P ALIST))
     (AND
      (IMPLIES
       (AND 
            (BFR-VARS-BOUNDED K P)
            (BVAR-DB-ORDEREDP P BVAR-DB)
            (BVAR-DB-VARS-BOUNDED K P K BVAR-DB)
            (GBC-DB-VARS-BOUNDED
             K P (NTH *IS-CONSTRAINT-DB* INTERP-ST))
            (bfr-mode))
       (BVAR-DB-ORDEREDP t BVAR-DB1)))))
  :hints (("goal" :use ((:instance BVAR-DB-ORDERED-OF-GLCP-GENERIC-INTERP-TEST))
           :in-theory (disable bvar-db-ordered-of-glcp-generic-interp-test))))

(DEFTHM VARS-BOUNDED-OF-GLCP-GENERIC-INTERP-TEST-aig-mode
  (B* (((MV ?VAL ?ERP ?PATHCOND1 ?INTERP-ST1 ?BVAR-DB1 ?STATE1)
        (GLCP-GENERIC-INTERP-TEST X ALIST PATHCOND CLK CONFIG INTERP-ST BVAR-DB ST)))
    (IMPLIES
     (AND (AND (EQUAL P (GLCP-CONFIG->PARAM-BFR CONFIG))
               (<= (NEXT-BVAR$A BVAR-DB1) (NFIX K))
               (BFR-VARS-BOUNDED K P)
               (BVAR-DB-VARS-BOUNDED K P (NEXT-BVAR$A BVAR-DB)
                                     BVAR-DB)
               (EQUAL NN (NEXT-BVAR$A BVAR-DB1))
               (GBC-DB-VARS-BOUNDED
                K P (NTH *IS-CONSTRAINT-DB* INTERP-ST)))
          (GOBJ-ALIST-VARS-BOUNDED K P ALIST)
          (bfr-mode))
     (AND (PBFR-VARS-BOUNDED K t VAL)
          (IMPLIES (BFR-CONSTR-VARS-BOUNDED
                    K t (NTH *IS-CONSTRAINT* INTERP-ST))
                   (BFR-CONSTR-VARS-BOUNDED
                    K t (NTH *IS-CONSTRAINT* INTERP-ST1)))
          (BVAR-DB-VARS-BOUNDED K t NN BVAR-DB1)
          (GBC-DB-VARS-BOUNDED
           K t
           (NTH *IS-CONSTRAINT-DB* INTERP-ST1)))))
  :hints (("goal" :use ((:instance vars-bounded-of-glcp-generic-interp-test))
           :in-theory (disable vars-bounded-of-glcp-generic-interp-test))))



                          
  

(defthm glcp-generic-interp-test-correct-fix-env
  (b* (((mv test-bfr ?er ?new-pathcond ?new-interp-st ?new-bvar-db state)
        (glcp-generic-interp-test x alist pathcond clk config interp-st bvar-db state))
       (p (glcp-config->param-bfr config))
       (fix-bfr-env (bvar-db-fix-env
                     last-bvar first-bvar new-bvar-db t bfr-env var-env)))
    (implies (and (bfr-hyp-eval (nth *is-constraint* interp-st) bfr-env)
                  (bfr-eval p bfr-env)
                  (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                  (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) (cons bfr-env var-env))
                  (equal last-bvar (next-bvar$a new-bvar-db))
                  (equal first-bvar (next-bvar$a bvar-db))
                  ;; (equal pp p)
                  (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                  (equal (w state0) (w state))
                  (not er)
                  (bvar-db-orderedp p bvar-db)
                  (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                  (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                  (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                  (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                  (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                  (bfr-mode)
                  )
             (and (implies (bfr-hyp-eval pathcond bfr-env)
                           (equal (bfr-eval test-bfr fix-bfr-env)
                                  (bool-fix (glcp-generic-geval-ev x (glcp-generic-geval-alist alist (cons bfr-env var-env))))))
                  (bfr-hyp-eval (nth *is-constraint* new-interp-st) fix-bfr-env))))
  :hints (("goal" :use ((:instance glcp-generic-interp-correct-test
                         (st state)
                         (env (cons (bvar-db-fix-env
                                     last-bvar first-bvar
                                     (mv-nth 4 (glcp-generic-interp-test x alist pathcond clk config interp-st bvar-db state))
                                     t bfr-env var-env)
                                    var-env))))
           :in-theory (e/d (bdd-mode-or-p-true glcp-interp-accs-ok iff*)
                           (glcp-generic-interp-correct-test)))))
  

(define glmc-generic-interp-bvar-alist-env (env x alist pathcond config interp-st bvar-db state)
  :non-executable t
  :verify-guards nil
  :measure (len x)
  :returns (new-env)
  (b* (((when (atom x)) env)
       ((unless (mbt (and (consp (car x))
                          (bfr-varname-p (caar x)))))
        (glmc-generic-interp-bvar-alist-env env (cdr x) alist pathcond config interp-st bvar-db state))
       ((cons ?var term) (car x))
       ((mv & & pathcond interp-st new-bvar-db state)
        (glcp-generic-interp-test term alist pathcond (Glcp-config->concl-clk config) config interp-st bvar-db state))
       (env (cons (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                   (next-bvar$a bvar-db)
                                   new-bvar-db t (car env) (cdr env))
                  (cdr env))))
    (glmc-generic-interp-bvar-alist-env env (cdr x) alist pathcond config interp-st new-bvar-db state))
  ///
  (std::defret glmc-generic-interp-bvar-alist-env-eval-vars-bounded
    (implies (and (pbfr-vars-bounded (next-bvar$a bvar-db) t q)
                  (bfr-mode))
             (equal (bfr-eval q (car new-env))
                    (bfr-eval q (car env)))))

  (std::defret glmc-generic-interp-bvar-alist-env-bfr-eval-alist-vars-bounded
    (implies (and (pbfr-list-vars-bounded (next-bvar$a bvar-db) t (alist-vals q))
                  (bfr-mode))
             (equal (bfr-eval-alist q (car new-env))
                    (bfr-eval-alist q (car env))))
    :hints(("Goal" :in-theory (e/d (alist-vals pbfr-list-vars-bounded bfr-eval-alist)
                                   (glmc-generic-interp-bvar-alist-env))
            :induct (alist-vals q))))

  (std::defret glmc-generic-interp-bvar-alist-env-bfr-hyp-eval-vars-bounded
    (implies (and (bfr-constr-vars-bounded (next-bvar$a bvar-db) t q)
                  (bfr-mode))
             (equal (bfr-hyp-eval q (car new-env))
                    (bfr-hyp-eval q (car env))))))

(local (defthm pbfr-vars-bounded-of-alist-lookup
           (implies (pbfr-list-vars-bounded k p (alist-vals updates))
                    (pbfr-vars-bounded k p (cdr (hons-assoc-equal x updates))))
           :hints(("Goal" :in-theory (e/d (alist-vals hons-assoc-equal pbfr-list-vars-bounded))))))

(defsection glmc-generic-interp-bvar-alist
  (local (in-theory (enable glmc-generic-interp-bvar-alist)))
  (local (std::set-define-current-function glmc-generic-interp-bvar-alist))
  (verify-guards glmc-generic-interp-bvar-alist
    :hints(("Goal" :in-theory (enable pseudo-term-alistp))))

  (std::defret glmc-generic-interp-bvar-alist-new-pathcond
    (equal new-pathcond (bfr-hyp-fix pathcond)))

  (std::defret w-state-preserved-of-glcp-generic-interp-bvar-alist
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glcp-generic-interp-bvar-alist
    (implies (state-p1 state) (state-p1 new-state)))

  (std::defret bvar-db-extension-p-of-glcp-generic-interp-bvar-alist
    (bvar-db-extension-p new-bvar-db bvar-db))

  (std::defret interp-st-obligs-extension-p-of-glcp-generic-interp-bvar-alist
    (interp-st-obligs-extension-p new-interp-st interp-st))
;; (define glmc-generic-interp-bvar-alist ((x pseudo-term-alistp)
;;                                         (alist)
;;                                         pathcond
;;                                         (config glcp-config-p)
;;                                         interp-st
;;                                         bvar-db
;;                                         state)

;;   :guard (b* (((glcp-config config)))
;;            (and (acl2::interp-defs-alistp config.overrides)
;;                 (acl2::interp-defs-alistp (is-obligs interp-st))
;;                 (bfr-varnamelist-p (alist-keys x))))
;;   :returns (mv (updates bfr-updates-p)
;;                er 
;;                (new-pathcond (equal new-pathcond (bfr-hyp-fix pathcond)))
;;                new-interp-st
;;                new-bvar-db
;;                new-state)
;;   :guard-hints (("goal" :in-theory (enable pseudo-term-alistp)))
;;   (b* (((when (atom x))
;;         (b* ((pathcond (lbfr-hyp-fix pathcond)))
;;           (mv nil nil pathcond interp-st bvar-db state)))
;;        ((unless (mbt (and (consp (car x))
;;                           (bfr-varname-p (caar x)))))
;;         (glmc-generic-interp-bvar-alist
;;          (cdr x) alist pathcond config interp-st bvar-db state))
;;        ((cons var term) (car x))
;;        ((mv bfr er pathcond interp-st bvar-db state)
;;         (glcp-generic-interp-test term alist pathcond (glcp-config->concl-clk config) config interp-st bvar-db state))
;;        ((when er) (mv nil er pathcond interp-st bvar-db state))
;;        ((mv rest er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-bvar-alist (cdr x) alist pathcond config interp-st bvar-db state)))
;;     (mv (and (not er) (cons (cons var bfr) rest))
;;         er pathcond interp-st bvar-db state))
;;   ///
  
  (std::defret interp-defs-of-glcp-generic-interp-bvar-alist
    (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                  (acl2::interp-defs-alistp (glcp-config->overrides config))
                  (pseudo-term-alistp x))
             (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st)))
    :hints(("Goal" :in-theory (enable pseudo-term-alistp))))

  ;; (std::defret glcp-generic-interp-bvar-alist-accs-ok
  ;;   (implies (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
  ;;            (glcp-interp-accs-ok interp-st bvar-db config env))
  ;;   :rule-classes :forward-chaining)

  ;; (local (defthm equal-of-bfr-eval-rewrite-under-iff
  ;;          (implies (and (equal eval1 (bfr-eval x env))
  ;;                        (equal eval (bool-fix (double-rewrite eval1)))
  ;;                        (syntaxp (not (equal eval eval1))))
  ;;                   (equal (equal (bfr-eval x env) b)
  ;;                          (equal eval b)))))


  (std::defret glcp-generic-interp-bvar-alist-lookup-bfr-correct
    (b* ((fix-env (glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state))
         (p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (equal (bfr-eval (cdr (hons-assoc-equal k updates)) (car fix-env))
                      (and 
                       (bfr-varname-p k)
                       (bool-fix (glcp-generic-geval-ev (cdr (hons-assoc-equal k x))
                                                        (glcp-generic-geval-alist alist env)))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal pseudo-term-alistp
                                      equal-of-booleans-rewrite
                                      glmc-generic-interp-bvar-alist-env)
            :induct (glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state)
            :expand ((glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state)
                     (glmc-generic-interp-bvar-alist x alist pathcond config interp-st bvar-db state))
            :do-not-induct t)))

  (std::defret glcp-generic-interp-bvar-alist-bfr-eval-alist-correct
    (b* ((fix-env (glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state))
         (p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (equal (bfr-eval-alist updates (car fix-env))
                      (glcp-generic-geval-ev-bfr-update-alist x (glcp-generic-geval-alist alist env)))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal pseudo-term-alistp
                                      equal-of-booleans-rewrite
                                      glmc-generic-interp-bvar-alist-env
                                      glcp-generic-geval-ev-bfr-update-alist)
            :induct (glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state)
            :expand ((glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state)
                     (glmc-generic-interp-bvar-alist x alist pathcond config interp-st bvar-db state))
            :do-not-induct t)))

  (std::defret glcp-generic-interp-bvar-alist-constraint-correct
    (b* ((fix-env (glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state))
         (p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) (car fix-env))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal pseudo-term-alistp
                                      equal-of-booleans-rewrite
                                      glmc-generic-interp-bvar-alist-env)
            :induct (glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state)
            :expand ((glmc-generic-interp-bvar-alist-env env x alist pathcond config interp-st bvar-db state)
                     (glmc-generic-interp-bvar-alist x alist pathcond config interp-st bvar-db state))
            :do-not-induct t)))

  ;; (std::defret glcp-generic-interp-bvar-alist-lookup-bfr-correct
  ;;   (implies (and (bind-free
  ;;                  (case-match bfr-env
  ;;                    (('car env) `((env . ,env)))
  ;;                    (('bvar-db-fix-env & & & & & var-env)
  ;;                     `((env . (cons ,bfr-env ,var-env))))
  ;;                    (& '((try-other-env-bindings . try-other-env-bindings)))))
  ;;                 (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
  ;;                 (equal bfr-env (car env))
  ;;                 (bfr-hyp-eval (is-constraint interp-st) bfr-env)
  ;;                 (bfr-hyp-eval pathcond bfr-env)
  ;;                 (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
  ;;                 (acl2::interp-defs-alistp (glcp-config->overrides config))
  ;;                 (pseudo-term-alistp x)
  ;;                 (alistp alist)
  ;;                 (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                 (equal (w state0) (w state))
  ;;                 (not er))
  ;;            (equal (bfr-eval (cdr (hons-assoc-equal k updates)) bfr-env)
  ;;                   (and 
  ;;                    (bfr-varname-p k)
  ;;                    (bool-fix (glcp-generic-geval-ev (cdr (hons-assoc-equal k x))
  ;;                                                     (glcp-generic-geval-alist alist env))))))
  ;;   :hints(("Goal" :in-theory (enable hons-assoc-equal pseudo-term-alistp
  ;;                                     equal-of-booleans-rewrite)
  ;;           :induct t :do-not-induct t)))


  ;; (std::defret glcp-generic-interp-bvar-alist-bfr-eval-alist-correct
  ;;   (implies (and (bind-free
  ;;                  (case-match bfr-env
  ;;                    (('car env) `((env . ,env)))
  ;;                    (('bvar-db-fix-env & & & & & var-env)
  ;;                     `((env . (cons ,bfr-env ,var-env))))
  ;;                    (& '((try-other-env-bindings . try-other-env-bindings)))))
  ;;                 (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
  ;;                 (equal bfr-env (car env))
  ;;                 (bfr-hyp-eval (is-constraint interp-st) bfr-env)
  ;;                 (bfr-hyp-eval pathcond bfr-env)
  ;;                 (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
  ;;                 (acl2::interp-defs-alistp (glcp-config->overrides config))
  ;;                 (pseudo-term-alistp x)
  ;;                 (alistp alist)
  ;;                 (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                 (equal (w state0) (w state))
  ;;                 (not er))
  ;;            (equal (bfr-eval-alist updates bfr-env)
  ;;                   (glcp-generic-geval-ev-bfr-update-alist x (glcp-generic-geval-alist alist env))))
  ;;   :hints(("Goal" :in-theory (enable glcp-generic-geval-ev-bfr-update-alist
  ;;                                     pseudo-term-alistp
  ;;                                     equal-of-booleans-rewrite)
  ;;           :induct t :do-not-induct t)))

  ;; (std::defret glcp-generic-interp-bvar-alist-constraint-correct
  ;;   (implies (and (bind-free
  ;;                  (case-match bfr-env
  ;;                    (('car env) `((env . ,env)))
  ;;                    (('bvar-db-fix-env & & & & & var-env)
  ;;                     `((env . (cons ,bfr-env ,var-env))))
  ;;                    (& '((try-other-env-bindings . try-other-env-bindings)))))
  ;;                 (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
  ;;                 (equal bfr-env (car env))
  ;;                 (bfr-hyp-eval (is-constraint interp-st) bfr-env)
  ;;                 (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
  ;;                 (acl2::interp-defs-alistp (glcp-config->overrides config))
  ;;                 (pseudo-term-alistp x) (alistp alist)
  ;;                 (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                 (equal (w state0) (w state)))
  ;;            (bfr-hyp-eval (nth *is-constraint* new-interp-st) bfr-env))
  ;;   :hints(("Goal" :induct t :expand ((pseudo-term-alistp x)))))

  
  

  (local (in-theory (enable hyp-tuplelist-alists-bounded)))

  (std::defret glcp-generic-interp-bvar-alist-vars-bounded
    (b* (((glcp-config config)))
      (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bfr-vars-bounded k p)
                    (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                    (equal nn (next-bvar$a new-bvar-db))
                    (equal p config.param-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k p alist))
               (and (pbfr-list-vars-bounded k p (alist-vals updates))
                    (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                             (bfr-constr-vars-bounded k p (nth *is-constraint* new-interp-st)))
                    (bvar-db-vars-bounded k p nn new-bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* new-interp-st)))))
    :hints(("Goal" :in-theory (enable alist-vals))))

  (std::defret glcp-generic-interp-bvar-alist-vars-bounded-aig-mode
    (b* (((glcp-config config)))
      (implies (and (equal nn (next-bvar$a new-bvar-db))
                    (equal p config.param-bfr)
                    (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bfr-vars-bounded k p)
                    (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k p alist)
                    (bfr-mode))
               (and (pbfr-list-vars-bounded k t (alist-vals updates))
                    (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                             (bfr-constr-vars-bounded k t (nth *is-constraint* new-interp-st)))
                    (bvar-db-vars-bounded k t nn new-bvar-db)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* new-interp-st)))))
    :hints (("goal" :use ((:instance glcp-generic-interp-bvar-alist-vars-bounded))
             :in-theory (disable glcp-generic-interp-bvar-alist-vars-bounded
                                 glmc-generic-interp-bvar-alist))))

  (std::defret glcp-generic-interp-bvar-alist-bvar-db-ordered
    (b* (((glcp-config config))
         (k (next-bvar$a bvar-db)))
      (implies (and (gobj-alist-vars-bounded k p alist)
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (equal p config.param-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st)))
               (bvar-db-orderedp p new-bvar-db))))

  (std::defret glcp-generic-interp-bvar-alist-bvar-db-ordered-aig-mode
    (b* (((glcp-config config))
         (k (next-bvar$a bvar-db)))
      (implies (and (equal p config.param-bfr)
                    (gobj-alist-vars-bounded k p alist)
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (bfr-mode))
               (bvar-db-orderedp t new-bvar-db)))
    :hints (("goal" :in-theory (disable glcp-generic-interp-bvar-alist-bvar-db-ordered
                                        glmc-generic-interp-bvar-alist)
             :use ((:instance glcp-generic-interp-bvar-alist-bvar-db-ordered)))))

  (std::defret glcp-generic-interp-bvar-alist-lookup-under-iff
    (implies (not er)
             (iff (hons-assoc-equal k updates)
                  (and (bfr-varname-p k)
                       (hons-assoc-equal k x))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (std::defret alist-keys-of-glcp-generic-interp-bvar-alist
    (implies (and (not er)
                  (bfr-varnamelist-p (alist-keys x)))
             (equal (alist-keys updates) (alist-keys x)))
    :hints(("Goal" :in-theory (enable alist-keys))))

  (std::defret glcp-generic-interp-bvar-alist-lookup-bfr-correct-no-new-bvars
    (b* ((p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (equal (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (equal (bfr-eval (cdr (hons-assoc-equal k updates)) (car env))
                      (and 
                       (bfr-varname-p k)
                       (bool-fix (glcp-generic-geval-ev (cdr (hons-assoc-equal k x))
                                                        (glcp-generic-geval-alist alist env)))))))
    :hints (("Goal" :use ((:instance glcp-generic-interp-bvar-alist-lookup-bfr-correct))
             :in-theory (disable glcp-generic-interp-bvar-alist-lookup-bfr-correct
                                 glmc-generic-interp-bvar-alist))))

  (std::defret glcp-generic-interp-bvar-alist-bfr-eval-alist-correct-no-new-bvars
    (b* ((p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (equal (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (equal (bfr-eval-alist updates (car env))
                      (glcp-generic-geval-ev-bfr-update-alist x (glcp-generic-geval-alist alist env)))))
    :hints (("Goal" :use ((:instance glcp-generic-interp-bvar-alist-bfr-eval-alist-correct))
             :in-theory (disable glcp-generic-interp-bvar-alist-bfr-eval-alist-correct
                                 glmc-generic-interp-bvar-alist))))

  (std::defret glcp-generic-interp-bvar-alist-constraint-correct-no-new-bvars
    (b* ((p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (equal (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) (car env))))
    :hints (("Goal" :use ((:instance glcp-generic-interp-bvar-alist-constraint-correct))
             :in-theory (disable glcp-generic-interp-bvar-alist-constraint-correct
                                 glmc-generic-interp-bvar-alist)))))


(define glmc-generic-interp-gvar-alist-env (env x alist pathcond config interp-st bvar-db state)
  :non-executable t
  :verify-guards nil
  :measure (len x)
  :returns (new-env)
  (b* (((when (atom x)) env)
       ((unless (mbt (and (consp (car x)))))
        (glmc-generic-interp-gvar-alist-env env (cdr x) alist pathcond config interp-st bvar-db state))
       ((cons ?var term) (car x))
       ((mv ?bfr ?er pathcond interp-st new-bvar-db state)
        (glcp-generic-interp-term-equivs
         term alist nil pathcond (glcp-config->concl-clk config) config interp-st bvar-db state))
       (env (cons (bvar-db-fix-env (next-bvar$a new-bvar-db)
                                   (next-bvar$a bvar-db)
                                   new-bvar-db t (car env) (cdr env))
                  (cdr env))))
    (glmc-generic-interp-gvar-alist-env env (cdr x) alist pathcond config interp-st new-bvar-db state))
  ///
  (std::defret glmc-generic-interp-gvar-alist-env-eval-vars-bounded
    (implies (and (pbfr-vars-bounded (next-bvar$a bvar-db) t q)
                  (bfr-mode))
             (equal (bfr-eval q (car new-env))
                    (bfr-eval q (car env)))))

  (defthm glmc-generic-interp-gvar-alist-env-eval-gobj-vars-bounded
    (implies (and (gobj-vars-bounded (next-bvar$a bvar-db) t q)
                  (bfr-mode))
             (equal (glcp-generic-geval q (glmc-generic-interp-gvar-alist-env
                                           env x alist pathcond config interp-st bvar-db state))
                    (glcp-generic-geval q env)))
    :hints(("Goal" :in-theory (enable GLCP-GENERIC-GEVAL-NORMALIZE-CONS-CAR-CDR-ENV))))

  (defthm glmc-generic-interp-gvar-alist-env-geval-alist-gobj-vars-bounded
    (implies (and (gobj-alist-vars-bounded (next-bvar$a bvar-db) t q)
                  (bfr-mode))
             (equal (glcp-generic-geval-alist q (glmc-generic-interp-gvar-alist-env
                                           env x alist pathcond config interp-st bvar-db state))
                    (glcp-generic-geval-alist q env)))
    :hints(("Goal" :in-theory (e/d (gobj-alist-vars-bounded glcp-generic-geval-alist)
                                   (glmc-generic-interp-gvar-alist-env)))))

  (std::defret glmc-generic-interp-gvar-alist-env-bfr-hyp-eval-vars-bounded
    (implies (and (bfr-constr-vars-bounded (next-bvar$a bvar-db) t q)
                  (bfr-mode))
             (equal (bfr-hyp-eval q (car new-env))
                    (bfr-hyp-eval q (car env))))))


(defsection glmc-generic-interp-gvar-alist
  (local (in-theory (enable glmc-generic-interp-gvar-alist)))
  (local (std::set-define-current-function glmc-generic-interp-gvar-alist))
  (verify-guards glmc-generic-interp-gvar-alist
    :hints(("Goal" :in-theory (enable pseudo-term-alistp))))

  (std::defret glmc-generic-interp-gvar-alist-new-pathcond
    (equal new-pathcond (bfr-hyp-fix pathcond)))

  (std::defret w-state-preserved-of-glcp-generic-interp-gvar-alist
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glcp-generic-interp-gvar-alist
    (implies (state-p1 state) (state-p1 new-state)))

  (std::defret bvar-db-extension-p-of-glcp-generic-interp-gvar-alist
    (bvar-db-extension-p new-bvar-db bvar-db))

  (std::defret interp-st-obligs-extension-p-of-glcp-generic-interp-gvar-alist
    (interp-st-obligs-extension-p new-interp-st interp-st))

;; (define glmc-generic-interp-gvar-alist ((x pseudo-term-alistp)
;;                                         (alist)
;;                                         pathcond
;;                                         (config glcp-config-p)
;;                                         interp-st
;;                                         bvar-db
;;                                         state)

;;   :guard (b* (((glcp-config config)))
;;            (and (acl2::interp-defs-alistp config.overrides)
;;                 (acl2::interp-defs-alistp (is-obligs interp-st))
;;                 (variable-listp (alist-keys x))))
;;   :returns (mv (updates gobj-alistp :hyp (variable-listp (alist-keys x)))
;;                er 
;;                (new-pathcond (equal new-pathcond (bfr-hyp-fix pathcond)))
;;                new-interp-st
;;                new-bvar-db
;;                new-state)
;;   :guard-hints (("goal" :in-theory (enable pseudo-term-alistp)))
;;   (b* (((when (atom x))
;;         (b* ((pathcond (lbfr-hyp-fix pathcond)))
;;           (mv nil nil pathcond interp-st bvar-db state)))
;;        ((unless (mbt (and (consp (car x)))))
;;         (glmc-generic-interp-gvar-alist
;;          (cdr x) alist pathcond config interp-st bvar-db state))
;;        ((cons var term) (car x))
;;        ((mv bfr er pathcond interp-st bvar-db state)
;;         (glcp-generic-interp-term-equivs
;;          term alist nil pathcond (glcp-config->concl-clk config) config interp-st bvar-db state))
;;        ((when er) (mv nil er pathcond interp-st bvar-db state))
;;        ((mv rest er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-gvar-alist (cdr x) alist pathcond config interp-st bvar-db state)))
;;     (mv (and (not er) (cons (cons var bfr) rest))
;;         er pathcond interp-st bvar-db state))
;;   ///
  
  (std::defret interp-defs-of-glcp-generic-interp-gvar-alist
    (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                  (acl2::interp-defs-alistp (glcp-config->overrides config))
                  (pseudo-term-alistp x))
             (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st)))
    :hints(("Goal" :in-theory (enable pseudo-term-alistp))))

  (std::defret glcp-generic-interp-gvar-alist-accs-ok
    (implies (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
             (glcp-interp-accs-ok interp-st bvar-db config env))
    :rule-classes :forward-chaining)


  (std::defret glcp-generic-interp-gvar-alist-lookup-correct
    (b* ((fix-env (glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state))
         (p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    ;; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (acl2::interp-defs-alistp (glcp-config->overrides config))
                    ;; (pseudo-term-alistp x)
                    ;; (alistp alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (equal (glcp-generic-geval (cdr (hons-assoc-equal k updates)) fix-env)
                      (glcp-generic-geval-ev (cdr (hons-assoc-equal k x))
                                             (glcp-generic-geval-alist alist env)))))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal pseudo-term-alistp
                                      equal-of-booleans-rewrite
                                      glmc-generic-interp-gvar-alist-env)
                                   ;; (obligs-clauses-theoremp-when-extension)
                                   )
            :induct (glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state)
            :expand ((glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state)
                     (glmc-generic-interp-gvar-alist x alist pathcond config interp-st bvar-db state))
            :do-not-induct t)
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable obligs-clauses-theoremp-when-extension
           ;;                           hons-assoc-equal pseudo-term-alistp
           ;;                           equal-of-booleans-rewrite
           ;;                           glmc-generic-interp-gvar-alist-env)))
           ))

  (std::defret glcp-generic-interp-gvar-alist-geval-alist-correct
    (b* ((fix-env (glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state))
         (p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    ;; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (acl2::interp-defs-alistp (glcp-config->overrides config))
                    ;; (pseudo-term-alistp x)
                    ;; (alistp alist)
                    (alistp x)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (equal (glcp-generic-geval-alist updates fix-env)
                      (glcp-generic-geval-ev-alist x (glcp-generic-geval-alist alist env)))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal pseudo-term-alistp
                                      equal-of-booleans-rewrite
                                      glmc-generic-interp-gvar-alist-env
                                      glcp-generic-geval-ev-bfr-update-alist)
            :induct (glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state)
            :expand ((glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state)
                     (glmc-generic-interp-gvar-alist x alist pathcond config interp-st bvar-db state)
                     (:free (env) (glcp-generic-geval-alist nil env)))
            :do-not-induct t)))

  (std::defret glcp-generic-interp-gvar-alist-constraint-correct
    (b* ((fix-env (glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state))
         (p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    ;; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (acl2::interp-defs-alistp (glcp-config->overrides config))
                    ;; (pseudo-term-alistp x)
                    ;; (alistp alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) (car fix-env))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal pseudo-term-alistp
                                      equal-of-booleans-rewrite
                                      glmc-generic-interp-gvar-alist-env)
            :induct (glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state)
            :expand ((glmc-generic-interp-gvar-alist-env env x alist pathcond config interp-st bvar-db state)
                     (glmc-generic-interp-gvar-alist x alist pathcond config interp-st bvar-db state))
            :do-not-induct t)))

  ;; (local (defthm equal-of-bfr-eval-rewrite-under-iff
  ;;          (implies (and (equal eval1 (bfr-eval x env))
  ;;                        (equal eval (bool-fix (double-rewrite eval1)))
  ;;                        (syntaxp (not (equal eval eval1))))
  ;;                   (equal (equal (bfr-eval x env) b)
  ;;                          (equal eval b)))))

  ;; (std::defret glcp-generic-interp-gvar-alist-lookup-correct
  ;;   (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
  ;;                 (equal bfr-env (car env))
  ;;                 (bfr-hyp-eval (is-constraint interp-st) bfr-env)
  ;;                 (bfr-hyp-eval pathcond bfr-env)
  ;;                 (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
  ;;                 (acl2::interp-defs-alistp (glcp-config->overrides config))
  ;;                 (pseudo-term-alistp x)
  ;;                 (alistp alist)
  ;;                 (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                 (equal (w state0) (w state))
  ;;                 (not er))
  ;;            (equal (glcp-generic-geval (cdr (hons-assoc-equal k updates)) env)
  ;;                   (glcp-generic-geval-ev (cdr (hons-assoc-equal k x))
  ;;                                          (glcp-generic-geval-alist alist env))))
  ;;   :hints(("Goal" :in-theory (enable hons-assoc-equal pseudo-term-alistp)
  ;;           :induct t :do-not-induct t)))

  ;; (std::defret glcp-generic-geval-alist-of-glcp-generic-interp-gvar-alist
  ;;   (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
  ;;                 (equal bfr-env (car env))
  ;;                 (bfr-hyp-eval (is-constraint interp-st) bfr-env)
  ;;                 (bfr-hyp-eval pathcond bfr-env)
  ;;                 (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
  ;;                 (acl2::interp-defs-alistp (glcp-config->overrides config))
  ;;                 (pseudo-term-alistp x)
  ;;                 (alistp alist)
  ;;                 (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                 (equal (w state0) (w state))
  ;;                 (not er))
  ;;            (equal (glcp-generic-geval-alist updates env)
  ;;                   (glcp-generic-geval-ev-alist x (glcp-generic-geval-alist alist env))))
  ;;   :hints(("Goal" :in-theory (enable glcp-generic-geval-alist glcp-generic-geval-ev-alist
  ;;                                     pseudo-term-alistp))))

  ;; (std::defret glcp-generic-interp-gvar-alist-constraint-correct
  ;;   (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
  ;;                 (equal bfr-env (car env))
  ;;                 (bfr-hyp-eval (is-constraint interp-st) bfr-env)
  ;;                 (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
  ;;                 (acl2::interp-defs-alistp (glcp-config->overrides config))
  ;;                 (pseudo-term-alistp x) (alistp alist)
  ;;                 (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                 (equal (w state0) (w state)))
  ;;            (bfr-hyp-eval (nth *is-constraint* new-interp-st) bfr-env))
  ;;   :hints(("Goal" :induct t :expand ((pseudo-term-alistp x)))))

  


  (local (in-theory (enable hyp-tuplelist-alists-bounded)))

  (std::defret glcp-generic-interp-gvar-alist-vars-bounded
    (b* (((glcp-config config)))
      (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bfr-vars-bounded k p)
                    (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                    (equal nn (next-bvar$a new-bvar-db))
                    (equal p config.param-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k p alist))
               (and (gobj-alist-vars-bounded k p updates)
                    (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                             (bfr-constr-vars-bounded k p (nth *is-constraint* new-interp-st)))
                    (bvar-db-vars-bounded k p nn new-bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* new-interp-st)))))
    :hints(("Goal" :in-theory (enable alist-vals))))

  (std::defret glcp-generic-interp-gvar-alist-bvar-db-ordered
    (b* (((glcp-config config))
         (k (next-bvar$a bvar-db)))
      (implies (and (gobj-alist-vars-bounded k p alist)
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (equal p config.param-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st)))
               (bvar-db-orderedp p new-bvar-db))))

  (std::defret glcp-generic-interp-gvar-alist-vars-bounded-aig-mode
    (b* (((glcp-config config)))
      (implies (and (equal nn (next-bvar$a new-bvar-db))
                    (equal p config.param-bfr)
                    (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bfr-vars-bounded k p)
                    (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (gobj-alist-vars-bounded k p alist)
                    (bfr-mode))
               (and (gobj-alist-vars-bounded k t updates)
                    (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                             (bfr-constr-vars-bounded k t (nth *is-constraint* new-interp-st)))
                    (bvar-db-vars-bounded k t nn new-bvar-db)
                    (gbc-db-vars-bounded k t (nth *is-constraint-db* new-interp-st)))))
    :hints(("Goal" :in-theory (disable glcp-generic-interp-gvar-alist-vars-bounded
                                       glmc-generic-interp-gvar-alist)
            :use glcp-generic-interp-gvar-alist-vars-bounded)))

  (std::defret glcp-generic-interp-gvar-alist-bvar-db-ordered-aig-mode
    (b* (((glcp-config config))
         (k (next-bvar$a bvar-db)))
      (implies (and (equal p config.param-bfr)
                    (gobj-alist-vars-bounded k p alist)
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (bfr-mode))
               (bvar-db-orderedp t new-bvar-db)))
    :hints (("goal" :in-theory (disable glcp-generic-interp-gvar-alist-bvar-db-ordered
                                        glmc-generic-interp-gvar-alist)
             :use glcp-generic-interp-gvar-alist-bvar-db-ordered)))

  (std::defret alist-keys-of-glcp-generic-interp-gvar-alist
    (implies (not er)
             (equal (alist-keys updates)
                    (alist-keys x))))


  (std::defret glcp-generic-interp-gvar-alist-lookup-correct-no-new-bvars
    (b* ((p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (equal (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    ;; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (acl2::interp-defs-alistp (glcp-config->overrides config))
                    ;; (pseudo-term-alistp x)
                    ;; (alistp alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (equal (glcp-generic-geval (cdr (hons-assoc-equal k updates)) env)
                      (glcp-generic-geval-ev (cdr (hons-assoc-equal k x))
                                             (glcp-generic-geval-alist alist env)))))
    :hints (("goal" :in-theory (disable glcp-generic-interp-gvar-alist-lookup-correct
                                        glmc-generic-interp-gvar-alist)
             :use glcp-generic-interp-gvar-alist-lookup-correct)))

  (std::defret glcp-generic-interp-gvar-alist-geval-alist-correct-no-new-bvars
    (b* ((p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (equal (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    ;; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (acl2::interp-defs-alistp (glcp-config->overrides config))
                    ;; (pseudo-term-alistp x)
                    ;; (alistp alist)
                    (alistp x)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (equal (glcp-generic-geval-alist updates env)
                      (glcp-generic-geval-ev-alist x (glcp-generic-geval-alist alist env)))))
    :hints (("goal" :in-theory (disable glcp-generic-interp-gvar-alist-geval-alist-correct
                                        glmc-generic-interp-gvar-alist)
             :use glcp-generic-interp-gvar-alist-geval-alist-correct)))

  (std::defret glcp-generic-interp-gvar-alist-constraint-correct-no-new-bvars
    (b* ((p (glcp-config->param-bfr config))
         (bfr-env (car env)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (equal (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    ;; (bfr-hyp-eval pathcond bfr-env)
                    (bfr-eval p bfr-env)
                    ;; (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    ;; (acl2::interp-defs-alistp (glcp-config->overrides config))
                    ;; (pseudo-term-alistp x)
                    ;; (alistp alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bvar-db-orderedp p bvar-db)
                    (gobj-alist-vars-bounded (next-bvar$a bvar-db) p alist)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) p (nth *is-constraint-db* interp-st))
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) p pathcond)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t p)
                    (bfr-mode))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) (car env))))
    :hints (("goal" :in-theory (disable glcp-generic-interp-gvar-alist-constraint-correct
                                        glmc-generic-interp-gvar-alist)
             :use glcp-generic-interp-gvar-alist-constraint-correct))))




(defsection glmc-gobj-to-term

  (flag::make-flag glmc-gobj-to-term-flag glmc-gobj-to-term :local t)

  (local (defthm assoc-when-key-nonnil
           (implies key
                    (equal (assoc key a)
                           (hons-assoc-equal key a)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (defthm-glmc-gobj-to-term-flag
    (defthm glcp-generic-geval-ev-of-glmc-gobj-to-term
      (b* (((mv er term) (glmc-gobj-to-term x)))
        (implies (and (not er)
                      (equal a (cdr env)))
                 (equal (glcp-generic-geval-ev term a)
                        (glcp-generic-geval x env))))
      :hints ('(:expand ((glmc-gobj-to-term x))
                :in-theory (enable GENERAL-CONCRETE-OBJ-CORRECT))
              (and stable-under-simplificationp
                   '(:expand ((:with glcp-generic-geval (glcp-generic-geval x env)))
                     :in-theory (enable glcp-generic-geval-ev-of-fncall-args))))
      :flag glmc-gobj-to-term)
    (defthm glcp-generic-geval-ev-of-glmc-gobj-list-to-terms
      (b* (((mv er terms) (glmc-gobj-list-to-terms x)))
        (implies (and (not er)
                      (equal a (cdr env)))
                 (equal (glcp-generic-geval-ev-lst terms a)
                        (glcp-generic-geval-list x env))))
      :hints ('(:expand ((glcp-generic-geval-list x env)
                         (glmc-gobj-list-to-terms x))))
      :flag glmc-gobj-list-to-terms))

  (defthm-glmc-gobj-to-term-flag
    (defthm glcp-generic-geval-normalize-env-when-glmc-gobj-to-term
      (b* (((mv er ?term) (glmc-gobj-to-term x)))
        (implies (and (syntaxp (not (equal bfr-env ''nil)))
                      (not er))
                 (equal (glcp-generic-geval x (cons bfr-env var-env))
                        (glcp-generic-geval x (cons nil var-env)))))
      :hints ('(:expand ((glmc-gobj-to-term x))
                :in-theory (enable GENERAL-CONCRETE-OBJ-CORRECT))
              (and stable-under-simplificationp
                   '(:expand ((:with glcp-generic-geval (:free (env) (glcp-generic-geval x env))))
                     :in-theory (enable glcp-generic-geval-ev-of-fncall-args))))
      :flag glmc-gobj-to-term)
    (defthm glcp-generic-geval-normalize-env-when-glmc-gobj-list-to-terms
      (b* (((mv er ?terms) (glmc-gobj-list-to-terms x)))
        (implies (and (syntaxp (not (equal bfr-env ''nil)))
                      (not er))
                 (equal (glcp-generic-geval-list x (cons bfr-env var-env))
                        (glcp-generic-geval-list x (cons nil var-env)))))
      :hints ('(:expand ((glcp-generic-geval-list x env)
                         (glmc-gobj-list-to-terms x))))
      :flag glmc-gobj-list-to-terms))

  (in-theory (disable glcp-generic-geval-normalize-env-when-glmc-gobj-to-term
                      glcp-generic-geval-normalize-env-when-glmc-gobj-list-to-terms))

  (defthm glcp-generic-geval-ev-of-glmc-gobj-to-term-of-cdr-env
    (b* (((mv er term) (glmc-gobj-to-term x)))
        (implies (not er)
                 (equal (glcp-generic-geval-ev term (cdr env))
                        (glcp-generic-geval x env))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-of-glmc-gobj-to-term
                           (a (cdr env))))
             :in-theory (disable glcp-generic-geval-ev-of-glmc-gobj-to-term))))

  (defthm glcp-generic-geval-ev-of-glmc-gobj-to-term-default-env
    (b* (((mv er term) (glmc-gobj-to-term x)))
        (implies (not er)
                 (equal (glcp-generic-geval-ev term env)
                        (glcp-generic-geval x (cons nil env)))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-of-glmc-gobj-to-term
                           (a env) (env (cons nil env))))
             :in-theory (disable glcp-generic-geval-ev-of-glmc-gobj-to-term))))

  (local (defthm-gobj-flag
           (defthm gobj-to-param-space-when-general-concretep
             (implies (general-concretep x)
                      (equal (gobj-to-param-space x p) x))
             :hints('(:expand ((gobj-to-param-space x p))
                      :in-theory (enable gl-cons))
                    (and stable-under-simplificationp
                         '(:in-theory (enable g-keyword-symbolp tag))))
             :flag gobj)
           :skip-others t))

  ;; (defthmd glmc-gobj-to-term-of-gobj-to-param-space-no-error-implies-bfr-independent
  ;;   (b* (((mv er ?term) (glmc-gobj-to-term (gobj-to-param-space x p))))
  ;;     (implies (and (not er)
  ;;                   (syntaxp (not (equal bfr-env1 `(bfr-unparam-env ,p 'nil))))
  ;;                   (bfr-eval p bfr-env1) 
  ;;                   ;; (bfr-eval p bfr-env2)
  ;;                   )
  ;;              (equal (glcp-generic-geval x (cons bfr-env1 var-env))
  ;;                     (glcp-generic-geval x (cons (bfr-unparam-env p nil) var-env)))))
  ;;   :hints (("goal" :use ((:instance glcp-generic-geval-normalize-env-when-glmc-gobj-to-term
  ;;                          (x (gobj-to-param-space x p))
  ;;                          (bfr-env (bfr-param-env p bfr-env1)))
  ;;                         (:instance glcp-generic-geval-normalize-env-when-glmc-gobj-to-term
  ;;                          (x (gobj-to-param-space x p))
  ;;                          (bfr-env nil)))
  ;;            :in-theory (e/d (genv-unparam) (glcp-generic-geval-normalize-env-when-glmc-gobj-to-term)))))

  )

(defsection glmc-bvar-db-to-state-updates
  (local (in-theory (enable glmc-bvar-db-to-state-updates)))
  (local (std::set-define-current-function glmc-bvar-db-to-state-updates))
  (verify-guards glmc-bvar-db-to-state-updates)

;; (define glmc-bvar-db-to-state-updates ((idx natp)
;;                                        (state-vars variable-listp)
;;                                        bvar-db)
;;     :guard (and (<= (base-bvar bvar-db) idx)
;;                 (<= idx (next-bvar bvar-db)))
;;     :measure (nfix (- (next-bvar bvar-db) (nfix idx)))
;;     :returns (updates pseudo-term-alistp)
;;     (b* ((idx (lnfix idx))
;;          ((when (mbe :logic (zp (- (next-bvar bvar-db) idx))
;;                      :exec (eql (next-bvar bvar-db) idx)))
;;           nil)
;;          (gobj (get-bvar->term idx bvar-db))
;;          (vars (gobj-vars gobj))
;;          (state-bitp (acl2::hons-intersect-p vars state-vars))
;;          ((unless state-bitp)
;;           (glmc-bvar-db-to-state-updates (1+ idx) state-vars bvar-db))
;;          ((mv to-term-er term) (glmc-gobj-to-term gobj))
;;          (bad-state-vars (acl2::hons-set-diff vars state-vars))
;;          ((when bad-state-vars)
;;           (cw "Warning: The following term containing both state and input ~
;;              variables was turned into a symbolic bit.  In the Boolean model ~
;;              it will be treated as an input, which may lead to false ~
;;              counterexamples:~%~x0~%" term)
;;           (glmc-bvar-db-to-state-updates (1+ idx) state-vars bvar-db))
;;          ((when to-term-er)
;;           (cw "Warning: The following term perhaps should be considered a state ~
;;              bit, but it was rejected because it ~@0. It will instead be ~
;;              treated as an input bit, which may lead to false ~
;;              counterexamples:~%~x1~%" to-term-er term)
;;           (glmc-bvar-db-to-state-updates (1+ idx) state-vars bvar-db)))
;;       (cons (cons idx term)
;;             (glmc-bvar-db-to-state-updates (1+ idx) state-vars bvar-db)))
;;     ///
    (std::defret lookup-in-glmc-bvar-db-to-state-updates
      (implies (hons-assoc-equal k updates)
               (equal (cdr (hons-assoc-equal k updates))
                      (mv-nth 1 (glmc-gobj-to-term (get-bvar->term k bvar-db)))))
      :hints(("Goal" :in-theory (enable hons-assoc-equal))))

    (std::defret lookup-in-glmc-bvar-db-implies-gobj-to-term-ok
      (implies (and (hons-assoc-equal k updates)
                    (equal (get-bvar->term$a k bvar-db1)
                           (get-bvar->term$a k bvar-db)))
               (not (mv-nth 0 (glmc-gobj-to-term (get-bvar->term$a k bvar-db1)))))
      :hints(("Goal" :in-theory (enable hons-assoc-equal))))

    (std::defret bfr-varnamelist-p-of-glmc-bvar-db-to-state-updates-keys
      (bfr-varnamelist-p (alist-keys updates)))

    (std::defret glmc-bvar-db-to-state-updates-of-extension
      (implies (and (bind-bvar-db-extension bvar-db old-bvar-db)
                    (equal (next-bvar$a bvar-db) (next-bvar$a old-bvar-db)))
               (equal updates
                      (glmc-bvar-db-to-state-updates idx state-vars old-bvar-db))))

    (std::defret nat-listp-alist-keys-of-glmc-bvar-db-to-state-updates
      (nat-listp (alist-keys updates))
      :hints(("Goal" :in-theory (enable alist-keys))))

    (std::defret bfr-varlist-bounded-of-keys-of-glmc-bvar-db-to-state-updates
      (implies (<= (next-bvar$a bvar-db) (nfix n))
               (bfr-varlist-bounded n (alist-keys updates)))
      :hints(("Goal" :in-theory (enable alist-keys bfr-varlist-bounded)))))


;; (define glmc-generic-bvar-db-to-updates ((idx natp)
;;                                          alist
;;                                          pathcond
;;                                          (config glcp-config-p)
;;                                          interp-st
;;                                          bvar-db
;;                                          state)
;;   :guard (b* (((glcp-config config)))
;;            (and (acl2::interp-defs-alistp config.overrides)
;;                 (acl2::interp-defs-alistp (is-obligs interp-st))
;;                 (<= (base-bvar bvar-db) idx)
;;                 (<= idx (next-bvar bvar-db))))
;;   :measure (nfix (- (next-bvar bvar-db) (nfix idx)))
;;   :returns (mv (updates bfr-updates-p)
;;                er
;;                (new-pathcond (equal new-pathcond (bfr-hyp-fix pathcond)))
;;                new-interp-st new-bvar-db new-state)
;;   (b* ((idx (lnfix idx))
;;        (next-bvar (next-bvar bvar-db))
;;        ((when (mbe :logic (zp (- (next-bvar bvar-db) idx))
;;                    :exec (eql (next-bvar bvar-db) idx)))
;;         (b* ((pathcond (lbfr-hyp-fix pathcond)))
;;           (mv nil nil pathcond interp-st bvar-db state)))
;;        (gobj (get-bvar->term idx bvar-db))
;;        (vars (gobj-vars gobj))
;;        (state-bitp (acl2::hons-intersect-p1 vars alist))
;;        ((unless state-bitp)
;;         (glmc-generic-bvar-db-to-updates (1+ idx) alist pathcond config interp-st bvar-db state))
;;        ((mv to-term-er term) (glmc-gobj-to-term gobj))
;;        (bad-state-vars (acl2::hons-sd1 vars alist))
;;        ((when bad-state-vars)
;;         (cw "Warning: The following term containing both state and input ~
;;              variables was turned into a symbolic bit.  In the Boolean model ~
;;              it will be treated as an input, which may lead to false ~
;;              counterexamples:~%~x0~%" term)
;;         (glmc-generic-bvar-db-to-updates (1+ idx) alist pathcond config interp-st bvar-db state))
;;        ((when to-term-er)
;;         (cw "Warning: The following term perhaps should be considered a state ~
;;              bit, but it was rejected because it ~@0. It will instead be ~
;;              treated as an input bit, which may lead to false ~
;;              counterexamples:~%~x1~%" to-term-er term)
;;         (glmc-generic-bvar-db-to-updates (1+ idx) alist pathcond config interp-st bvar-db state))
;;        ((glcp-config config))
;;        ((mv bfr er pathcond interp-st bvar-db state)
;;         (glcp-generic-interp-test term alist pathcond config.hyp-clk config interp-st bvar-db state))
;;        ((unless (equal next-bvar (next-bvar bvar-db)))
;;         (mv nil
;;             (msg "Programming error: added Boolean variables to the database while
;;                   computing state updates.  Term: ~x0" term)
;;             pathcond interp-st bvar-db state))
;;        ((when er)
;;         (cw "Warning: The following term perhaps should be considered a state ~
;;              bit, but it was rejected because we encountered the following ~
;;              error while composing it with the state update function: ~@0. It ~
;;              will instead be treated as an input bit, which may lead to false ~
;;              counterexamples:~%~x1~%" er term)
;;         (glmc-generic-bvar-db-to-updates (1+ idx) alist pathcond config interp-st bvar-db state))
;;        ((mv updates er pathcond interp-st bvar-db state)
;;         (glmc-generic-bvar-db-to-updates (1+ idx) alist pathcond config interp-st bvar-db state)))
;;     (mv (cons (cons idx bfr) updates)
;;         er pathcond interp-st bvar-db state))
;;   ///
;;   (std::defret interp-defs-of-glmc-generic-bvar-db-to-updates
;;     (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
;;                   (acl2::interp-defs-alistp (glcp-config->overrides config)))
;;              (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st))))

  

;;   (std::defret glcp-generic-bvar-db-to-updates-accs-ok
;;     (implies (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
;;              (glcp-interp-accs-ok interp-st bvar-db config env))
;;     :rule-classes :forward-chaining)

;;   ;; (local (defthm equal-of-bfr-eval-rewrite-under-iff
;;   ;;          (implies (and (equal eval1 (bfr-eval x env))
;;   ;;                        (equal eval (bool-fix (double-rewrite eval1)))
;;   ;;                        (syntaxp (not (equal eval eval1))))
;;   ;;                   (equal (equal (bfr-eval x env) b)
;;   ;;                          (equal eval b)))))

;;   (std::defret glcp-generic-bvar-db-to-updates-lookup-correct
;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
;;                   (equal bfr-env (car env))
;;                   (bfr-hyp-eval (is-constraint interp-st) bfr-env)
;;                   (bfr-hyp-eval pathcond bfr-env)
;;                   (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
;;                   (acl2::interp-defs-alistp (glcp-config->overrides config))
;;                   (alistp alist)
;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
;;                   (equal (w state0) (w state))
;;                   (hons-assoc-equal k updates))
;;              (equal (bfr-eval (cdr (hons-assoc-equal k updates)) bfr-env)
;;                     (bool-fix
;;                      (glcp-generic-geval (get-bvar->term k bvar-db) (cons nil (glcp-generic-geval-alist alist env))))))
;;     :hints(("Goal" :in-theory (enable hons-assoc-equal
;;                                       equal-of-booleans-rewrite)
;;             :induct t :do-not-induct t)))

;;   (std::defret glcp-generic-bvar-db-vars-out-of-range
;;     (implies (or (< (nfix k) (nfix idx))
;;                  (<= (next-bvar$a bvar-db) (nfix k)))
;;              (not (hons-assoc-equal k updates)))
;;     :hints(("Goal" :in-theory (enable hons-assoc-equal))))

;;   (std::defret glcp-generic-bvar-db-to-updates-constraint-correct
;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config env)
;;                   (equal bfr-env (car env))
;;                   (bfr-hyp-eval (is-constraint interp-st) bfr-env)
;;                   (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
;;                   (acl2::interp-defs-alistp (glcp-config->overrides config))
;;                   (alistp alist)
;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
;;                   (equal (w state0) (w state)))
;;              (bfr-hyp-eval (nth *is-constraint* new-interp-st) bfr-env))
;;     :hints(("Goal" :induct t :expand ((pseudo-term-alistp x)))))
  
;;   (std::defret w-state-preserved-of-glcp-generic-bvar-db-to-updates
;;     (equal (w new-state) (w state)))
  
;;   (std::defret state-p1-preserved-of-glcp-generic-bvar-db-to-updates
;;     (implies (state-p1 state) (state-p1 new-state)))

;;   (std::defret bvar-db-extension-p-of-glcp-generic-bvar-db-to-updates
;;     (bvar-db-extension-p new-bvar-db bvar-db))

;;   (std::defret next-bvar-of-glcp-generic-bvar-db-to-updates
;;     (implies (not er)
;;              (equal (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))))

;;   (std::defret glcp-generic-bvar-db-to-updates-vars-bounded
;;     (b* (((glcp-config config)))
;;       (implies (and (<= (next-bvar$a bvar-db) (nfix k))
;;                     (bfr-vars-bounded k p)
;;                     (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
;;                     (equal p config.param-bfr)
;;                     (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
;;                     (gobj-alist-vars-bounded k p alist)
;;                     (not er))
;;                (and (pbfr-list-vars-bounded k p (alist-vals updates))
;;                     (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
;;                              (bfr-constr-vars-bounded k p (nth *is-constraint* new-interp-st)))
;;                     (implies (equal nn (next-bvar$a bvar-db))
;;                              (bvar-db-vars-bounded k p nn new-bvar-db))
;;                     (gbc-db-vars-bounded k p (nth *is-constraint-db* new-interp-st)))))
;;     :hints(("Goal" :in-theory (enable alist-vals))))

;;   (std::defret glcp-generic-bvar-db-to-updates-bvar-db-ordered
;;     (b* (((glcp-config config))
;;          (k (next-bvar$a bvar-db)))
;;       (implies (and (gobj-alist-vars-bounded k p alist)
;;                     (bfr-vars-bounded k p)
;;                     (bvar-db-orderedp p bvar-db)
;;                     (bvar-db-vars-bounded k p k bvar-db)
;;                     (equal p config.param-bfr)
;;                     (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st)))
;;                (bvar-db-orderedp p new-bvar-db)))))


(defthm-shape-spec-flag
  (defthm variable-listp-of-shape-spec-vars
    (implies (shape-specp x)
             (variable-listp (shape-spec-vars x)))
    :hints ('(:expand ((shape-spec-vars x)
                       (shape-specp x))))
    :flag ss)
  (defthm variable-listp-of-shape-spec-list-vars
    (implies (shape-spec-listp x)
             (variable-listp (shape-spec-list-vars x)))
    :hints ('(:expand ((shape-spec-list-vars x)
                       (shape-spec-listp x))))
    :flag list))


(define glmc-generic-state-bvar-as-function-of-state ((k natp)
                                                      (st "An actual value of the state object")
                                                      (config glmc-config-p)
                                                      bvar-db)
  :non-executable t
  :verify-guards nil
  (b* (((glmc-config+ config))
       (st-shape-spec (cadr (hons-assoc-equal config.st-var config.shape-spec-alist)))
       ((mv bvar-bindings gvar-bindings) (shape-spec-invert st-shape-spec config.st-var))
       (bvar-bindings-look (hons-assoc-equal k bvar-bindings))
       (st-alist `((,config.st-var . ,st)))
       ((when bvar-bindings-look)
        (bool-fix (glcp-generic-geval-ev (cdr bvar-bindings-look) st-alist)))
       (gvar-bindings (glcp-generic-geval-ev-alist gvar-bindings st-alist)))
    (bool-fix (glcp-generic-geval (get-bvar->term k bvar-db) (cons nil gvar-bindings)))))

(define glmc-generic-state-bvars ((config glmc-config-p)
                                  bvar-db)
  :returns (statebits nat-listp :hyp :guard)
  :non-executable t
  :verify-guards nil
  (b* (((glmc-config+ config))
       (st-shape-spec (cadr (hons-assoc-equal config.st-var config.shape-spec-alist)))
       ((mv bvar-bindings ?gvar-bindings) (shape-spec-invert st-shape-spec config.st-var))
       ;;(bvar-bindings-eval (glcp-generic-geval-ev-bfr-update-alist bvar-bindings st-alist))
       ;; (gvar-bindings-eval (glcp-generic-geval-ev-alist gvar-bindings st-alist))
       (bvar-db-alist (glmc-bvar-db-to-state-updates (base-bvar bvar-db)
                                                     (alist-keys gvar-bindings)
                                                     bvar-db)))
    (append (alist-keys bvar-bindings)
            (alist-keys bvar-db-alist)))
  ///
  (defthm glmc-generic-state-bvars-of-similar-bvar-db
    (implies (and (bind-bvar-db-extension bvar-db old-bvar-db)
                  (equal (next-bvar$a bvar-db)
                         (next-bvar$a old-bvar-db)))
             (equal (glmc-generic-state-bvars config bvar-db)
                    (glmc-generic-state-bvars config old-bvar-db))))

  (local (defthm bfr-varlist-bounded-of-append
           (implies (and (bfr-varlist-bounded m x)
                         (bfr-varlist-bounded m y))
                    (bfr-varlist-bounded m (append x y)))
           :hints(("Goal" :in-theory (enable bfr-varlist-bounded)))))

  (local (defthm bfr-varlist-bounded-by-nat-list-max
           (implies (and (<= (nat-list-max x) (nfix n))
                         (nat-listp x))
                    (bfr-varlist-bounded n x))
           :hints(("Goal" :in-theory (enable bfr-varlist-bounded nat-list-max nat-listp)))))

  (defthm-shape-spec-flag
    (defthm bfr-varlist-bounded-of-shape-spec-indices-by-shape-spec-max-bvar
      (implies (and (<= (shape-spec-max-bvar x) (nfix n))
                    (shape-specp x))
               (bfr-varlist-bounded n (shape-spec-indices x)))
      :hints ('(:expand ((shape-spec-indices x)
                         (shape-spec-max-bvar x)
                         (bfr-varlist-bounded n nil)
                         (:free (a b) (bfr-varlist-bounded n (cons a b))))))
      :flag ss)
    (defthm bfr-varlist-bounded-of-shape-spec-list-indices-by-shape-spec-max-bvar-list
      (implies (and (<= (shape-spec-max-bvar-list x) (nfix n))
                    (shape-spec-listp x))
               (bfr-varlist-bounded n (shape-spec-list-indices x)))
      :hints ('(:expand ((shape-spec-list-indices x)
                         (shape-spec-max-bvar-list x)
                         (bfr-varlist-bounded n nil))))
      :flag list))

  (defthm bfr-varlist-bounded-of-shape-spec-indices-of-lookup
    (implies (and (<= (shape-spec-max-bvar-list
                       (shape-spec-bindings->sspecs x)) (nfix n))
                  (shape-spec-bindingsp x))
             (bfr-varlist-bounded n (shape-spec-indices
                                     (cadr (hons-assoc-equal k x)))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal
                                      shape-spec-max-bvar-list
                                      shape-spec-bindings->sspecs
                                      shape-spec-bindingsp))))
  

  (std::defret bfr-varlist-bounded-of-glmc-generic-state-bvars
    (b* (((glmc-config+ config)))
      (implies (and (<= (shape-spec-max-bvar-list
                         (shape-spec-bindings->sspecs config.shape-spec-alist))
                        (base-bvar$a bvar-db))
                    (glmc-config-p config))
               (bfr-varlist-bounded (next-bvar$a bvar-db) statebits)))))

(define glmc-generic-extract-state-bits ((st "An actual value of the state object")
                                         (config glmc-config-p)
                                         bvar-db)
  :returns (statebits alistp)
  :non-executable t
  :verify-guards nil
  (b* (((glmc-config+ config))
       (st-shape-spec (cadr (hons-assoc-equal config.st-var config.shape-spec-alist)))
       ((mv bvar-bindings gvar-bindings) (shape-spec-invert st-shape-spec config.st-var))
       (st-alist `((,config.st-var . ,st)))
       (bvar-bindings-eval (glcp-generic-geval-ev-bfr-update-alist bvar-bindings st-alist))
       (gvar-bindings-eval (glcp-generic-geval-ev-alist gvar-bindings st-alist))
       (bvar-db-alist (glmc-bvar-db-to-state-updates (base-bvar bvar-db)
                                                     (alist-keys gvar-bindings)
                                                     bvar-db)))
    (append bvar-bindings-eval
            (glcp-generic-geval-ev-bfr-update-alist bvar-db-alist gvar-bindings-eval)))
  ///
  (local (include-book "std/alists/hons-assoc-equal" :dir :system))

  (std::defret lookup-in-glmc-generic-extract-state-bits
    (implies (hons-assoc-equal k statebits)
             (equal (cdr (hons-assoc-equal k statebits))
                    (glmc-generic-state-bvar-as-function-of-state k st config bvar-db)))
    :hints(("Goal" :in-theory (enable glmc-generic-state-bvar-as-function-of-state))))

  (std::defret glmc-generic-extract-state-bits-of-update-param
    (equal (glmc-generic-extract-state-bits st (glmc-config-update-param p config) bvar-db)
           (glmc-generic-extract-state-bits st config bvar-db)))

  (local (defthm alist-keys-of-glcp-generic-geval-ev-bfr-update-alist
           (implies (bfr-varnamelist-p (alist-keys x))
                    (equal (alist-keys (glcp-generic-geval-ev-bfr-update-alist x env))
                           (alist-keys x)))
           :hints(("Goal" :in-theory (enable glcp-generic-geval-ev-bfr-update-alist alist-keys)))))

  (std::defret alist-keys-of-glmc-generic-extract-state-bits
    (implies (glmc-config-p config)
             (equal (alist-keys statebits)
                    (glmc-generic-state-bvars config bvar-db)))
    :hints(("Goal" :in-theory (enable glmc-generic-state-bvars))))

  (std::defret lookup-exists-of-glmc-generic-extract-state-bits
    (implies (glmc-config-p config)
             (iff (hons-assoc-equal k statebits)
                  (member k (glmc-generic-state-bvars config bvar-db))))
    :hints(("Goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                                   (glmc-generic-extract-state-bits
                                    acl2::alist-keys-member-hons-assoc-equal))))))


       

(defthm glcp-generic-geval-alist-of-nil
  (equal (glcp-generic-geval-alist nil env) nil)
  :hints(("Goal" :in-theory (enable glcp-generic-geval-alist))))

(defthm bfr-eval-alist-of-append
  (equal (bfr-eval-alist (append a b) env)
         (append (bfr-eval-alist a env)
                 (bfr-eval-alist b env))))

(local (defthm pseudo-termp-when-variablep
         (implies (variablep x)
                  (pseudo-termp x))
         :hints(("Goal" :in-theory (enable pseudo-termp)))))

(local (defthm consp-lookup-in-shape-spec-bindings
         (implies (and (shape-spec-bindingsp x)
                       (hons-assoc-equal k x))
                  (consp (cdr (hons-assoc-equal k x))))
         :hints(("Goal" :in-theory (enable shape-spec-bindingsp hons-assoc-equal)))))

;; (define glmc-generic-next-state-env (env
;;                                      nextst-obj
;;                                      hyp-bfr
;;                                      config
;;                                      interp-st
;;                                      bvar-db
;;                                      state)
;;   :returns (new-env)
;;   :non-executable t
;;   :verify-guards nil
;;   :ignore-ok t
;;   (b* (((glmc-config+ config) (glmc-config-update-param hyp-bfr config))
;;        (pathcond (create-pathcond))

;;        (next-bvar (next-bvar bvar-db))

;;        ((mv ?contra pathcond) (glcp-bfr-to-pathcond hyp-bfr pathcond))
       
;;        (st-shape-spec (cadr (hons-assoc-equal config.st-var config.shape-spec-alist)))
;;        ((mv bvar-bindings gvar-bindings) (shape-spec-invert st-shape-spec config.st-var))

;;        (interp-st (update-is-add-bvars-allowed nil interp-st))

;;        (st-alist `((,config.st-var . ,nextst-obj)))

;;        (env1 (glmc-generic-interp-bvar-alist-env
;;               env bvar-bindings st-alist pathcond config.glcp-config interp-st bvar-db state))
;;        ((mv updates1 er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-bvar-alist
;;          bvar-bindings st-alist
;;          pathcond config.glcp-config interp-st bvar-db state))

;;        (env2 (glmc-generic-interp-gvar-alist-env
;;               env1 gvar-bindings st-alist pathcond config.glcp-config interp-st bvar-db state))
;;        ((mv gvar-updates er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-gvar-alist
;;          gvar-bindings st-alist pathcond config.glcp-config interp-st bvar-db state))

;;        (bvar-db-alist (glmc-bvar-db-to-state-updates (base-bvar bvar-db) (alist-keys gvar-updates) bvar-db))

;;        (env3 (glmc-generic-interp-bvar-alist-env
;;               env2 bvar-db-alist gvar-updates pathcond config.glcp-config interp-st bvar-db state)))
;;     env3))

  

(defsection glmc-generic-next-state
  (local (in-theory (enable glmc-generic-next-state)))
  (local (std::set-define-current-function glmc-generic-next-state))
  (verify-guards glmc-generic-next-state)
;; (define glmc-generic-next-state ((nextst-obj)
;;                                  hyp-bfr
;;                                  (config glmc-config-p)
;;                                  interp-st
;;                                  bvar-db
;;                                  state)
;;   :guard (b* (((glmc-config+ config)))
;;            (and (acl2::interp-defs-alistp config.overrides)
;;                 (acl2::interp-defs-alistp (is-obligs interp-st))
;;                 (hons-assoc-equal config.st-var config.shape-spec-alist)))
;;   :returns (mv (updates bfr-updates-p) er new-interp-st new-bvar-db new-state)

;;   :prepwork ((local (defthm shape-specp-of-lookup-in-shape-spec-bindings
;;                       (implies (and (shape-spec-bindingsp x)
;;                                     (hons-assoc-equal k x))
;;                                (shape-specp (cadr (hons-assoc-equal k x))))
;;                       :hints(("Goal" :in-theory (enable hons-assoc-equal)))))
;;              (local (defthm consp-of-lookup-in-shape-spec-bindings
;;                       (implies (and (shape-spec-bindingsp x)
;;                                     (hons-assoc-equal k x))
;;                                (consp (cdr (hons-assoc-equal k x))))
;;                       :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

;;              (local (defthm bfr-varnamelist-p-when-nat-listp+
;;                       (implies (nat-listp x)
;;                                (bfr-varnamelist-p x))
;;                       :hints(("Goal" :in-theory (enable bfr-varnamelist-p)))))
;;              (local (defthm pseudo-termp-when-variablep
;;                       (implies (variablep x)
;;                                (pseudo-termp x))
;;                       :hints(("Goal" :in-theory (enable pseudo-termp))))))
  
;;   (b* (((glmc-config+ config) (glmc-config-update-param hyp-bfr config))
;;        ((acl2::local-stobjs pathcond)
;;         (mv updates er pathcond interp-st bvar-db state))

;;        (next-bvar (next-bvar bvar-db))

;;        ((mv ?contra pathcond) (glcp-bfr-to-pathcond hyp-bfr pathcond))
       
;;        (st-shape-spec (cadr (hons-assoc-equal config.st-var config.shape-spec-alist)))
;;        ((mv bvar-bindings gvar-bindings) (shape-spec-invert st-shape-spec config.st-var))

;;        (interp-st (update-is-add-bvars-allowed nil interp-st))

;;        (st-alist `((,config.st-var . ,nextst-obj)))

;;        ((mv updates1 er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-bvar-alist
;;          bvar-bindings st-alist
;;          pathcond config.glcp-config interp-st bvar-db state))
;;        ((when er)
;;         (mv nil
;;             (msg "Error extracting the shape spec bits from the next state object: ~@0" er)
;;             pathcond interp-st bvar-db state))

;;        ((mv gvar-updates er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-gvar-alist
;;          gvar-bindings st-alist pathcond config.glcp-config interp-st bvar-db state))
;;        ((when er)
;;         (mv nil
;;             (msg "Error extracting the shape spec variables from the next state object: ~@0" er)
;;             pathcond interp-st bvar-db state))

;;        (bvar-db-alist (glmc-bvar-db-to-state-updates (base-bvar bvar-db) (alist-keys gvar-updates) bvar-db))

;;        ((mv updates2 er pathcond interp-st bvar-db state)
;;         (glmc-generic-interp-bvar-alist
;;          bvar-db-alist gvar-updates pathcond config.glcp-config interp-st bvar-db state))
;;        ((when er)
;;         (mv nil
;;             (msg "Error extracting bvar-db variable updates: ~@0" er)
;;             pathcond interp-st bvar-db state))

;;        ((unless (equal (next-bvar bvar-db) next-bvar))
;;         (mv nil
;;             "Programming error in glmc-generic-next-state: bvar-db was unexpectedly updated"
;;             pathcond interp-st bvar-db state)))

;;     (mv (acl2::append-without-guard updates1 updates2)
;;         nil pathcond interp-st bvar-db state))
;;   ///
  
  (local (acl2::use-trivial-ancestors-check))


  (std::defret interp-defs-of-glmc-generic-next-state
    (b* (((glmc-config+ config)))
      (implies (and (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
                    (acl2::interp-defs-alistp config.overrides)
                    (glmc-config-p config)
                    (hons-assoc-equal config.st-var config.shape-spec-alist))
               (acl2::interp-defs-alistp (nth *is-obligs* new-interp-st)))))

  (local (include-book "std/alists/hons-assoc-equal" :dir :system))


  (local (defthmd lookup-in-shape-spec-invert-implies-varname
           (implies (and (hons-assoc-equal k (mv-nth 0 (shape-spec-invert x term)))
                         (shape-specp x))
                    (bfr-varname-p k))
           :hints(("Goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                                          (acl2::alist-keys-member-hons-assoc-equal))))))

  (local (defthmd lookup-in-shape-spec-invert-implies-varname
           (implies (and (hons-assoc-equal k (mv-nth 0 (shape-spec-invert x term)))
                         (shape-specp x))
                    (bfr-varname-p k))
           :hints(("Goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                                          (acl2::alist-keys-member-hons-assoc-equal))))))

  (local (defthm alistp-when-gobj-alistp
           (implies (gobj-alistp x) (alistp x))
           :hints(("Goal" :in-theory (enable gobj-alistp)))))

  

  (std::defret lookup-in-glcp-generic-next-state
    (b* ((config1 config)
         ((glmc-config+ config) (glmc-config-update-param hyp-bfr config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    ;; (glcp-interp-accs-ok new-interp-st new-bvar-db
                    ;;                      (glcp-config-update-param hyp-bfr (glmc-config->glcp-config config1))
                    ;;                      env)
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (equal bfr-env (car env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-eval hyp-bfr bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (glmc-config-p config1)
                    (hons-assoc-equal k updates)
                    (hons-assoc-equal config.st-var config.shape-spec-alist)
                    (bfr-mode)
                    (gobj-vars-bounded (next-bvar$a bvar-db) t nextst-obj)
                    (bvar-db-orderedp t bvar-db)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t hyp-bfr)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) t (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) t (nth *is-constraint-db* interp-st)))
               (equal (bfr-eval (cdr (hons-assoc-equal k updates)) (car env))
                      (glmc-generic-state-bvar-as-function-of-state
                       k (glcp-generic-geval nextst-obj env)
                       config new-bvar-db))))
    :hints(("Goal" :in-theory (enable glmc-generic-state-bvar-as-function-of-state
                                      lookup-in-shape-spec-invert-implies-varname
                                      equal-of-booleans-rewrite))))

  ;; (std::defret lookup-in-glcp-generic-next-state
  ;;   (b* ((config1 config)
  ;;        ((glmc-config+ config) (glmc-config-update-param hyp-bfr config)))
  ;;     (implies (and (glcp-generic-geval-ev-theoremp
  ;;                    (conjoin-clauses (acl2::interp-defs-alistp (is-obligs new-interp-st))))
  ;;                   ;; (glcp-interp-accs-ok new-interp-st new-bvar-db
  ;;                   ;;                      (glcp-config-update-param hyp-bfr (glmc-config->glcp-config config1))
  ;;                   ;;                      env)
  ;;                   (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env) 
  ;;                   (equal bfr-env (car env))
  ;;                   (bfr-hyp-eval (is-constraint interp-st) bfr-env)
  ;;                   (bfr-eval hyp-bfr (bfr-unparam-env hyp-bfr bfr-env))
  ;;                   (acl2::interp-defs-alistp (nth *is-obligs* interp-st))
  ;;                   (acl2::interp-defs-alistp config.overrides)
  ;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                   (equal (w state0) (w state))
  ;;                   (glmc-config-p config1)
  ;;                   (hons-assoc-equal k updates)
  ;;                   (hons-assoc-equal config.st-var config.shape-spec-alist))
  ;;              (equal (bfr-eval (cdr (hons-assoc-equal k updates)) bfr-env)
  ;;                     (glmc-generic-state-bvar-as-function-of-state
  ;;                      k (glcp-generic-geval nextst-obj env)
  ;;                      config new-bvar-db))))
  ;;   :hints(("Goal" :in-theory (enable glmc-generic-state-bvar-as-function-of-state
  ;;                                     lookup-in-shape-spec-invert-implies-varname
  ;;                                     equal-of-booleans-rewrite))))

  (std::defret glcp-generic-next-state-bfr-eval-alist
    (b* ((config1 config)
         ((glmc-config+ config) (glmc-config-update-param hyp-bfr config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (equal bfr-env (car env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-eval hyp-bfr bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (glmc-config-p config1)
                    (hons-assoc-equal config.st-var config.shape-spec-alist)
                    (not er)
                    (bfr-mode)
                    (gobj-vars-bounded (next-bvar$a bvar-db) t nextst-obj)
                    (bvar-db-orderedp t bvar-db)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t hyp-bfr)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) t (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) t (nth *is-constraint-db* interp-st)))
               (equal (bfr-eval-alist updates (car env))
                      (glmc-generic-extract-state-bits
                       (glcp-generic-geval nextst-obj env) config new-bvar-db))))
    :hints(("Goal" :in-theory (enable glmc-generic-extract-state-bits))))


  (std::defret glcp-generic-next-state-constraint-correct
    (b* ((config1 config)
         ((glmc-config+ config) (glmc-config-update-param hyp-bfr config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (glcp-generic-bvar-db-env-ok bvar-db t (next-bvar$a bvar-db) env)
                    (equal bfr-env (car env))
                    (bfr-hyp-eval (is-constraint interp-st) bfr-env)
                    (bfr-eval hyp-bfr bfr-env)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (glmc-config-p config1)
                    (equal (w state0) (w state))
                    (hons-assoc-equal config.st-var config.shape-spec-alist)
                    (not er)
                    (bfr-mode)
                    (gobj-vars-bounded (next-bvar$a bvar-db) t nextst-obj)
                    (bvar-db-orderedp t bvar-db)
                    (pbfr-vars-bounded (next-bvar$a bvar-db) t hyp-bfr)
                    (bfr-constr-vars-bounded (next-bvar$a bvar-db) t (nth *is-constraint* interp-st))
                    (gbc-db-vars-bounded (next-bvar$a bvar-db) t (nth *is-constraint-db* interp-st)))
               (bfr-hyp-eval (nth *is-constraint* new-interp-st) (car env)))))
  
  (std::defret w-state-preserved-of-glcp-generic-next-state
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glcp-generic-next-state
    (implies (state-p1 state) (state-p1 new-state)))

  (std::defret bvar-db-extension-p-of-glcp-generic-next-state
    (bvar-db-extension-p new-bvar-db bvar-db))

  (std::defret next-bvar-of-glcp-generic-next-state
    (implies (not er)
             (equal (next-bvar$a new-bvar-db) (next-bvar$a bvar-db))))

  (local (defthm pbfr-list-vars-bounded-of-append
           (iff (pbfr-list-vars-bounded k p (append a b))
                (and (pbfr-list-vars-bounded k p a)
                     (pbfr-list-vars-bounded k p b)))
           :hints(("Goal" :in-theory (enable pbfr-list-vars-bounded)))))

  (std::defret glcp-generic-next-state-vars-bounded
    (b* (;; (config1 config)
         ((glmc-config+ config) (glmc-config-update-param hyp-bfr config)))
      (implies (and (<= (next-bvar$a new-bvar-db) (nfix k))
                    (bfr-vars-bounded k p)
                    (bvar-db-vars-bounded k p (next-bvar$a bvar-db) bvar-db)
                    (equal p hyp-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st))
                    (gobj-vars-bounded k p nextst-obj)
                    (not er))
               (and (pbfr-list-vars-bounded k p (alist-vals updates))
                    (implies (bfr-constr-vars-bounded k p (nth *is-constraint* interp-st))
                             (bfr-constr-vars-bounded k p (nth *is-constraint* new-interp-st)))
                    (implies (equal nn (next-bvar$a new-bvar-db))
                             (bvar-db-vars-bounded k p nn new-bvar-db))
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* new-interp-st)))))
    :hints(("Goal" :in-theory (enable alist-vals))))

  (std::defret glcp-generic-next-state-bvar-db-ordered
    (b* (;; (config1 config)
         ((glmc-config+ config) (glmc-config-update-param hyp-bfr config))
         (k (next-bvar$a bvar-db)))
      (implies (and (gobj-vars-bounded k p nextst-obj)
                    (bfr-vars-bounded k p)
                    (bvar-db-orderedp p bvar-db)
                    (bvar-db-vars-bounded k p k bvar-db)
                    (equal p hyp-bfr)
                    (gbc-db-vars-bounded k p (nth *is-constraint-db* interp-st)))
               (bvar-db-orderedp p new-bvar-db))))

  ;; (local (defthm glcp-interp-accs-ok-of-update-add-bvars-allowed
  ;;          (implies (glcp-interp-accs-ok
  ;;                    (update-nth *is-add-bvars-allowed* v interp-st)
  ;;                    bvar-db config env)
  ;;                   (glcp-interp-accs-ok
  ;;                    interp-st bvar-db config env))
  ;;          :hints(("Goal" :in-theory (enable glcp-interp-accs-ok)))
  ;;          :rule-classes :forward-chaining))

  ;; (std::defret glcp-generic-next-state-accs-ok
  ;;   (b* ((config (glcp-config-update-param hyp-bfr (glmc-config->glcp-config config))))
  ;;     (implies (and (glcp-interp-accs-ok new-interp-st new-bvar-db config env))
  ;;              (glcp-interp-accs-ok interp-st bvar-db config env)))
  ;;   :rule-classes :forward-chaining)

  (std::defret interp-st-obligs-extension-p-of-glcp-generic-next-state
    (interp-st-obligs-extension-p new-interp-st interp-st))

  (std::defret alist-keys-of-glmc-generic-next-state
    (implies (and (glmc-config-p config)
                  (not er))
             (equal (alist-keys updates)
                    (glmc-generic-state-bvars config bvar-db)))
    :hints(("Goal" :in-theory (e/d (glmc-generic-state-bvars)))))

  (local (defthm bfr-updates->states-are-alist-keys
           (implies (bfr-updates-p updates)
                    (equal (bfr-updates->states updates) (alist-keys updates)))
           :hints(("Goal" :in-theory (enable bfr-updates-p bfr-updates->states alist-keys)))))

  (std::defret bfr-updates->states-of-glmc-generic-next-state
    (implies (and (glmc-config-p config)
                  (not er))
             (equal (bfr-updates->states updates)
                    (glmc-generic-state-bvars config bvar-db)))
    :hints(("Goal" :in-theory (e/d (glmc-generic-state-bvars)))))

  (std::defret lookup-exists-of-glmc-generic-next-state
    (implies (and (glmc-config-p config)
                  (not er))
             (iff (hons-assoc-equal k updates)
                  (member k (glmc-generic-state-bvars config bvar-db))))
    :hints(("Goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                                   (glmc-generic-next-state
                                    acl2::alist-keys-member-hons-assoc-equal))))))






;; (define glmc-generic-mcheck-to-fsm-bvar-db ((config glmc-config-p)
;;                                             state)
;;   :returns (bvar-db)
;;   :non-executable t
;;   :verify-guards nil
;;   (b* (((mv ?nextst-obj ?prop-bfr ?fsm-constr-bfr ?initst-bfr ?st-hyp-bfr ?hyp-bfr ?st-hyp-next-bfr ?hyp-max-bvar
;;             ?er interp-st bvar-db state)
;;         (glmc-generic-mcheck-main-interps config nil nil state))
;;        ((when er) (mv nil er interp-st bvar-db state))

;;        ((mv ?nextst-bfrs ?er ?interp-st bvar-db ?state)
;;         (glmc-generic-next-state nextst-obj hyp-bfr config interp-st bvar-db state)))
;;     bvar-db))

(define glmc-generic-mcheck-to-fsm-interp-st ((config glmc-config-p)
                                            state)
  :returns (bvar-db)
  :non-executable t
  :verify-guards nil
  (b* (((mv ?nextst-obj ?prop-bfr ?fsm-constr-bfr ?initst-bfr ?st-hyp-bfr ?hyp-bfr ?st-hyp-next-bfr ?hyp-max-bvar
            ?er interp-st bvar-db state)
        (b* ((config (b* (((glmc-config+ config1) config))
                          (glmc-config-update-rewrites
                           config config1.main-rewrite-rules config1.main-branch-merge-rules))))
          (glmc-generic-mcheck-main-interps config nil nil state)))
       (interp-st (is-prof-report interp-st))
       (interp-st (is-prof-reset interp-st))
       ((when er) (mv nil er interp-st bvar-db state))

       ((mv ?nextst-bfrs ?er interp-st ?bvar-db ?state)
        (b* ((config (b* (((glmc-config+ config1) config))
                          (glmc-config-update-rewrites
                           config config1.extract-rewrite-rules config1.extract-branch-merge-rules))))
          (glmc-generic-next-state nextst-obj hyp-bfr config interp-st bvar-db state))))
    interp-st))


;; Interaction of parametrization with the bvar-db is complicated.  Suppose we
;; add a bvar while processing the hyps, i.e. before any parametrization, and
;; the eventual hyp we come up with depends on that bvar.  Then we parametrize
;; the bvar-db on that hyp.  The bvar-db maps (non-parametrized) variable
;; numbers to (parametrized) gobjects.  When we want to compute an env that is
;; consistent with the bvar-db, the correct formulation is from
;; glcp-generic-bvar-db-env-ok:
;;  (iff (bfr-lookup n (bfr-unparam-env p (car env)))
;;       (glcp-generic-geval (get-bvar->term n bvar-db) env))
;; (that is, for an env in the parametrized space).
;; Typically, if we unparametrize the env, set variable n to its appropriate
;; value, and return the env to the param space, this satisfies the requirement
;; for that index n.  But if the hyp depends on n, then translating it to the
;; unparam space and back doesn't necessarily work as expected.  In particular,
;; we depend on bfr-env-equiv-of-unparam-param-env:
;;            (IMPLIES (BFR-EVAL P ENV)
;;                     (BFR-ENV-EQUIV (BFR-UNPARAM-ENV P (BFR-PARAM-ENV P ENV))
;;                                    ENV))
;; Setting variable n in the unparametrized env might disrupt the evaluation of p.

;; For example, suppose our hyp is (iff (logbitp 0 x) (logbitp (bool->bit
;; (logbitp 0 x)) x)).  The first logbitp becomes bvar 0 and the other logbitp,
;; containing a reference to the first one, becomes bvar 1.  Once we're done
;; computing the hyp we parametrize the bvar-db under 

;; The horrible way we do this in gl-generic-interp.lisp is by taking the bvar-db from 




(define glmc-generic-mcheck-env ((alist alistp)
                                 (config glmc-config-p)
                                 state)
  :non-executable t
  :verify-guards nil
  (b* (((glmc-config+ config))
       (env1 (glmc-cov-env config alist))
       (config (b* (((glmc-config+ config1) config))
                          (glmc-config-update-rewrites
                           config config1.main-rewrite-rules config1.main-branch-merge-rules))))
    (glmc-generic-mcheck-main-interps-env env1 config state)))
       
    ;;    ((mv & & & & hyp-bvar-db &)
    ;;     (glmc-generic-interp-hyps config nil nil state))
    ;;    (bfr-env2 (bvar-db-fix-env (next-bvar hyp-bvar-db) (base-bvar hyp-bvar-db) hyp-bvar-db
    ;;                               t (car env1) (cdr env1)))
    ;;    ((mv nextst-obj & & & & hyp-bfr & & & interp-st bvar-db state)
    ;;     (glmc-generic-mcheck-main-interps config nil nil state))
    ;;    ((mv ?nextst-bfrs ?er ?interp-st bvar-db ?state)
    ;;     (glmc-generic-next-state nextst-obj hyp-bfr config interp-st bvar-db state))
    ;;    (bfr-env3 (bfr-param-env hyp-bfr bfr-env2))
    ;;    (bfr-env4 (bvar-db-fix-env (next-bvar bvar-db) (next-bvar hyp-bvar-db) bvar-db
    ;;                               hyp-bfr bfr-env3 (cdr env1))))
    ;; (cons bfr-env4 (cdr env1))))


;; bozo this must be already defined somewhere
(define alist-extract-incl-unbound (keys x)
  (if (atom keys)
      nil
    (cons (cons (car keys) (cdr (hons-get (car keys) x)))
          (alist-extract-incl-unbound (cdr keys) x)))
  ///
  (defthm lookup-in-alist-extract-incl-unbound
    (equal (hons-assoc-equal k (alist-extract-incl-unbound keys x))
           (and (member k keys)
                (cons k (cdr (hons-assoc-equal k x)))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (local (defthm assoc-is-hons-assoc
           (implies k
                    (equal (assoc k x) (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (in-theory (enable glcp-generic-geval-ev-of-nonsymbol-atom)))

  (acl2::defthm-simple-term-vars-flag
    (defthm glcp-generic-geval-ev-of-extract-variable-subset-incl-unbound
      (implies (and (subsetp (simple-term-vars x) vars))
               (equal (glcp-generic-geval-ev x (alist-extract-incl-unbound vars env))
                      (glcp-generic-geval-ev x env)))
      :hints ('(:expand ((simple-term-vars x)
                         (pseudo-termp x))
                :in-theory (enable glcp-generic-geval-ev-of-fncall-args)))
      :flag simple-term-vars)
    (defthm glcp-generic-geval-ev-lst-of-extract-variable-subset-incl-unbound
      (implies (and (subsetp (simple-term-vars-lst x) vars))
               (equal (glcp-generic-geval-ev-lst x (alist-extract-incl-unbound vars env))
                      (glcp-generic-geval-ev-lst x env)))
      :hints ('(:expand ((simple-term-vars-lst x)
                         (pseudo-term-listp x))))
      :flag simple-term-vars-lst))

  (defthm glcp-generic-geval-ev-alist-of-extract-variable-subset-incl-unbound
    (implies (and (subsetp (simple-term-vars-lst (alist-vals x)) vars))
             (equal (glcp-generic-geval-ev-alist x (alist-extract-incl-unbound vars env))
                    (glcp-generic-geval-ev-alist x env)))
    :hints(("Goal" :in-theory (enable alist-vals glcp-generic-geval-ev-alist pseudo-term-alistp
                                      simple-term-vars-lst)))))

(local (defthm pseudo-term-list-listp-of-interp-defs-alist-clauses
         (implies (acl2::interp-defs-alistp defs)
                  (pseudo-term-list-listp (acl2::interp-defs-alist-clauses defs)))
         :hints(("Goal" :in-theory (enable acl2::interp-defs-alistp acl2::interp-defs-alist-clauses)))))


(local (include-book "centaur/misc/introduce-var" :dir :system))
(local (in-theory (Disable vl::consp-when-member-equal-of-vl-namedb-prefixmap-p
                           vl::consp-when-member-equal-of-vl-namedb-nameset-p
                           (:t shape-spec-list-oblig-term)
                            nat-listp
                            nat-list-max
                            acl2::natp-when-member-equal-of-nat-listp
                            acl2::consp-of-car-when-alistp
                            acl2::nat-listp-when-subsetp-equal
                            glmc-cov-clause-implies-oblig-term
                            bvar-db-fix-env
                            member
                            pseudo-termp)))



(defthm glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars
  (implies (and (acl2::eval-alists-agree (acl2::bindinglist-free-vars x) a b)
                (acl2::eval-alists-agree (set-difference-eq (simple-term-vars body)
                                                            (acl2::bindinglist-bound-vars x)) a b))
           (equal (glcp-generic-geval-ev body (glmc-generic-ev-bindinglist x a))
                  (glcp-generic-geval-ev body (glmc-generic-ev-bindinglist x b))))
  :hints(("Goal" :use ((:instance
                        (:functional-instance acl2::unify-ev-bindinglist-when-eval-alists-agree-on-free-vars
                         (acl2::unify-ev glcp-generic-geval-ev)
                         (acl2::unify-ev-lst glcp-generic-geval-ev-lst)
                         (acl2::unify-ev-bindinglist glmc-generic-ev-bindinglist))
                        (x x) (a a) (b b) (body body)))
          :in-theory (enable glmc-generic-ev-bindinglist
                             glcp-generic-geval-ev-of-fncall-args))))
  

(local (defthm lookup-in-pairlis$-of-glcp-generic-geval-ev-lst
         (equal (cdr (hons-assoc-equal k (pairlis$ vars (glcp-generic-geval-ev-lst vars a))))
                (and (member k vars)
                     (glcp-generic-geval-ev k a)))
         :hints (("goal" :in-theory (enable pairlis$)))))


(defsection eval-alists-agree-on-free-vars-of-pairlis$
  (local (defthmd symbolp-when-member-symbol-list
           (implies (and (member k x)
                         (symbol-listp (list-fix x)))
                    (symbolp k))
           :hints(("Goal" :in-theory (enable list-fix)))))

  (local (defthmd symbol-listp-when-subsetp
           (implies (and (subsetp x y)
                         (symbol-listp y))
                    (symbol-listp (list-fix x)))
           :hints(("Goal" :in-theory (enable subsetp symbolp-when-member-symbol-list)
                   :induct (len x)))))
                       
  (defthm eval-alists-agree-on-free-vars-of-pairlis$
    (implies (and (subsetp vars1 vars2)
                  (symbol-listp vars2)
                  (not (member nil vars1)))
             (acl2::eval-alists-agree vars1 (pairlis$ vars2 (glcp-generic-geval-ev-lst vars2 a)) a))
    :hints(("Goal" :in-theory (enable acl2::eval-alists-agree-by-bad-guy
                                      symbolp-when-member-symbol-list
                                      acl2::assoc-is-hons-assoc-equal-when-key-nonnil
                                      symbol-listp-when-subsetp)
            :do-not-induct t))))

(defthm glmc-generic-ev-bindinglist-of-pairlis$-keys
  (implies (and (subsetp (set-difference-eq (simple-term-vars body)
                                            (acl2::bindinglist-bound-vars x))
                         vars)
                (subsetp (acl2::bindinglist-free-vars x) vars)
                (symbol-listp vars)
                (acl2::bindinglist-p x)
                (pseudo-termp body))
           (equal (glcp-generic-geval-ev body
                                         (glmc-generic-ev-bindinglist
                                          x
                                          (pairlis$ vars (glcp-generic-geval-ev-lst vars a))))
                  (glcp-generic-geval-ev body
                                         (glmc-generic-ev-bindinglist x a))))
  :hints (("goal" :use ((:instance glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars
                         (a (pairlis$ vars (glcp-generic-geval-ev-lst vars a)))
                         (b a)))
           :in-theory (disable glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars)
           :do-not-induct t)))

(define glmc-hyp-bvar-db ((config glmc-config-p) state)
  :non-executable t
  :verify-guards nil
  :returns (new-bvar-db)
  (b* ((config (b* (((glmc-config+ config1) config))
                 (glmc-config-update-rewrites
                  config config1.main-rewrite-rules config1.main-branch-merge-rules))))
    (mv-nth 4 (glmc-generic-interp-hyps config nil nil state)))
  ///
  (std::defret glmc-generic-mcheck-main-interps-hyp-env-ok-under-config-change
    :pre-bind ((orig-config config)
               (config (b* (((glmc-config+ config1) config))
                         (glmc-config-update-rewrites
                          config config1.main-rewrite-rules config1.main-branch-merge-rules))))
    (b* (((glmc-config+ config1))
         (fix-env (glmc-generic-mcheck-main-interps-env env config state)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (acl2::interp-defs-alist-clauses (is-obligs new-interp-st))))
                    (not (glmc-syntax-checks config))
                    (glmc-config-p config)
                    ;; (assoc config.st-var config.shape-spec-alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (not er)
                    (bfr-mode))
               (glcp-generic-bvar-db-env-ok
                (glmc-hyp-bvar-db orig-config state)
                t hyp-max-bvar fix-env)))
    :hints(("Goal" :use ((:instance glmc-generic-mcheck-main-interps-hyp-env-ok
                          (config (b* (((glmc-config+ config1) config))
                                    (glmc-config-update-rewrites
                                     config config1.main-rewrite-rules config1.main-branch-merge-rules)))))))
    :fn glmc-generic-mcheck-main-interps)

  (std::defret get-bvar->term-below-hyp-bound-of-glcp-generic-main-interps-under-config-change
      :pre-bind ((orig-config config)
               (config (b* (((glmc-config+ config1) config))
                         (glmc-config-update-rewrites
                          config config1.main-rewrite-rules config1.main-branch-merge-rules))))
      (implies (and (<= (base-bvar$a new-bvar-db) (nfix n))
                    (< (nfix n) hyp-max-bvar))
               (equal (get-bvar->term$a n new-bvar-db)
                      (gobj-to-param-space
                       (get-bvar->term$a n (glmc-hyp-bvar-db orig-config state))
                       hyp-bfr)))
      :hints (("goal" :use ((:instance get-bvar->term-below-hyp-bound-of-glcp-generic-main-interps
                             (config (b* (((glmc-config+ config1) config))
                                    (glmc-config-update-rewrites
                                     config config1.main-rewrite-rules config1.main-branch-merge-rules)))))))
      :fn glmc-generic-mcheck-main-interps)

  (std::defret base-bvar-of-<fn>
    (equal (base-bvar$a new-bvar-db)
           (b* (((glmc-config+ config)))
             (shape-spec-max-bvar-list
              (shape-spec-bindings->sspecs config.shape-spec-alist))))))


(defsection glmc-generic-mcheck-to-fsm
  (local (in-theory (enable glmc-generic-mcheck-to-fsm)))
  (local (std::set-define-current-function glmc-generic-mcheck-to-fsm))
  (verify-guards glmc-generic-mcheck-to-fsm
    :guard-debug t)

  (defthm glmc-generic-extract-state-bits-of-glmc-config-update-rewrites
    (equal (glmc-generic-extract-state-bits nextst (glmc-config-update-rewrites config rewrites branch-merges) bvar-db)
           (glmc-generic-extract-state-bits nextst config bvar-db))
    :hints(("Goal" :in-theory (enable glmc-generic-extract-state-bits))))

  (defthm glmc-generic-state-bvars-of-glmc-config-update-rewrites
    (equal (glmc-generic-state-bvars (glmc-config-update-rewrites config rewrites branch-merges) bvar-db)
           (glmc-generic-state-bvars config bvar-db))
    :hints(("Goal" :in-theory (enable glmc-generic-state-bvars))))

  (std::defret glmc-fsm-p-of-glmc-mcheck-to-fsm
    (b* (((glmc-config+ config)))
      (implies (and (glmc-config-p config)
                    (acl2::interp-defs-alistp config.overrides)
                    (not er))
               (glmc-fsm-p fsm))))

;; (define glmc-generic-mcheck-to-fsm ((config glmc-config-p)
;;                                     bvar-db
;;                                     state)
;;   :returns (mv (fsm (implies (not er) (glmc-fsm-p fsm))
;;                     :hyp (b* (((glmc-config+ config)))
;;                            (and (glmc-config-p config)
;;                                 (acl2::interp-defs-alistp config.overrides))))
;;                er new-bvar-db new-state)
;;   :guard (b* (((glmc-config+ config)))
;;            (acl2::interp-defs-alistp config.overrides))

;;   (b* (((acl2::local-stobjs interp-st)
;;         (mv fsm er interp-st bvar-db state))

;;        (bvar-db (init-bvar-db 0 bvar-db))
;;        (er (glmc-syntax-checks config))
;;        ((when er) (mv nil er interp-st bvar-db state))

;;        ((mv nextst-obj prop-bfr fsm-constr-bfr initst-bfr st-hyp-bfr hyp-bfr st-hyp-next-bfr ?hyp-max-bvar
;;             er interp-st bvar-db state)
;;         (glmc-generic-mcheck-main-interps config interp-st bvar-db state))
;;        ((when er) (mv nil er interp-st bvar-db state))

;;        ((mv nextst-bfrs er interp-st bvar-db state)
;;         (glmc-generic-next-state nextst-obj hyp-bfr config interp-st bvar-db state))
;;        ((when er) (mv nil er interp-st bvar-db state))

;;        (bit-constr-bfr (bfr-constr->bfr (is-constraint interp-st))))

;;     (mv (make-glmc-fsm :nextst nextst-bfrs
;;                        :prop prop-bfr
;;                        :fsm-constr fsm-constr-bfr
;;                        :bit-constr bit-constr-bfr
;;                        :initst initst-bfr
;;                        :st-hyp st-hyp-bfr
;;                        :st-hyp-next st-hyp-next-bfr
;;                        :hyp hyp-bfr
;;                        :hyp-var-bound hyp-max-bvar
;;                        :interp-clauses (acl2::interp-defs-alist-clauses (is-obligs interp-st))
;;                        :var-bound (next-bvar bvar-db))
;;         nil interp-st bvar-db state))
;;   ///
  (defthm glmc-generic-mcheck-to-fsm-normalize
    (implies (syntaxp (not (equal bvar-db ''nil)))
             (equal (glmc-generic-mcheck-to-fsm config bvar-db interp-st state)
                    (glmc-generic-mcheck-to-fsm config nil nil state))))

  (local (defthm subsetp-of-set-difference
           (iff (subsetp-equal (set-difference-equal a b) c)
                (subsetp-equal a (union-equal c b)))
           :hints ((acl2::set-reasoning))))

  (local (in-theory (disable acl2::commutativity-of-append-under-set-equiv)))

  (std::defret glmc-generic-mcheck-to-fsm-correct
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm))
         ;; (new-bvar-db (glmc-generic-mcheck-to-fsm-bvar-db config state))
         (env (glmc-generic-mcheck-env alist config state)))
      (implies (and (not er)
                    (glmc-config-p config)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses fsm.interp-clauses))
                    (glcp-generic-geval-ev
                     (shape-spec-list-oblig-term
                      (shape-spec-bindings->sspecs config.shape-spec-alist)
                      (alist-keys config.shape-spec-alist))
                     alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (bfr-mode))
               (and (equal (bfr-eval fsm.hyp (car env))
                           (and (glcp-generic-geval-ev config.in-hyp alist)
                                (bool-fix (glcp-generic-geval-ev config.st-hyp alist))))
                    (equal (bfr-eval fsm.st-hyp (car env))
                           (bool-fix (glcp-generic-geval-ev config.st-hyp alist)))
                    (glcp-generic-bvar-db-env-ok
                     (glmc-hyp-bvar-db config state)
                     t fsm.hyp-var-bound env)
                    (implies (and (glcp-generic-geval-ev config.in-hyp alist)
                                  (glcp-generic-geval-ev config.st-hyp alist))
                             (b* ((new-alist (glmc-generic-ev-bindinglist config.bindings alist)))
                               (and (equal (bfr-eval fsm.bit-constr (car env)) t)
                                    (glcp-generic-bvar-db-env-ok new-bvar-db t (next-bvar$a new-bvar-db) env)
                                    (equal (bfr-eval-alist fsm.nextst (car env))
                                           (glmc-generic-extract-state-bits
                                            (glcp-generic-geval-ev config.nextst new-alist)
                                            config
                                            new-bvar-db))
                                    (equal (bfr-eval fsm.prop (car env))
                                           (bool-fix (glcp-generic-geval-ev config.prop new-alist)))
                                    (equal (bfr-eval fsm.fsm-constr (car env))
                                           (bool-fix (glcp-generic-geval-ev config.constr new-alist)))
                                    (equal (bfr-eval fsm.initst (car env))
                                           (bool-fix (glcp-generic-geval-ev config.initstp new-alist)))
                                    (equal (bfr-eval fsm.st-hyp-next (car env))
                                           (bool-fix (glcp-generic-geval-ev config.st-hyp
                                                                            (list (cons config.st-var
                                                                                        (glcp-generic-geval-ev config.nextst new-alist))))))))))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-env))))

  (std::defret w-state-preserved-of-glmc-generic-mcheck-to-fsm
    (equal (w new-state) (w state)))
  
  (std::defret state-p1-preserved-of-glmc-generic-mcheck-to-fsm
    (implies (state-p1 state) (state-p1 new-state)))

  (std::defret glmc-generic-mcheck-to-fsm-vars-bounded
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm)))
      (and (implies (and (<= fsm.var-bound (nfix k))
                         (not er))
                    (and (pbfr-vars-bounded k fsm.hyp fsm.initst)
                         (pbfr-vars-bounded k fsm.hyp fsm.fsm-constr)
                         (pbfr-vars-bounded k fsm.hyp fsm.bit-constr)
                         (pbfr-vars-bounded k fsm.hyp fsm.prop)
                         (pbfr-vars-bounded k fsm.hyp fsm.st-hyp-next)
                         (pbfr-list-vars-bounded k fsm.hyp (alist-vals fsm.nextst))))
           (implies (and (<= fsm.hyp-var-bound (nfix k))
                         (not er))
                    (and (pbfr-vars-bounded k t fsm.st-hyp)
                         (pbfr-vars-bounded k t fsm.hyp))))))

  (std::defret glmc-generic-mcheck-to-fsm-vars-bounded-aig-mode
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm)))
      (and (implies (and (<= fsm.var-bound (nfix k))
                         (not er)
                         (bfr-mode))
                    (and (pbfr-vars-bounded k t fsm.initst)
                         (pbfr-vars-bounded k t fsm.fsm-constr)
                         (pbfr-vars-bounded k t fsm.bit-constr)
                         (pbfr-vars-bounded k t fsm.prop)
                         (pbfr-vars-bounded k t fsm.st-hyp-next)
                         (pbfr-list-vars-bounded k t (alist-vals fsm.nextst))))))
    :hints (("goal" :use glmc-generic-mcheck-to-fsm-vars-bounded
             :in-theory (disable glmc-generic-mcheck-to-fsm-vars-bounded
                                 glmc-generic-mcheck-to-fsm))))

  (std::defret bvar-db-orderedp-of-glmc-generic-mcheck-to-fsm-bvar-db
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm)))
      (implies (not er)
               (bvar-db-orderedp fsm.hyp new-bvar-db))))

  (std::defret bvar-db-orderedp-of-glmc-generic-mcheck-to-fsm-bvar-db-aig-mode
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm)))
      (implies (and (not er) (bfr-mode))
               (bvar-db-orderedp t new-bvar-db)))
    :hints (("goal" :use bvar-db-orderedp-of-glmc-generic-mcheck-to-fsm-bvar-db
             :in-theory (disable bvar-db-orderedp-of-glmc-generic-mcheck-to-fsm-bvar-db
                                 glmc-generic-mcheck-to-fsm))))


  ;; (local (defthm bvar-db-env-ok-of-extension-main->hyp
  ;;          (b* (((mv st-hyp in-hyp & & hyp-bvar-db &)
  ;;                (glmc-generic-interp-hyps config nil nil state))
  ;;               ((mv & & & & & & & & er & main-bvar-db &)
  ;;                (glmc-generic-mcheck-main-interps config nil nil state))
  ;;               (p (bfr-and in-hyp st-hyp)))
  ;;            (implies (and (<= bound (next-bvar$a hyp-bvar-db))
  ;;                          (not er))
  ;;                     (equal (glcp-generic-bvar-db-env-ok main-bvar-db p bound env)
  ;;                            (glcp-generic-bvar-db-env-ok hyp-bvar-db t bound (genv-unparam p env)))))
  ;;          :hints (("goal" :use ((:instance glcp-generic-bvar-db-env-ok-of-bvar-db-extension
  ;;                                 (old (parametrize-bvar-db (bfr-and (mv-nth 1 (glmc-generic-interp-hyps config nil nil state))
  ;;                                                                    (mv-nth 0 (glmc-generic-interp-hyps config nil nil state)))
  ;;                                                           (mv-nth 4 (glmc-generic-interp-hyps config nil nil state))
  ;;                                                           nil))
  ;;                                 (p (bfr-and (mv-nth 1 (glmc-generic-interp-hyps config nil nil state))
  ;;                                             (mv-nth 0 (glmc-generic-interp-hyps config nil nil state))))
  ;;                                 (new (mv-nth 10 (glmc-generic-mcheck-main-interps config nil nil state)))))
  ;;                   :in-theory (enable genv-unparam)))))


  ;; (local (defthm bvar-db-env-fix-of-same-next-extension
  ;;          (implies (and (bind-bvar-db-extension bvar-db old)
  ;;                        (equal (next-bvar$a bvar-db) (next-bvar$a old)))
  ;;                   (equal (Bvar-db-fix-env next base bvar-db p bfr-env var-env)
  ;;                          (Bvar-db-fix-env next base old p bfr-env var-env)))
  ;;          :hints(("Goal" :in-theory (enable bvar-db-fix-env)))))

  (std::defret glmc-generic-mcheck-env-correct-for-glmc-generic-mcheck-to-fsm
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm))
         (env (glmc-generic-mcheck-env alist config state)))
      (implies (and (not er)
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (glmc-config-p config)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses fsm.interp-clauses))
                    (glcp-generic-geval-ev
                     (shape-spec-list-oblig-term
                      (shape-spec-bindings->sspecs config.shape-spec-alist)
                      (alist-keys config.shape-spec-alist))
                     alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (bfr-mode))
               (glcp-generic-bvar-db-env-ok new-bvar-db fsm.hyp (next-bvar$a new-bvar-db) env)))
    :hints(("Goal" :in-theory (disable glmc-generic-mcheck-to-fsm)))
    :otf-flg t)

  (std::defret glmc-generic-mcheck-env-correct-for-glmc-generic-mcheck-to-fsm-hyp
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm))
         (env (glmc-generic-mcheck-env alist config state)))
      (implies (and (not er)
                    (glmc-config-p config)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses fsm.interp-clauses))
                    (glcp-generic-geval-ev
                     (shape-spec-list-oblig-term
                      (shape-spec-bindings->sspecs config.shape-spec-alist)
                      (alist-keys config.shape-spec-alist))
                     alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (bfr-mode))
               (glcp-generic-bvar-db-env-ok
                (glmc-hyp-bvar-db config state)
                     t fsm.hyp-var-bound env)))
    :hints(("Goal" :in-theory (disable glmc-generic-mcheck-to-fsm)))
    :otf-flg t)

  
  (local (std::defret GLMC-GENERIC-MCHECK-TO-FSM-INTERP-ST-clauses-are-interp-clauses
           (b* (((glmc-fsm fsm)))
             (implies (not er)
                      (equal fsm.interp-clauses
                             (acl2::interp-defs-alist-clauses
                              (is-obligs (glmc-generic-mcheck-to-fsm-interp-st config state))))))
           :hints(("Goal" :in-theory (enable glmc-generic-mcheck-to-fsm-interp-st)))))


  (local (std::defret glmc-generic-mcheck-env-eval-shape-specs
           (b* (((glmc-config+ config))
                ((glmc-fsm fsm))
                ;; (new-bvar-db (glmc-generic-mcheck-to-fsm-bvar-db config state))
                (env (glmc-generic-mcheck-env alist config state)))
             (implies (and (not er)
                           (glcp-generic-geval-ev config.st-hyp alist)
                           (glcp-generic-geval-ev config.in-hyp alist)
                           (glmc-config-p config)
                           (glcp-generic-geval-ev-theoremp
                            (conjoin-clauses fsm.interp-clauses))
                           (glcp-generic-geval-ev
                            (shape-spec-list-oblig-term
                             (shape-spec-bindings->sspecs config.shape-spec-alist)
                             (alist-keys config.shape-spec-alist))
                            alist)
                           (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                           (equal (w state0) (w state))
                           (bfr-mode))
                      (equal (glcp-generic-geval-alist
                              (shape-specs-to-interp-al config.shape-spec-alist)
                              env)
                             (pairlis$ (alist-keys config.shape-spec-alist)
                                       (glcp-generic-geval-ev-lst (alist-keys config.shape-spec-alist) alist)))))
           :hints(("Goal" :in-theory (enable glmc-generic-mcheck-env)))))

  (std::defret no-err-implies-syntax-ok
    (implies (not er)
             (not (glmc-syntax-checks config))))

  

  (std::defret alist-keys-of-glmc-generic-mcheck-to-fsm
    (b* (((glmc-fsm fsm)))
      (implies (and (glmc-config-p config)
                    (not er))
               (equal (alist-keys fsm.nextst)
                      (glmc-generic-state-bvars
                       config
                       new-bvar-db))))
    :hints(("Goal" :in-theory (e/d (;; glmc-generic-state-bvars
                                    ;; GLMC-GENERIC-MCHECK-TO-FSM-BVAR-DB
                                    )))))

  (std::defret lookup-exists-of-glmc-generic-mcheck-to-fsm
    (b* (((glmc-fsm fsm)))
      (implies (and (glmc-config-p config)
                    (not er))
               (iff (hons-assoc-equal k fsm.nextst)
                    (member k (glmc-generic-state-bvars
                               config
                               new-bvar-db)))))
    :hints(("Goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                                   (acl2::alist-keys-member-hons-assoc-equal
                                    glmc-generic-mcheck-to-fsm)))))


  (local (defthm bfr-lookup-in-slice-to-bdd-env
           (implies (and (bfr-varnamelist-p (alist-keys x))
                         (alistp x))
                    (equal (bfr-lookup k (slice-to-bdd-env x y))
                           (let ((k (bfr-varname-fix k)))
                             (if (hons-assoc-equal k x)
                                 (bool-fix (cdr (hons-assoc-equal k x)))
                               (bfr-lookup k y)))))
           :hints(("Goal" :in-theory (enable alist-keys hons-assoc-equal slice-to-bdd-env)))))


  (local (defthm intro-var-for-bfr-env-equiv-witness
           (equal (bfr-env-equiv-witness x y)
                  (acl2::introduce-var 'bvar (hide (bfr-env-equiv-witness x y))))
           :hints(("Goal" :in-theory (enable acl2::introduce-var)
                   :expand ((:free (x) (hide x)))))))

  (local (defthm lookup-exists-of-shape-spec-invert
           (implies (shape-specp x)
                    (iff (hons-assoc-equal k (mv-nth 0 (shape-spec-invert x term)))
                         (member k (shape-spec-indices x))))
           :hints (("goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                                           (acl2::alist-keys-member-hons-assoc-equal))))))


  (local (defthm member-implies-less-than-nat-list-max
           (implies (and (member k x)
                         (nat-listp x))
                    (< k (nat-list-max x)))
           :hints(("Goal" :in-theory (enable nat-listp nat-list-max)))
           :rule-classes :linear))

  (local (defthm-shape-spec-flag
           (defthm member-shape-spec-indices-implies-less-than-max
             (implies (shape-specp x)
                      (iff (member k (shape-spec-indices x))
                           (and (natp k)
                                (< k (shape-spec-max-bvar x))
                                (hide (member k (shape-spec-indices x))))))
             :hints ('(:expand ((shape-spec-indices x)
                                (shape-spec-max-bvar x)
                                (:free (x) (hide x)))
                       :in-theory (enable acl2::natp-when-member-equal-of-nat-listp)))
             :flag ss)
           (defthm member-shape-spec-list-indices-implies-less-than-max
             (implies (and (shape-spec-listp x))
                      (iff (member k (shape-spec-list-indices x))
                           (and (natp k)
                                (< k (shape-spec-max-bvar-list x))
                                (hide (member k (shape-spec-list-indices x))))))
             :hints ('(:expand ((shape-spec-list-indices x)
                                (shape-spec-max-bvar-list x)
                                (:free (x) (hide x)))))
             :flag list)))

  (local (defthm aig-env-lookup-of-append
           (iff (acl2::aig-env-lookup k (append x y))
                (if (hons-assoc-equal k x)
                    (cdr (hons-assoc-equal k x))
                  (acl2::aig-env-lookup k y)))))

  ;; (local (defthm lookup-in-bfr-unparam-env-when-p-in-aig-mode
  ;;          (implies (and (bfr-mode)
  ;;                        (bfr-eval p bfr-env))
  ;;                   (bfr-env-equiv (bfr-unparam-env p bfr-env)
  ;;                                  bfr-env))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       `(:expand (,(car (last clause)))))
  ;;                  (and stable-under-simplificationp
  ;;                       '(:in-theory (e/d (bfr-lookup bfr-eval bfr-unparam-env
  ;;                                                     acl2::lookup-in-aig-extract-iterated-assigns-alist)
  ;;                                         (acl2::aig-env-lookup)))))))

  ;; (local (defthm bfr-eval-preserved-for-param-in-bvar-db-env-fix-aig-mode
  ;;          (implies (and (bfr-mode)
  ;;                        (bfr-eval p bfr-env)
  ;;                        (pbfr-vars-bounded base t p))
  ;;                   (bfr-eval p (bvar-db-fix-env next base bvar-db p bfr-env var-env)))
  ;;          :hints(("Goal" :in-theory (enable bvar-db-fix-env bfr-param-env)))))

  ;; (local (defthm bfr-lookup-in-bvar-db-fix-env-when-less-than-base
  ;;          (implies (and (let ((k (bfr-varname-fix k)))
  ;;                          (not (and (integerp k)
  ;;                                    (<= (nfix base) k)
  ;;                                    (< k (nfix next)))))
  ;;                        (bfr-mode)
  ;;                        (bfr-eval p bfr-env)
  ;;                        (pbfr-vars-bounded base t p))
  ;;                   (equal (bfr-lookup k (bvar-db-fix-env next base bvar-db p bfr-env var-env))
  ;;                          (bfr-lookup k bfr-env)))
  ;;          :hints(("Goal" :in-theory (enable bvar-db-fix-env bfr-param-env)))))

  (local (defthm max-bvar-of-lookup-less-list
           (<= (shape-spec-max-bvar (cadr (hons-assoc-equal k alist)))
               (shape-spec-max-bvar-list (shape-spec-bindings->sspecs alist)))
           :hints(("Goal" :in-theory (enable shape-spec-bindings->sspecs hons-assoc-equal
                                             shape-spec-max-bvar-list)))
           :rule-classes :linear))
  
  ;; (local (defthm lookup-exists-of-
  ;;          (implies (shape-spec-listp x)
  ;;                   (iff (hons-assoc-equal k (car (glcp-generic-geval-ev
  ;;                                                  (shape-spec-list-env-term x terms)
  ;;                                                  alist)))
  ;;                        (member k (shape-spec-list-indices x))))
  ;;          :hints(("Goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
  ;;                                         (acl2::alist-keys-member-hons-assoc-equal))))))

  (defthm alist-keys-of-glcp-generic-geval-ev-alist
    (implies (alistp x)
             (equal (alist-keys (glcp-generic-geval-ev-alist x a))
                    (alist-keys x)))
    :hints(("Goal" :in-theory (enable alist-keys))))

  (defthm alistp-of-glcp-generic-geval-ev-alist
    (alistp (glcp-generic-geval-ev-alist x a)))

  (defthm lookup-in-glcp-generic-geval-ev-alist
    (implies (alistp x)
             (equal (hons-assoc-equal k (glcp-generic-geval-ev-alist x a))
                    (and (hons-assoc-equal k x)
                         (cons k (glcp-generic-geval-ev (cdr (hons-assoc-equal k x)) a))))))

  (defthm hons-assoc-equal-of-shape-spec-list-invert
    (implies (shape-spec-listp x)
             (iff (hons-assoc-equal k (mv-nth 0 (shape-spec-list-invert x terms)))
                  (member k (shape-spec-list-indices x))))
    :hints(("Goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                                   (acl2::alist-keys-member-hons-assoc-equal)))))

  (defthm hons-assoc-equal-of-shape-spec-invert
    (implies (shape-specp x)
             (iff (hons-assoc-equal k (mv-nth 0 (shape-spec-invert x terms)))
                  (member k (shape-spec-indices x))))
    :hints(("Goal" :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                                   (acl2::alist-keys-member-hons-assoc-equal)))))


  (local (defthm member-shape-spec-list-indices-when-member-index
           (implies (member k (shape-spec-indices (cadr (hons-assoc-equal var x))))
                    (member k (shape-spec-list-indices (shape-spec-bindings->sspecs x))))
           :hints(("Goal" :in-theory (enable shape-spec-bindings->sspecs shape-spec-list-indices hons-assoc-equal)))))


  (defthm lookup-in-shape-spec-list-invert-when-lookup-in-lookup
    (implies (and (member k (shape-spec-indices (cadr (hons-assoc-equal var x))))
                  (no-duplicatesp (shape-spec-list-indices (shape-spec-bindings->sspecs x)))
                  (shape-spec-bindingsp x))
             (equal (hons-assoc-equal k (mv-nth 0 (shape-spec-list-invert
                                                   (shape-spec-bindings->sspecs x)
                                                   (alist-keys x))))
                    (hons-assoc-equal k (mv-nth 0 (shape-spec-invert (cadr (hons-assoc-equal var x)) var)))))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal
                                      shape-spec-bindings->sspecs
                                      shape-spec-list-indices
                                      alist-keys
                                      shape-spec-bindingsp
                                      shape-spec-list-invert)
                                   (MEMBER-SHAPE-SPEC-INDICES-IMPLIES-LESS-THAN-MAX
                                    MEMBER-SHAPE-SPEC-LIST-INDICES-IMPLIES-LESS-THAN-MAX))
            :induct (shape-spec-bindingsp x))
           (acl2::set-reasoning)))

  (local (defthm simple-term-vars-when-variablep
           (implies (variablep v)
                    (equal (simple-term-vars v) (list v)))
           :hints(("Goal" :in-theory (enable simple-term-vars)))))

  (defthm lookup-in-shape-spec-invert-vars-subset
    (implies (not (member v (simple-term-vars-lst (alist-vals x))))
             (not (member v (simple-term-vars (cdr (hons-assoc-equal k x))))))
    :hints(("Goal" :in-theory (enable simple-term-vars-lst hons-assoc-equal alist-vals))))

  (defthm lookup-in-shape-spec-invert-vars-subset-of-state
    (implies (variablep st-var)
             (subsetp (simple-term-vars (cdr (hons-assoc-equal v (mv-nth 0 (shape-spec-invert x st-var)))))
                      (list st-var)))
    :hints ((acl2::set-reasoning)))

  
  (defthm lookup-in-shape-spec-invert-vars-subset-of-state-gvar
    (implies (variablep st-var)
             (subsetp (simple-term-vars (cdr (hons-assoc-equal v (mv-nth 1 (shape-spec-invert x st-var)))))
                      (list st-var)))
    :hints ((acl2::set-reasoning)))

  (defthmd normalize-alist-of-shape-spec-invert-lookup
    (implies (and (syntaxp (symbolp alist))
                  (variablep st-var)
                  (shape-specp x))
             (equal (glcp-generic-geval-ev (cdr (hons-assoc-equal v (mv-nth 0 (shape-spec-invert x st-var)))) alist)
                    (glcp-generic-geval-ev
                     (cdr (hons-assoc-equal v (mv-nth 0 (shape-spec-invert x st-var))))
                     (list (cons st-var (cdr (hons-assoc-equal st-var alist)))))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-of-extract-variable-subset-incl-unbound
                           (x (cdr (hons-assoc-equal v (mv-nth 0 (shape-spec-invert x st-var)))))
                           (vars (list st-var))
                           (env alist)))
             :in-theory (enable alist-extract-incl-unbound pseudo-termp))))

  (defthm shape-spec-invert-alist-vals-vars-subset-of-state-gvar
    (implies (variablep st-var)
             (subsetp (simple-term-vars-lst (alist-vals (mv-nth 1 (shape-spec-invert x st-var))))
                      (list st-var)))
    :hints ((acl2::set-reasoning)))

  
  


  (defthmd normalize-geval-alist-of-shape-spec-invert-lookup
    (implies (and (syntaxp (symbolp alist))
                  (variablep st-var)
                  (shape-specp x))
             (equal (glcp-generic-geval-ev-alist (mv-nth 1 (shape-spec-invert x st-var)) alist)
                    (glcp-generic-geval-ev-alist (mv-nth 1 (shape-spec-invert x st-var))
                                                 (list (cons st-var (cdr (hons-assoc-equal st-var alist)))))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-alist-of-extract-variable-subset-incl-unbound
                           (x (mv-nth 1 (shape-spec-invert x st-var)))
                           (vars (list st-var))
                           (env alist)))
             :in-theory (enable alist-extract-incl-unbound pseudo-termp))))

  ;; (local (in-theory (disable MEMBER-SHAPE-SPEC-INDICES-IMPLIES-LESS-THAN-MAX
  ;;                                   MEMBER-SHAPE-SPEC-LIST-INDICES-IMPLIES-LESS-THAN-MAX)))


  ;; (defthm bfr-lookup-in-bvar-db-fix-env-aig-mode-when-state-varp
  ;;   (implies (and (natp (bfr-varname-fix k))
  ;;                 (case-split (< (bfr-varname-fix k) (nfix next)))
  ;;                 (case-split (<= (nfix base) (bfr-varname-fix k)))
  ;;                 (<= (base-bvar$a bvar-db) (bfr-varname-fix k))
  ;;                 (bfr-mode)
  ;;                 (bfr-eval p bfr-env)
  ;;                 (pbfr-vars-bounded base t p)
  ;;                 (not (mv-nth 0 (glmc-gobj-to-term (get-bvar->term k bvar-db)))))
  ;;            (equal (bfr-lookup k (bvar-db-fix-env next base bvar-db p bfr-env var-env))
  ;;                   (bool-fix (glcp-generic-geval (get-bvar->term k bvar-db) (cons nil var-env)))))
  ;;   :hints(("Goal" :in-theory (enable bvar-db-fix-env bfr-param-env
  ;;                                     glcp-generic-geval-normalize-env-when-glmc-gobj-to-term
  ;;                                     glcp-generic-geval-normalize-env-when-glmc-gobj-list-to-terms))))


  (local (defthm GLCP-GENERIC-GEVAL-OF-SET-VAR-WHEN-GOBJ-VARS-BOUNDED-no-param-same-var
           (implies (gobj-vars-bounded k t x)
                    (equal (glcp-generic-geval x (cons (bfr-set-var k v bfr-env) var-env))
                           (glcp-generic-geval x (cons bfr-env var-env))))
           :hints (("goal" :use ((:instance glcp-generic-geval-of-set-var-when-gobj-vars-bounded
                                  (m k) (p t) (env bfr-env)))
                    :in-theory (disable glcp-generic-geval-of-set-var-when-gobj-vars-bounded)))))
  
  (local (defthm bvar-db-orderdp-necc-stronger
           (implies (and (<= (base-bvar$a bvar-db) (nfix k))
                         (< (nfix k) (next-bvar$a bvar-db))
                         (bvar-db-orderedp p bvar-db))
                    (gobj-vars-bounded k p (get-bvar->term$a k bvar-db)))
           :hints (("goal" :use ((:instance bvar-db-orderedp-necc (n (nfix k))))))))
                    
  (local (defthmd nfix-when-natp-bfr-varname-fix
           (implies (natp (bfr-varname-fix x))
                    (equal (nfix x) (bfr-varname-fix x)))
           :hints(("Goal" :in-theory (enable bfr-varname-fix aig-var-fix acl2::aig-var-p)))))
                       
  ;; (defthm bfr-lookup-in-bvar-db-fix-env-aig-mode-blah
  ;;   (implies (and (natp (bfr-varname-fix k))
  ;;                 (case-split (< (bfr-varname-fix k) (nfix next)))
  ;;                 (case-split (<= (nfix base) (bfr-varname-fix k)))
  ;;                 (<= (base-bvar$a bvar-db) (bfr-varname-fix k))
  ;;                 (< (bfr-varname-fix k) (next-bvar$a bvar-db))
  ;;                 (bfr-mode)
  ;;                 (bvar-db-orderedp t bvar-db))
  ;;            (equal (bfr-lookup k (bvar-db-fix-env next base bvar-db t bfr-env var-env))
  ;;                   (bool-fix (glcp-generic-geval (get-bvar->term k bvar-db)
  ;;                                                 (cons (bvar-db-fix-env next base bvar-db t bfr-env var-env)
  ;;                                                       var-env)))))
  ;;   :hints(("Goal" :in-theory (enable bvar-db-fix-env bfr-param-env
  ;;                                     nfix-when-natp-bfr-varname-fix
  ;;                                     glcp-generic-geval-normalize-env-when-glmc-gobj-to-term
  ;;                                     glcp-generic-geval-normalize-env-when-glmc-gobj-list-to-terms))))

  (local (defthm set-difference-under-iff
           (iff (set-difference$ a b)
                (not (subsetp a b)))
           :hints (("goal" :cases ((consp (set-difference$ a b))))
                   (acl2::set-reasoning))))

  (defthm lookup-in-glmc-bvar-db-to-state-updates-strong
    (equal (hons-assoc-equal k
                             (GLMC-BVAR-DB-TO-STATE-UPDATES idx state-vars bvar-db))
           (and (natp k)
                (<= (nfix idx) k)
                (< k (next-bvar$a bvar-db))
                (b* ((gobj (get-bvar->term k bvar-db))
                     ((mv er term) (glmc-gobj-to-term gobj)))
                  (and (intersectp state-vars (gobj-vars gobj))
                       (not er)
                       (subsetp (gobj-vars gobj) state-vars)
                       (cons k term)))))
    :hints(("Goal" :in-theory (enable glmc-bvar-db-to-state-updates)
            :induct t)))

; Note.  We suddenly shift to only considering aig-mode -- (bfr-mode)=t --
; here, even after going to some significant effort to treat bdd-mode equally.
; Why?  For the moment, we don't deal with BDDs because BDD parametrization
; causes variable numbers to be "smeared" around -- a given variable isn't
; necessarily strictly a state or input variable, but might be one under some
; conditions and the other under others.  We could support this, potentially,
; by dealing with parametrization inside bfr-mcrun.

  (defthm-gobj-flag
    (defthm glcp-generic-geval-of-normalize-var-alist
      (implies (subsetp (gobj-vars x) vars)
               (equal (glcp-generic-geval x (cons bfr-env
                                                  (alist-extract-incl-unbound vars var-env)))
                      (glcp-generic-geval x (cons bfr-env var-env))))
      :hints ('(:expand ((:with glcp-generic-geval (:free (env) (glcp-generic-geval x env)))
                         (gobj-vars x))))
      :flag gobj)
    (defthm glcp-generic-geval-list-of-normalize-var-alist
      (implies (subsetp (gobj-list-vars x) vars)
               (equal (glcp-generic-geval-list x (cons bfr-env
                                                  (alist-extract-incl-unbound vars var-env)))
                      (glcp-generic-geval-list x (cons bfr-env var-env))))
      :hints ('(:expand ((:free (env) (glcp-generic-geval-list x env))
                         (gobj-list-vars x))))
      :flag list))


  (defthm-gobj-flag
    (defthm glcp-generic-geval-of-append-var-alists-subset
      (implies (subsetp (gobj-vars x) (alist-keys var-env1))
               (equal (glcp-generic-geval x (cons bfr-env (append var-env1 var-env2)))
                      (glcp-generic-geval x (cons bfr-env var-env1))))
      :hints ('(:expand ((:with glcp-generic-geval (:free (env) (glcp-generic-geval x env)))
                         (gobj-vars x))))
      :flag gobj)
    (defthm glcp-generic-geval-list-of-append-var-alists-subset
      (implies (subsetp (gobj-list-vars x) (alist-keys var-env1))
               (equal (glcp-generic-geval-list x (cons bfr-env (append var-env1 var-env2)))
                      (glcp-generic-geval-list x (cons bfr-env var-env1))))
      :hints ('(:expand ((:free (env) (glcp-generic-geval-list x env))
                         (gobj-list-vars x))))
      :flag list))


  (defthm-gobj-flag
    (defthm glcp-generic-geval-of-append-var-alists-no-intersect
      (implies (not (intersectp (gobj-vars x) (alist-keys var-env1)))
               (equal (glcp-generic-geval x (cons bfr-env (append var-env1 var-env2)))
                      (glcp-generic-geval x (cons bfr-env var-env2))))
      :hints ('(:expand ((:with glcp-generic-geval (:free (env) (glcp-generic-geval x env)))
                         (gobj-vars x))))
      :flag gobj)
    (defthm glcp-generic-geval-list-of-append-var-alists-no-intersect
      (implies (not (intersectp (gobj-list-vars x) (alist-keys var-env1)))
               (equal (glcp-generic-geval-list x (cons bfr-env (append var-env1 var-env2)))
                      (glcp-generic-geval-list x (cons bfr-env var-env2))))
      :hints ('(:expand ((:free (env) (glcp-generic-geval-list x env))
                         (gobj-list-vars x))))
      :flag list))

  (defthm-gobj-flag
    (defthm glcp-generic-geval-of-no-vars
      (implies (and (syntaxp (not (equal var-env ''nil)))
                    (not (consp (gobj-vars x))))
               (equal (glcp-generic-geval x (cons bfr-env var-env))
                      (glcp-generic-geval x (cons bfr-env nil))))
      :hints ('(:expand ((:with glcp-generic-geval (:free (env) (glcp-generic-geval x env)))
                         (gobj-vars x))))
      :flag gobj)
    (defthm glcp-generic-geval-list-of-no-vars
      (implies (and (syntaxp (not (equal var-env ''nil)))
                    (not (consp (gobj-list-vars x))))
               (equal (glcp-generic-geval-list x (cons bfr-env var-env))
                      (glcp-generic-geval-list x (cons bfr-env nil))))
      :hints ('(:expand ((:free (env) (glcp-generic-geval-list x env))
                         (gobj-list-vars x))))
      :flag list))

  (defthm glcp-generic-geval-ev-alist-of-append
    (equal (glcp-generic-geval-ev-alist (append a b) env)
           (append (glcp-generic-geval-ev-alist a env)
                   (glcp-generic-geval-ev-alist b env)))
    :hints(("Goal" :in-theory (enable glcp-generic-geval-ev-alist))))

  (defthm member-of-shape-spec-vars-of-lookup
    (implies (not (member v (shape-spec-list-vars (shape-spec-bindings->sspecs x))))
             (not (member v (shape-spec-vars (cadr (hons-assoc-equal k x))))))
    :hints(("Goal" :in-theory (enable shape-spec-list-vars hons-assoc-equal shape-spec-bindings->sspecs))))

  (defthm subsetp-of-lookup-implies-not-intersect-other
    (implies (and (subsetp vars (shape-spec-vars (cadr (hons-assoc-equal k x))))
                  (not (intersectp-equal (shape-spec-list-vars (shape-spec-bindings->sspecs x))
                                         (shape-spec-vars y))))
             (not (intersectp-equal vars (shape-spec-vars y))))
    :hints ((acl2::set-reasoning)))

  (defthm geval-with-shape-spec-list-invert-when-gobj-vars-subset-of-lookup-shape-spec-vars
    (implies (and (subsetp (gobj-vars gobj) (shape-spec-vars (cadr (hons-assoc-equal st-var x))))
                  (no-duplicatesp (shape-spec-list-vars (shape-spec-bindings->sspecs x)))
                  (shape-spec-bindingsp x))
             (equal (glcp-generic-geval gobj (cons bfr-env
                                                   (glcp-generic-geval-ev-alist
                                                    (mv-nth 1 (shape-spec-list-invert
                                                               (shape-spec-bindings->sspecs x)
                                                               (alist-keys x)))
                                                    alist)))
                    (glcp-generic-geval gobj (cons bfr-env
                                                   (glcp-generic-geval-ev-alist
                                                    (mv-nth 1 (shape-spec-invert
                                                               (cadr (hons-assoc-equal st-var x))
                                                               st-var))
                                                    alist)))))
    :hints (("goal" :induct (shape-spec-bindings->sspecs x)
             :in-theory (enable shape-spec-bindings->sspecs
                                shape-spec-list-vars
                                shape-spec-bindingsp
                                shape-spec-list-invert
                                alist-keys hons-assoc-equal))))


  ;; (defthm geval-with-shape-spec-list-invert-when-gobj-vars-subset-of-lookup-shape-spec-vars-param
  ;;   (implies (and (subsetp (gobj-vars (gobj-to-param-space gobj p))
  ;;                          (shape-spec-vars (cadr (hons-assoc-equal st-var x))))
  ;;                 (no-duplicatesp (shape-spec-list-vars (shape-spec-bindings->sspecs x)))
  ;;                 (shape-spec-bindingsp x))
  ;;            (equal (glcp-generic-geval gobj (cons (bfr-unparam-env p bfr-env)
  ;;                                                  (glcp-generic-geval-ev-alist
  ;;                                                   (mv-nth 1 (shape-spec-list-invert
  ;;                                                              (shape-spec-bindings->sspecs x)
  ;;                                                              (alist-keys x)))
  ;;                                                   alist)))
  ;;                   (glcp-generic-geval gobj (cons (bfr-unparam-env p bfr-env)
  ;;                                                  (glcp-generic-geval-ev-alist
  ;;                                                   (mv-nth 1 (shape-spec-invert
  ;;                                                              (cadr (hons-assoc-equal st-var x))
  ;;                                                              st-var))
  ;;                                                   alist)))))
  ;;   :hints (("goal" :use ((:instance geval-with-shape-spec-list-invert-when-gobj-vars-subset-of-lookup-shape-spec-vars
  ;;                          (gobj (gobj-to-param-space gobj p))))
  ;;            :in-theory (e/d (genv-unparam)
  ;;                            (geval-with-shape-spec-list-invert-when-gobj-vars-subset-of-lookup-shape-spec-vars)))))



  (local (defthm base-bvar-of-glmc-generic-mcheck-main-interps
           (b* (((glmc-config+ config)))
             (implies (not (mv-nth 2 (glmc-generic-interp-hyps config nil nil state)))
                      (equal (base-bvar$a (mv-nth 10 (glmc-generic-mcheck-main-interps config nil nil state)))
                             (shape-spec-max-bvar-list
                              (shape-spec-bindings->sspecs config.shape-spec-alist)))))
           :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps)))))


  ;; (defthm get-bvar->term-of-main-interps-when-hyp
  ;;   (b* (((mv & & & & & hyp-bfr & & er & bvar-db)
  ;;         (glmc-generic-mcheck-main-interps config nil nil state)))
  ;;     (implies (and (< (nfix n) (next-bvar$a (mv-nth 4 (Glmc-generic-interp-hyps config nil nil state))))
  ;;                   (not er))
  ;;              (equal (get-bvar->term$a n bvar-db)
  ;;                     (get-bvar->term$a n (parametrize-bvar-db
  ;;                                          hyp-bfr
  ;;                                          (mv-nth 4 (Glmc-generic-interp-hyps config nil nil state))
  ;;                                          nil)))))
  ;;   :hints (("goal" :use ((:instance BVAR-DB-EXTENSION-PRESERVES-GET-BVAR->TERM
  ;;                          (new (mv-nth 10 (glmc-generic-mcheck-main-interps config nil nil state)))
  ;;                          (old (parametrize-bvar-db
  ;;                                (bfr-and (mv-nth 1 (Glmc-generic-interp-hyps config nil nil state))
  ;;                                         (mv-nth 0 (Glmc-generic-interp-hyps config nil nil state)))
  ;;                                (mv-nth 4 (Glmc-generic-interp-hyps config nil nil state))
  ;;                                nil))
  ;;                          (v n)))
  ;;            :in-theory (disable bvar-db-extension-preserves-get-bvar->term))))
                           
  
  ;; (local (in-theory (enable (force))))

  (std::defret base-bvar-of-glmc-generic-mcheck-to-fsm
    (b* (((glmc-config+ config)))
      (implies (not er)
               (Equal (base-bvar$a new-bvar-db)
                      (shape-spec-max-bvar-list
                       (shape-spec-bindings->sspecs config.shape-spec-alist)))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-main-interps))))

  (std::defret bfr-lookup-in-glmc-generic-mcheck-env-out-of-range
    (b* (((glmc-config+ config))
         (fix-env (glmc-generic-mcheck-env alist config state)))
      (implies (and (bfr-mode)
                    (not er)
                    (not (and (integerp (bfr-varname-fix k))
                              (<= (shape-spec-max-bvar-list
                                   (shape-spec-bindings->sspecs
                                    config.shape-spec-alist))
                                  (bfr-varname-fix k))
                              (< (bfr-varname-fix k)
                                 (next-bvar$a new-bvar-db)))))
               (equal (bfr-lookup k (car fix-env))
                      (bfr-lookup k (car (glmc-cov-env config alist))))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-env))))

  (local (in-theory (disable glmc-generic-mcheck-to-fsm)))


  (std::defret lookup-in-glmc-generic-mcheck-env
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm))
         (env (glmc-generic-mcheck-env alist config state)))
      (implies (and (not er)
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (glmc-config-p config)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses fsm.interp-clauses))
                    (glcp-generic-geval-ev
                     (shape-spec-list-oblig-term
                      (shape-spec-bindings->sspecs config.shape-spec-alist)
                      (alist-keys config.shape-spec-alist))
                     alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (bfr-mode))
               (equal (bfr-lookup n (car env))
                      (b* ((n (bfr-varname-fix n)))
                        (if (and (natp n)
                                 (< n (next-bvar$a new-bvar-db))
                                 (<= (shape-spec-max-bvar-list
                                      (shape-spec-bindings->sspecs config.shape-spec-alist))
                                     n))
                            (bool-fix (glcp-generic-geval (get-bvar->term$a n new-bvar-db) env))
                          (bfr-lookup n (car (glmc-cov-env config alist))))))))
    :hints ((and stable-under-simplificationp
                 (subsetp-equal '((not (integerp (bfr-varname-fix n)))
                                  (not (< (bfr-varname-fix N)
                                          (NEXT-BVAR$A (MV-NTH '2
                                                               (GLMC-GENERIC-MCHECK-TO-FSM CONFIG 'NIL 'NIL
                                                                                           STATE)))))
                                  (< (bfr-varname-fix N)
                                     (SHAPE-SPEC-MAX-BVAR-LIST
                                      (SHAPE-SPEC-BINDINGS->SSPECS
                                       (GLCP-CONFIG->SHAPE-SPEC-ALIST$INLINE
                                        (GLMC-CONFIG->GLCP-CONFIG$INLINE CONFIG))))))
                                clause)
                     '(:use ((:instance glmc-generic-mcheck-env-correct-for-glmc-generic-mcheck-to-fsm)
                             (:instance glcp-generic-bvar-db-env-ok-necc
                              (n (bfr-varname-fix n))
                              (bvar-db (mv-nth 2 (glmc-generic-mcheck-to-fsm config bvar-db nil state)))
                              (p t)
                              (bound (next-bvar$a (mv-nth 2 (glmc-generic-mcheck-to-fsm config bvar-db nil state))))
                              (env (glmc-generic-mcheck-env alist config state))))
                       :in-theory (disable glmc-generic-mcheck-env-correct-for-glmc-generic-mcheck-to-fsm))))
    :otf-flg t)

  

  (std::defret get-bvar->term-below-hyp-bound-of-glcp-generic-mcheck-to-fsm
    (b* (((glmc-fsm fsm)))
      (implies (and (<= (base-bvar$a new-bvar-db) (nfix n))
                    (< (nfix n) fsm.hyp-var-bound))
               (equal (get-bvar->term$a n new-bvar-db)
                      (gobj-to-param-space
                       (get-bvar->term$a n (glmc-hyp-bvar-db config state))
                       fsm.hyp))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-to-fsm))))

  (std::defret glmc-generic-mcheck-to-fsm-hyp-var-bound
    (b* (((glmc-fsm fsm)))
      (implies (not er)
               (equal fsm.hyp-var-bound
                      (next-bvar$a (glmc-hyp-bvar-db config state)))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-to-fsm
                                      glmc-generic-mcheck-main-interps
                                      glmc-hyp-bvar-db))))

  (std::defret lookup-in-glmc-generic-mcheck-env-hyp
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm))
         (env (glmc-generic-mcheck-env alist config state))
         (hyp-bvar-db (glmc-hyp-bvar-db config state)))
      (implies (and (not er)
                    (glmc-config-p config)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses fsm.interp-clauses))
                    (glcp-generic-geval-ev
                     (shape-spec-list-oblig-term
                      (shape-spec-bindings->sspecs config.shape-spec-alist)
                      (alist-keys config.shape-spec-alist))
                     alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (bfr-mode)
                    (not (and (natp (bfr-varname-fix n))
                              (<= fsm.hyp-var-bound (bfr-varname-fix n)))))
               (equal (bfr-lookup n (car env))
                      (b* ((n (bfr-varname-fix n)))
                        (if (and (natp n)
                                 (<= (shape-spec-max-bvar-list
                                      (shape-spec-bindings->sspecs config.shape-spec-alist))
                                     n))
                            (bool-fix (glcp-generic-geval (get-bvar->term$a n hyp-bvar-db) env))
                          (bfr-lookup n (car (glmc-cov-env config alist))))))))
    :hints ((and stable-under-simplificationp
                 (subsetp-equal '((not (integerp (bfr-varname-fix n)))
                                  (< (bfr-varname-fix N)
                                     (SHAPE-SPEC-MAX-BVAR-LIST
                                      (SHAPE-SPEC-BINDINGS->SSPECS
                                       (GLCP-CONFIG->SHAPE-SPEC-ALIST$INLINE
                                        (GLMC-CONFIG->GLCP-CONFIG$INLINE CONFIG))))))
                                clause)
                     '(:use ((:instance glmc-generic-mcheck-env-correct-for-glmc-generic-mcheck-to-fsm-hyp)
                             (:instance glcp-generic-bvar-db-env-ok-necc
                              (n (bfr-varname-fix n))
                              (bvar-db (glmc-hyp-bvar-db config state))
                              (p t)
                              (bound (next-bvar$a (glmc-hyp-bvar-db config state)))
                              (env (glmc-generic-mcheck-env alist config state))))
                       :in-theory (disable glmc-generic-mcheck-env-correct-for-glmc-generic-mcheck-to-fsm-hyp))))
    :otf-flg t)

  (local (in-theory (disable lookup-in-glmc-generic-extract-state-bits)))
   
  

  (local (defthm lookup-in-glmc-generic-extract-state-bits-out-of-range
           (b* (((glmc-config+ config))
                (statebits (glmc-generic-extract-state-bits (cdr (hons-assoc-equal config.st-var alist))
                                                            config bvar-db)))
             (implies (and (not (glmc-syntax-checks config))
                           (bfr-varname-p k)
                           (member k
                                   (glmc-generic-state-bvars config bvar-db))
                           (not (and (natp k)
                                     (<= (base-bvar$a bvar-db) k)
                                     (< k (next-bvar$a bvar-db))))
                           (glmc-config-p config)
                           (<= (shape-spec-max-bvar-list
                                (shape-spec-bindings->sspecs config.shape-spec-alist))
                               (base-bvar$a bvar-db)))
                      (equal (cdr (hons-assoc-equal k statebits))
                             (bfr-lookup k (car (glmc-cov-env config alist))))))
           :hints(("Goal" :in-theory (e/d (glmc-generic-state-bvars
                                           glmc-generic-extract-state-bits
                                           glmc-cov-env
                                           NORMALIZE-ALIST-OF-SHAPE-SPEC-INVERT-LOOKUP)
                                          (member-shape-spec-list-indices-implies-less-than-max
                                           member-shape-spec-indices-implies-less-than-max))))))

  (local (defthm eval-glmc-generic-mcheck-env-when-glmc-gobj-to-term
           (implies (not (mv-nth 0 (glmc-gobj-to-term x)))
                    (equal (glcp-generic-geval x (glmc-generic-mcheck-env alist config state))
                           (glcp-generic-geval x (glmc-cov-env config alist))))
           :hints(("Goal" :in-theory (enable glmc-generic-mcheck-env
                                             glmc-generic-mcheck-main-interps-env
                                             glmc-cov-env
                                             glcp-generic-geval-normalize-env-when-glmc-gobj-to-term)))))

  (local (defthm normalize-geval-of-gobj-to-term-invert-env
           (b* (((glmc-config+ config)))
             (implies (And (NOT (MV-NTH 0 (GLMC-GOBJ-TO-TERM x)))
                           (SUBSETP-EQUAL
                            (GOBJ-VARS x)
                            (SHAPE-SPEC-VARS
                             (CADR
                              (HONS-ASSOC-EQUAL
                               config.st-var config.shape-spec-alist))))
                           (glmc-config-p config)
                           (not (glmc-syntax-checks config)))
                      (equal (glcp-generic-geval
                              x
                              (cons nil (glcp-generic-geval-ev-alist
                                         (mv-nth 1 (shape-spec-invert
                                                    (cadr (hons-assoc-equal
                                                           config.st-var config.shape-spec-alist))
                                                    config.st-var))
                                         (list (cons config.st-var (cdr (hons-assoc-equal config.st-var alist)))))))
                             (glcp-generic-geval x (glmc-cov-env config alist)))))
           :hints(("Goal" :in-theory (enable glmc-cov-env
                                             NORMALIZE-GEVAL-ALIST-OF-SHAPE-SPEC-INVERT-LOOKUP
                                             glcp-generic-geval-normalize-env-when-glmc-gobj-to-term)))))
                                               

  (local (defthm lookup-in-glmc-generic-extract-state-bits-in-range
           (b* (((glmc-config+ config))
                (statebits (glmc-generic-extract-state-bits (cdr (hons-assoc-equal config.st-var alist))
                                                            config bvar-db)))
             (implies (and (not (glmc-syntax-checks config))
                           (bfr-varname-p k)
                           (member k (glmc-generic-state-bvars config bvar-db))
                           (<= (base-bvar$a bvar-db) k)
                           (< k (next-bvar$a bvar-db))
                           (glmc-config-p config)
                           (<= (shape-spec-max-bvar-list
                                (shape-spec-bindings->sspecs config.shape-spec-alist))
                               (base-bvar$a bvar-db))
                           ;; (glcp-generic-bvar-db-env-ok
                           ;;  bvar-db t (next-bvar$a bvar-db)
                           ;;  (GLMC-GENERIC-MCHECK-ENV ALIST CONFIG STATE))
                           (bfr-mode))
                      (equal (cdr (hons-assoc-equal k statebits))
                             (bool-fix (glcp-generic-geval
                                        (get-bvar->term$a k bvar-db)
                                        (glmc-cov-env config alist)
                                        ;; (glmc-generic-mcheck-env alist config state)
                                        )))))
           :hints(("Goal" :in-theory (e/d (glmc-generic-state-bvars
                                           glmc-generic-extract-state-bits
                                           ;; glmc-cov-env
                                           bfr-unparam-env)
                                          (glcp-generic-bvar-db-env-ok-necc))
                   ;; :use ((:instance glcp-generic-bvar-db-env-ok-necc
                   ;;        (n k)
                   ;;        (bound (next-bvar$a bvar-db))
                   ;;        (env (glmc-generic-mcheck-env alist config state))))
                   ))))

  (local (defthm lookup-in-glmc-generic-extract-state-bits-in-range-of-glmc-generic-mcheck-env
           (b* (((glmc-config+ config)))
             (implies (and (not (glmc-syntax-checks config))
                           (member (bfr-varname-fix k) (glmc-generic-state-bvars config bvar-db))
                           (<= (base-bvar$a bvar-db) (bfr-varname-fix k))
                           (< (bfr-varname-fix k) (next-bvar$a bvar-db))
                           (glmc-config-p config)
                           (<= (shape-spec-max-bvar-list
                                (shape-spec-bindings->sspecs config.shape-spec-alist))
                               (base-bvar$a bvar-db))
                           ;; (glcp-generic-bvar-db-env-ok
                           ;;  bvar-db t (next-bvar$a bvar-db)
                           ;;  (GLMC-GENERIC-MCHECK-ENV ALIST CONFIG STATE))
                           (bfr-mode))
                      (equal (glcp-generic-geval
                              (get-bvar->term$a k bvar-db)
                              (glmc-generic-mcheck-env alist config state))
                             (glcp-generic-geval
                              (get-bvar->term$a k bvar-db)
                              (glmc-cov-env config alist)))))
           :hints(("Goal" :in-theory (e/d (glmc-generic-state-bvars
                                           ;; glmc-generic-mcheck-env
                                           ;; glmc-cov-env
                                           bfr-unparam-env))))))

;; Tricky part: we need to show that the st-hyp bfr evaluates correctly under
;; the composed alist (bfr-env-override term in the theorem below) even when
;; the hyps aren't true.
;; We know that in this situation glmc-generic-mcheck-env is consistent with
;; the post-hyps bvar-db, but perhaps not the final bvar-db.  However, the state update vars never depend on the bfr part of the 

  ;; (local (defthm lookup-in-glmc-generic-extract-state-bits-in-range-hyp
  ;;          (b* (((glmc-config+ config))
  ;;               (statebits (glmc-generic-extract-state-bits (cdr (hons-assoc-equal config.st-var alist))
  ;;                                                           config bvar-db)))
  ;;            (implies (and (not (glmc-syntax-checks config))
  ;;                          (bfr-varname-p k)
  ;;                          (member k (glmc-generic-state-bvars config bvar-db))
  ;;                          (<= (base-bvar$a bvar-db) k)
  ;;                          (< k (next-bvar$a bvar-db))
  ;;                          (glmc-config-p config)
  ;;                          (<= (shape-spec-max-bvar-list
  ;;                               (shape-spec-bindings->sspecs config.shape-spec-alist))
  ;;                              (base-bvar$a bvar-db))
  ;;                          (bind-free '((state . state)))
  ;;                          (glcp-generic-bvar-db-env-ok
  ;;                           (mv-nth 4 (glbvar-db t 
  ;;                           (GLMC-GENERIC-MCHECK-ENV ALIST CONFIG STATE))
  ;;                          (bfr-mode))
  ;;                     (equal (cdr (hons-assoc-equal k statebits))
  ;;                            (bool-fix (glcp-generic-geval
  ;;                                       (get-bvar->term$a k bvar-db)
  ;;                                       (glmc-generic-mcheck-env alist config state))))))
  ;;          :hints(("Goal" :in-theory (e/d (glmc-generic-state-bvars
  ;;                                          glmc-generic-extract-state-bits
  ;;                                          ;; glmc-cov-env
  ;;                                          bfr-unparam-env)
  ;;                                         (glcp-generic-bvar-db-env-ok-necc))
  ;;                  :use ((:instance glcp-generic-bvar-db-env-ok-necc
  ;;                         (n k)
  ;;                         (bound (next-bvar$a bvar-db))
  ;;                         (env (glmc-generic-mcheck-env alist config state))))))))
                          
                    

  (std::defret glmc-generic-mcheck-to-fsm-bfr-mc-env-correct
    (b* (((glmc-config+ config))
         ((glmc-fsm fsm))
         ;; (new-bvar-db (glmc-generic-mcheck-to-fsm-bvar-db config state))
         (env (glmc-generic-mcheck-env alist config state)))
      (implies (and (not er)
                    (bfr-mode)
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (glmc-config-p config)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses fsm.interp-clauses))
                    (glcp-generic-geval-ev
                     (shape-spec-list-oblig-term
                      (shape-spec-bindings->sspecs config.shape-spec-alist)
                      (alist-keys config.shape-spec-alist))
                     alist)
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (equal bfr-env (car env))
                    (equal curr-st (cdr (hons-assoc-equal config.st-var alist))))
               (bfr-env-equiv (bfr-env-override (glmc-generic-state-bvars config new-bvar-db)
                                                (slice-to-bdd-env
                                                 (glmc-generic-extract-state-bits
                                                  curr-st config 
                                                  new-bvar-db)
                                                 nil)
                                                (car env))
                              (car env))))
    :hints((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
           (acl2::introduce-vars)))


  
  (std::defret glmc-generic-mcheck-to-fsm-var-bound-gte-hyp-var-bound
    (implies (not er)
             (<= (next-bvar$a (glmc-hyp-bvar-db config state))
                 (next-bvar$A new-bvar-db)))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-to-fsm
                                      glmc-generic-mcheck-main-interps
                                      glmc-hyp-bvar-db)))
    :rule-classes :linear)

  ;; BOZO.  We need to prove the following theorem in order to add the st-hyp
  ;; into the invariant property -- the above isn't good enough because it has
  ;; the evaluation of the st-hyp as a hyp.  We need to show that the
  ;; correspondence holds for variables bounded below the hyp-bvar-bound even
  ;; when the hyps aren't true.  Generally, the parametrized bvar-db's values
  ;; don't correspond to anything when the hyps don't hold.  We hoped to argue
  ;; that the only bvars that we take as states have no dependence on BFRs, so
  ;; it doesn't matter if they're parametrized, but this is wrong because
  ;; parametrization could remove an actual dependence on BFRs.  So it seems we
  ;; need to compute the next-state using both the hyp-bvar-db and regular
  ;; bvar-db in order to get around this.

  ;; (std::defret glmc-generic-mcheck-to-fsm-bfr-mc-env-correct-for-hyp-lookup
  ;;   (b* (((glmc-config+ config))
  ;;        ((glmc-fsm fsm))
  ;;        ;; (new-bvar-db (glmc-generic-mcheck-to-fsm-bvar-db config state))
  ;;        (env (glmc-generic-mcheck-env alist config state)))
  ;;     (implies (and (not er)
  ;;                   (bfr-mode)
  ;;                   (glmc-config-p config)
  ;;                   (glcp-generic-geval-ev-theoremp
  ;;                    (conjoin-clauses fsm.interp-clauses))
  ;;                   (glcp-generic-geval-ev
  ;;                    (shape-spec-list-oblig-term
  ;;                     (shape-spec-bindings->sspecs config.shape-spec-alist)
  ;;                     (alist-keys config.shape-spec-alist))
  ;;                    alist)
  ;;                   (acl2::interp-defs-alistp config.overrides)
  ;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                   (equal (w state0) (w state))
  ;;                   (equal bfr-env (car env))
  ;;                   (equal curr-st (cdr (hons-assoc-equal config.st-var alist)))
  ;;                   (natp (bfr-varname-fix k))
  ;;                   (< (bfr-varname-fix k) fsm.hyp-var-bound))
  ;;              (equal (bfr-lookup k (bfr-env-override (glmc-generic-state-bvars config new-bvar-db)
  ;;                                                     (slice-to-bdd-env
  ;;                                                      (glmc-generic-extract-state-bits
  ;;                                                       curr-st config 
  ;;                                                       new-bvar-db)
  ;;                                                      nil)
  ;;                                                     (car env)))
  ;;                     (bfr-lookup k (car env)))))
  ;;   :hints (("goal" :Cases ((and (<= (shape-spec-max-bvar-list
  ;;                                     (shape-spec-bindings->sspecs
  ;;                                      (glcp-config->shape-spec-alist (glmc-config->glcp-config config))))
  ;;                                    (bfr-varname-fix k))
  ;;                                (< (bfr-varname-fix k)
  ;;                                   (next-bvar$a
  ;;                                    (mv-nth 2 (glmc-generic-mcheck-to-fsm config nil state)))))))))


  ;; (std::defret glmc-generic-mcheck-to-fsm-eval-initst-under-slice
  ;;   (b* (((glmc-config+ config))
  ;;        ((glmc-fsm fsm))
  ;;        ;; (new-bvar-db (glmc-generic-mcheck-to-fsm-bvar-db config state))
  ;;        (env (glmc-generic-mcheck-env alist config state)))
  ;;     (implies (and (not er)
  ;;                   (bfr-mode)
  ;;                   (glcp-generic-geval-ev config.st-hyp alist)
  ;;                   (glcp-generic-geval-ev config.in-hyp alist)
  ;;                   (glmc-config-p config)
  ;;                   (glcp-generic-geval-ev-theoremp
  ;;                    (conjoin-clauses fsm.interp-clauses))
  ;;                   (glcp-generic-geval-ev
  ;;                    (shape-spec-list-oblig-term
  ;;                     (shape-spec-bindings->sspecs config.shape-spec-alist)
  ;;                     (alist-keys config.shape-spec-alist))
  ;;                    alist)
  ;;                   (acl2::interp-defs-alistp config.overrides)
  ;;                   (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
  ;;                   (equal (w state0) (w state))
  ;;                   (equal bfr-env (car env))
  ;;                   (equal curr-st (cdr (hons-assoc-equal config.st-var alist))))
  ;;              (equal (bfr-eval fsm.initst
  ;;                               (slice-to-bdd-env
  ;;                                (glmc-generic-extract-state-bits
  ;;                                 curr-st config 
  ;;                                 new-bvar-db)
  ;;                                nil))
  ;;                     (glcp-generic-geval-ev config.initstp alist))))
  ;;   :hints (("goal" :use ((:instance )

  (local (defthm pbfr-vars-bounded-deparameterize
           (implies (and (pbfr-vars-bounded n p x)
                         (bfr-mode))
                    (pbfr-vars-bounded n t x))
           :hints (("goal" :use ((:instance pbfr-vars-bounded-necc
                                  (m (pbfr-vars-bounded-witness n t x))))
                    :expand ((pbfr-vars-bounded n t x))
                    :in-theory (e/d (pbfr-depends-on bfr-depends-on bfr-from-param-space)
                                    (set::in-tail))))))
  
  (local (defthm pbfr-list-vars-bounded-deparameterize
           (implies (and (pbfr-list-vars-bounded n p x)
                         (bfr-mode))
                    (pbfr-list-vars-bounded n t x))
           :hints(("Goal" :in-theory (enable pbfr-list-vars-bounded)))))

  (std::defret bfr-updates->states-of-glmc-generic-mcheck-to-fsm
    (b* (((glmc-fsm fsm)))
      (implies (and (glmc-config-p config)
                    (not er))
               (equal (bfr-updates->states fsm.nextst)
                      (glmc-generic-state-bvars config new-bvar-db))))
    :hints(("Goal" :in-theory (enable glmc-generic-mcheck-to-fsm))))

  )





(define glmc-generic-term-level-mcrun ((config glmc-config-p) curr-st alists)
  :measure (len alists)
  (b* (((when (atom alists)) t)
       ((glmc-config config))
       (alist (cons (cons config.st-var curr-st) (car alists)))
       (in-hyp (glcp-generic-geval-ev config.in-hyp alist))
       (binding-alist (glmc-generic-ev-bindinglist config.bindings (acl2::alist-fix alist)))
       (nextst (glcp-generic-geval-ev config.nextst binding-alist))
       (constr (glcp-generic-geval-ev config.constr binding-alist))
       (prop   (glcp-generic-geval-ev config.prop binding-alist))
       (st-hyp-next (glcp-generic-geval-ev config.st-hyp (list (cons config.st-var nextst))))
       ((unless (and constr in-hyp)) t)
       ((unless (and prop st-hyp-next)) nil))
    (glmc-generic-term-level-mcrun config nextst (cdr alists))))



(local (defthm glcp-generic-geval-ev-of-state-only-terms
         (b* (((glmc-config+ config)))
           (implies (and (syntaxp (not (case-match env
                                         (('cons ('cons & &) ''nil) t)
                                         (& nil))))
                         (glmc-config-p config)
                         (not (glmc-syntax-checks config))
                         (equal new-env (list (cons config.st-var
                                                    (cdr (hons-assoc-equal config.st-var env)))))
                         (syntaxp (not (equal new-env env))))
                    (and ;; (equal (glcp-generic-geval-ev config.initstp env)
                     ;;        (glcp-generic-geval-ev config.initstp new-env))
                     (equal (glcp-generic-geval-ev config.st-hyp env)
                            (glcp-generic-geval-ev config.st-hyp new-env)))))
         :hints (("goal" :use ((:instance GLCP-GENERIC-GEVAL-EV-OF-EXTRACT-VARIABLE-SUBSET-INCL-UNBOUND
                                (x (b* (((glmc-config+ config))) config.initstp))
                                (vars (b* (((glmc-config+ config))) (list config.st-var))))
                               (:instance GLCP-GENERIC-GEVAL-EV-OF-EXTRACT-VARIABLE-SUBSET-INCL-UNBOUND
                                (x (b* (((glmc-config+ config))) config.st-hyp))
                                (vars (b* (((glmc-config+ config))) (list config.st-var)))))
                  :in-theory (enable alist-extract-incl-unbound)))))


(local (defthm hons-assoc-equal-when-not-member-alist-keys
         (implies (not (member v (alist-keys x)))
                  (not (hons-assoc-equal v x)))))

(define glmc-generic-term-level-alists ((config glmc-config-p)
                                        alist)
  :verify-guards nil
  :measure (b* (((glmc-config config))
                (measure (glcp-generic-geval-ev config.in-measure alist)))
             (if (o-p measure) measure 0))
  :hints (("goal" :in-theory (disable o-p o<)))
  :returns (alists)
  (b* (((glmc-config config))
       (endp (glcp-generic-geval-ev config.end-ins alist))
       ((when endp) nil)
       (measure (glcp-generic-geval-ev config.in-measure alist))
       (rest-ins (glcp-generic-geval-ev-lst config.rest-ins alist))
       (frame-alist (append (pairlis$ config.frame-in-vars
                                      (glcp-generic-geval-ev-lst config.frame-ins alist))
                            (cons `(,config.st-var . ,(cdr (hons-assoc-equal config.st-var alist)))
                                  (pairlis$ config.in-vars rest-ins))))
       (binding-alist (glmc-generic-ev-bindinglist config.bindings frame-alist))
       ((unless (and (glcp-generic-geval-ev config.in-hyp frame-alist)
                     (glcp-generic-geval-ev config.constr binding-alist)
                     (glcp-generic-geval-ev config.prop binding-alist)))
        (list frame-alist))
       (nextst (glcp-generic-geval-ev config.nextst binding-alist))
       ((unless (glcp-generic-geval-ev config.st-hyp (list (cons config.st-var nextst))))
        (list frame-alist))
       (next-alist (cons `(,config.st-var . ,nextst)
                         (pairlis$ config.in-vars rest-ins)))
       (next-measure (glcp-generic-geval-ev config.in-measure next-alist))
       ((unless (and (o-p measure) (o-p next-measure) (o< next-measure measure)))
        (list frame-alist)))
    (cons frame-alist (glmc-generic-term-level-alists config next-alist)))
  ///
  (std::defret glmc-generic-term-level-alists-lookup-st-var
    (b* (((glmc-config+ config)))
      (implies (and (not (glcp-generic-geval-ev config.end-ins alist))
                    (not (glmc-clause-syntax-checks config)))
               (equal (cdr (hons-assoc-equal config.st-var (car alists)))
                      (cdr (hons-assoc-equal config.st-var alist)))))
    :hints (("goal" :do-not-induct t
             :in-theory (disable glmc-generic-term-level-alists)
             :expand ((glmc-generic-term-level-alists config alist))))))


;; ;; BOZO remove
;; (local (defthm glcp-generic-geval-ev-disjoin-cons-when-not-theoremp
;;          (implies (and (equal aa (glcp-generic-geval-ev-falsify (disjoin (cons x y))))
;;                        (syntaxp (not (equal aa a))))
;;                   (iff (glcp-generic-geval-ev (disjoin (cons x y)) a)
;;                        (or (glcp-generic-geval-ev x a)
;;                            (glcp-generic-geval-ev (disjoin y) a))))))

;; (local (in-theory (disable glcp-generic-geval-ev-disjoin-cons)))
       


(defsection glmc-measure-clauses
  (local (in-theory (enable glmc-measure-clauses)))
  (local (std::set-define-current-function glmc-measure-clauses))
;; (define glmc-measure-clauses ((config glmc-config-p))
;;   :guard (not (glmc-clause-syntax-checks config))
;;   :returns (measure-clauses pseudo-term-list-listp :hyp :guard
;;                             :hints(("Goal" :in-theory (enable length pseudo-termp))))
;;   :prepwork ((local (defthm symbol-listp-when-variable-listp
;;                       (implies (variable-listp x)
;;                                (symbol-listp (list-fix x)))
;;                       :hints(("Goal" :in-theory (enable variable-listp))))))
;;   (b* (((glmc-config+ config)))
;;     (list `((not (gl-cp-hint 'measure-check))
;;             (o-p ,config.in-measure))
;;           `((not (gl-cp-hint 'measure-check))
;;             ,config.end-ins
;;             (o< ((lambda ,(list-fix config.in-vars)
;;                    ,config.in-measure)
;;                  . ,config.rest-ins)
;;                 ,config.in-measure))))
;;   ///
  (std::defret glmc-measure-clauses-correct
    (b* (((glmc-config+ config)))
      (implies (glcp-generic-geval-ev-theoremp 
                (conjoin-clauses measure-clauses))
               (and (o-p (glcp-generic-geval-ev config.in-measure alist))
                    (implies (not (glcp-generic-geval-ev config.end-ins alist))
                             (o< (glcp-generic-geval-ev config.in-measure
                                                        (pairlis$ config.in-vars
                                                                  (glcp-generic-geval-ev-lst config.rest-ins alist)))
                                 (glcp-generic-geval-ev config.in-measure alist))))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-falsify-sufficient
                           (a alist) (x (conjoin-clauses (glmc-measure-clauses config)))))))))

(defsection glmc-run-check-clause
  (local (in-theory (enable glmc-run-check-clause)))
  (local (std::set-define-current-function glmc-run-check-clause))
;; (define glmc-run-check-clause ((config glmc-config-p))
;;   :guard (not (glmc-clause-syntax-checks config))
;;   :returns (run-clause pseudo-term-listp :hyp :Guard
;;                        :hints(("Goal" :in-theory (enable length  pseudo-termp))))
;;   :prepwork ((local (defthm pseudo-term-listp-when-variable-listp
;;                       (implies (and (variable-listp x)
;;                                     (true-listp x))
;;                                (pseudo-term-listp x))
;;                       :hints(("Goal" :in-theory (enable pseudo-term-listp variable-listp  pseudo-termp)))))
;;              (local (defthm symbol-listp-when-variable-listp
;;                       (implies (and (variable-listp x)
;;                                     (true-listp x))
;;                                (symbol-listp x))
;;                       :hints(("Goal" :in-theory (enable variable-listp)))))
;;              (local (defthm pseudo-term-listp-append
;;                       (implies (and (pseudo-term-listp (list-fix x))
;;                                     (pseudo-term-listp y))
;;                                (pseudo-term-listp (append x y))))))
;;   (b* (((glmc-config+ config)))
;;     `((not (gl-cp-hint 'run-check))
;;      (not (if ,config.end-ins
;;               't
;;             ((lambda (,@(list-fix config.frame-in-vars) ,@(list-fix config.in-vars) ,config.st-var)
;;                (if (not ,config.st-hyp)
;;                    'nil
;;                  (if (not ,config.in-hyp)
;;                      't
;;                    (if (not ,config.constr)
;;                        't
;;                      (if (not ,config.prop)
;;                          'nil
;;                        ((lambda (,@(list-fix config.in-vars) ,config.st-var)
;;                           ,config.run)
;;                         ,@(list-fix config.in-vars) ,config.nextst))))))
;;              ,@config.frame-ins
;;              ,@config.rest-ins
;;              ,config.st-var)))
;;       ,config.run))
;;   ///
  (local (defthm glcp-generic-geval-ev-lst-of-actual-cons
           (equal (glcp-generic-geval-ev-lst (cons x y) a)
                  (cons (glcp-generic-geval-ev x a)
                        (glcp-generic-geval-ev-lst y a)))))

  (local (defthm glcp-generic-geval-ev-lst-of-append
           (equal (glcp-generic-geval-ev-lst (append x y) a)
                  (append (glcp-generic-geval-ev-lst x a)
                          (glcp-generic-geval-ev-lst y a)))))

  (local (defthm len-of-glcp-generic-geval-ev-lst
           (equal (len (glcp-generic-geval-ev-lst x a))
                  (len x))))

  (local (in-theory (disable glcp-generic-geval-ev-lst-of-cons)))

  (local (defthm pairlis$-of-append
           (implies (equal (len a) (len c))
                    (equal (pairlis$ (append a b) (append c d))
                           (append (pairlis$ a c)
                                   (pairlis$ b d))))
           :hints(("Goal" :in-theory (enable pairlis$ append)))))

  (local (defthm glcp-generic-geval-ev-when-variablep
           (implies (variablep x)
                    (equal (glcp-generic-geval-ev x alist)
                           (cdr (hons-assoc-equal x alist))))
           :hints(("Goal" :in-theory (enable variablep)))))

  (local (defthm glcp-generic-geval-ev-lst-vars-of-append-when-no-intersection
           (implies (and (variable-listp vars)
                         (not (intersectp-equal vars (alist-keys a))))
                    (equal (glcp-generic-geval-ev-lst vars (append a b))
                           (glcp-generic-geval-ev-lst vars b)))
           :hints(("Goal" :in-theory (enable variable-listp intersectp-equal)))))

  (local (defthm glcp-generic-geval-ev-lst-vars-of-cons-irrel
           (implies (and (variable-listp vars)
                         (not (member v vars)))
                    (equal (glcp-generic-geval-ev-lst vars (cons (cons v val) a))
                           (glcp-generic-geval-ev-lst vars a)))
           :hints(("Goal" :in-theory (enable member variable-listp
                                             glcp-generic-geval-ev-lst-of-cons)))))

  (local (defthm glcp-generic-geval-ev-lst-vars-of-append-pairlis$
           (implies (and (variable-listp vars)
                         (equal (len vars) (len vals))
                         (no-duplicatesp vars))
                    (equal (glcp-generic-geval-ev-lst vars (append (pairlis$ vars vals) b))
                           (list-fix vals)))
           :hints(("Goal" :in-theory (enable variable-listp no-duplicatesp pairlis$
                                             glcp-generic-geval-ev-lst-of-cons)
                   :induct (pairlis$ vars vals)))))

  (local (in-theory (enable glcp-generic-geval-ev-of-nonsymbol-atom)))

    (acl2::defthm-simple-term-vars-flag
    (defthm glcp-generic-geval-ev-of-cons-redundant
      (implies (and (equal val (cdr (hons-assoc-equal var al))))
               (equal (glcp-generic-geval-ev x (cons (cons var val) al))
                      (glcp-generic-geval-ev x al)))
      :hints ('(:in-theory (enable glcp-generic-geval-ev-of-fncall-args pseudo-termp)))
      :flag simple-term-vars)
    (defthm glcp-generic-geval-ev-lst-of-cons-redundant
      (implies (and (equal val (cdr (hons-assoc-equal var al))))
               (equal (glcp-generic-geval-ev-lst x (cons (cons var val) al))
                      (glcp-generic-geval-ev-lst x al)))
      :flag simple-term-vars-lst))

  (local (defthm assoc-is-hons-assoc
           (implies k
                    (equal (assoc k x) (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (acl2::defthm-simple-term-vars-flag
    (defthm glcp-generic-geval-ev-of-normalize-append-cons
      (implies (and (not (hons-assoc-equal var a))
                    (not (hons-assoc-equal var b)))
               (and (equal (glcp-generic-geval-ev x (append a b (cons (cons var val) c)))
                           (glcp-generic-geval-ev x (cons (cons var val) (append a b c))))
                    (equal (glcp-generic-geval-ev x (append a (cons (cons var val) b)))
                           (glcp-generic-geval-ev x (cons (cons var val) (append a b))))))
      :hints ('(:in-theory (enable glcp-generic-geval-ev-of-fncall-args pseudo-termp)))
      :flag simple-term-vars)
    (defthm glcp-generic-geval-ev-lst-of-normalize-append-cons
      (implies (and (not (hons-assoc-equal var a))
                    (not (hons-assoc-equal var b)))
               (and (equal (glcp-generic-geval-ev-lst x (append a b (cons (cons var val) c)))
                           (glcp-generic-geval-ev-lst x (cons (cons var val) (append a b c))))
                    (equal (glcp-generic-geval-ev-lst x (append a (cons (cons var val) b)))
                           (glcp-generic-geval-ev-lst x (cons (cons var val) (append a b))))))
      :flag simple-term-vars-lst))

  (acl2::defthm-simple-term-vars-flag
    (defthm glcp-generic-geval-ev-of-alist-fix
      (equal (glcp-generic-geval-ev x (acl2::alist-fix a))
             (glcp-generic-geval-ev x a))
      :hints ('(:in-theory (enable glcp-generic-geval-ev-of-fncall-args pseudo-termp)))
      :flag simple-term-vars)
    (defthm glcp-generic-geval-ev-lst-of-alist-fix
      (equal (glcp-generic-geval-ev-lst x (acl2::alist-fix a))
             (glcp-generic-geval-ev-lst x a))
      :flag simple-term-vars-lst))

  (defthm glmc-generic-ev-bindinglist-of-normalize-append-cons
    (implies (and (not (hons-assoc-equal var a))
                  (not (hons-assoc-equal var b)))
             (and (equal (glcp-generic-geval-ev body (glmc-generic-ev-bindinglist x (append a b (cons (cons var val) c))))
                         (glcp-generic-geval-ev body (glmc-generic-ev-bindinglist x (cons (cons var val) (append a b c)))))
                  (equal (glcp-generic-geval-ev body (glmc-generic-ev-bindinglist x (append a (cons (cons var val) b))))
                         (glcp-generic-geval-ev body (glmc-generic-ev-bindinglist x (cons (cons var val) (append a b)))))))
    :hints(("Goal" :use ((:instance glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars
                          (a (append a b (cons (cons var val) c)))
                          (b (cons (cons var val) (append a b c))))
                         (:instance glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars
                          (a (append a (cons (cons var val) b)))
                          (b (cons (cons var val) (append a b)))))
            :in-theory (e/d (acl2::eval-alists-agree-by-bad-guy)
                            (glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars)))))

  (defthm glmc-generic-ev-bindinglist-of-normalize-redundant-cons
    (equal (glcp-generic-geval-ev body (glmc-generic-ev-bindinglist x (cons (cons var val) (append a (cons (cons var val) b)))))
           (glcp-generic-geval-ev body (glmc-generic-ev-bindinglist x (cons (cons var val) (append a b)))))
    :hints(("Goal" :use ((:instance glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars
                          (a (cons (cons var val) (append a (cons (cons var val) b))))
                          (b (cons (cons var val) (append a b)))))
            :in-theory (e/d (acl2::eval-alists-agree-by-bad-guy)
                            (glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars)))))

  (acl2::defthm-simple-term-vars-flag
    (defthm glcp-generic-geval-ev-of-cons-irrel
      (implies (not (member var (simple-term-vars x)))
               (equal (glcp-generic-geval-ev x (cons (cons var val) a))
                      (glcp-generic-geval-ev x a)))
      :hints ('(:in-theory (enable glcp-generic-geval-ev-of-fncall-args pseudo-termp)
                :expand ((simple-term-vars x))))
      :flag simple-term-vars)
    (defthm glcp-generic-geval-ev-lst-of-cons-irrel
      (implies (not (member var (simple-term-vars-lst x)))
               (equal (glcp-generic-geval-ev-lst x (cons (cons var val) a))
                      (glcp-generic-geval-ev-lst x a)))
      :hints ('(:expand ((simple-term-vars-lst x))))
      :flag simple-term-vars-lst))

  ;; (local (defthm alist-equiv-of-cons-redundant
  ;;          (implies (equal val (cdr (hons-assoc-equal var al)))
  ;;                   (acl2::alist-equiv (cons (cons var val) al) al))))

  (acl2::def-functional-instance glmc-generic-ev-bindinglist-to-lambda-nest-correct
    acl2::bindinglist-to-lambda-nest-correct
    ((acl2::unify-ev glcp-generic-geval-ev)
     (acl2::unify-ev-lst glcp-generic-geval-ev-lst)
     (acl2::unify-ev-bindinglist glmc-generic-ev-bindinglist))
    :hints ('(:in-theory (enable glmc-generic-ev-bindinglist
                                 glcp-generic-geval-ev-of-fncall-args))))


  (local (defthm symbol-listp-of-list-fix-when-variable-listp
           (implies (variable-listp x)
                    (symbol-listp (list-fix x)))
           :hints(("Goal" :in-theory (enable variable-listp)))))

  (local (defthm not-member-nil-when-variable-listp
           (implies (variable-listp x)
                    (not (member nil x)))
           :hints(("Goal" :in-theory (enable variable-listp)))))

  (local (defthm glcp-generic-geval-ev-lst-of-list-fix
           (equal (glcp-generic-geval-ev-lst (list-fix x) a)
                  (glcp-generic-geval-ev-lst x a))
           :hints(("Goal" :in-theory (enable list-fix)))))

  (local (defthm GLCP-GENERIC-GEVAL-EV-LST-OF-PAIRLIS-variable-list
           (implies (and (no-duplicatesp keys)
                         (variable-listp keys))
                    (equal (glcp-generic-geval-ev-lst keys (pairlis$ keys vals))
                           (take (len keys) vals)))
           :hints (("goal" :use ((:instance glcp-generic-geval-ev-lst-of-pairlis
                                  (keys (list-fix keys)) (vals vals)))
                    :in-theory (disable glcp-generic-geval-ev-lst-of-pairlis)
                    :do-not-induct t))))

  (local (in-theory (disable acl2::pseudo-term-listp-of-cons
                             acl2::pseudo-termp-opener
                             pseudo-termp-of-fncall
                             pseudo-term-listp-of-cons
                             append not 
                             GLCP-GENERIC-GEVAL-EV-DISJOIN-CONS
                             VARIABLEP-WHEN-MEMBER-EQUAL-OF-VARIABLE-LISTP)))

  (std::defret glmc-run-check-clause-correct
    (b* (((glmc-config+ config))
         (frame-alist ;; (append (pairlis$ config.frame-in-vars
                      ;;                   (glcp-generic-geval-ev-lst config.frame-ins alist))
                      ;;         (pairlis$ config.in-vars
                      ;;                   (glcp-generic-geval-ev-lst config.rest-ins alist))
                      ;;         (list (cons config.st-var
                      ;;                     (cdr (hons-assoc-equal config.st-var alist)))))
          (car (glmc-generic-term-level-alists config alist)))
         (bindings-alist (glmc-generic-ev-bindinglist config.bindings frame-alist)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (disjoin (glmc-run-check-clause config)))
                    (glmc-config-p config)
                    (not (glmc-clause-syntax-checks config))
                    (not (glcp-generic-geval-ev config.run alist)))
               (and (not (glcp-generic-geval-ev config.end-ins alist))
                    (glcp-generic-geval-ev config.constr bindings-alist)
                    (glcp-generic-geval-ev config.in-hyp frame-alist)
                    (implies (glcp-generic-geval-ev config.prop bindings-alist)
                             (let ((nextst-alist (append (pairlis$ config.in-vars
                                                                   (glcp-generic-geval-ev-lst config.rest-ins alist))
                                                         (list (cons config.st-var
                                                                     (glcp-generic-geval-ev config.nextst bindings-alist))))))
                               (implies (glcp-generic-geval-ev config.st-hyp nextst-alist)
                                        (not (glcp-generic-geval-ev config.run nextst-alist))))))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-falsify-sufficient
                           (x (disjoin (glmc-run-check-clause config)))
                           (a alist)))
             :in-theory (disable acl2::car-of-append))
            (and stable-under-simplificationp
                 '(:expand ((glmc-generic-term-level-alists config alist))))))

  (local (in-theory (disable glmc-run-check-clause)))


 


  (defthm glmc-generic-run-clause-check-implies-term-level-alists-correct
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (disjoin (glmc-run-check-clause config)))
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (glmc-measure-clauses config)))
                    (glmc-config-p config)
                    (not (glmc-clause-syntax-checks config))
                    (not (glmc-syntax-checks config))
                    (not (glcp-generic-geval-ev config.run alist)))
               (not (glmc-generic-term-level-mcrun
                     config
                     (cdr (hons-assoc-equal config.st-var alist))
                     (glmc-generic-term-level-alists config alist)))))
    :hints(("Goal" :induct (glmc-generic-term-level-alists config alist)
            :in-theory (enable (:i glmc-generic-term-level-alists) glmc-generic-term-level-mcrun)
            :expand ((GLMC-GENERIC-TERM-LEVEL-ALISTS CONFIG ALIST))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:use ((:instance glmc-run-check-clause-correct))
                  :in-theory (disable glmc-run-check-clause-correct)
                  :expand ((glmc-generic-term-level-alists config alist)))))))
                                                     
                                                             




                        
(defsection glmc-clause-check-clause
  (local (in-theory (enable glmc-clause-check-clause)))
  (local (std::set-define-current-function glmc-clause-check-clause))
  ;; (define glmc-clause-check-clause ((clause pseudo-term-listp)
  ;;                                           (config glmc-config-p))
  ;;   :guard (not (glmc-clause-syntax-checks config))
  ;;   :returns (clause-clause pseudo-term-listp :hyp :guard)
  ;;   ;; (implies (implies (and config.st-hyp config.initstp) config.run) clause)
  ;;   (b* (((glmc-config config)))
  ;;     `((not (gl-cp-hint 'clause-check))
  ;;       (not (implies (if ,config.initstp
  ;;                         ,config.st-hyp
  ;;                       'nil)
  ;;                     ,config.run))
  ;;       . ,clause))
  ;;   ///

  (local (defthm glcp-generic-geval-ev-when-variablep
           (implies (variablep x)
                    (equal (glcp-generic-geval-ev x a)
                           (cdr (hons-assoc-equal x a))))))

  
  (local (defthm len-of-glcp-generic-geval-ev-lst
           (equal (len (glcp-generic-geval-ev-lst x a))
                  (len x))))

  (local (defthm pairlis$-of-append
           (implies (equal (len a) (len c))
                    (equal (pairlis$ (append a b) (append c d))
                           (append (pairlis$ a c)
                                   (pairlis$ b d))))
           :hints(("Goal" :in-theory (enable pairlis$ append)))))

  (local (defthm glcp-generic-geval-ev-lst-of-append
           (equal (glcp-generic-geval-ev-lst (append x y) a)
                  (append (glcp-generic-geval-ev-lst x a)
                          (glcp-generic-geval-ev-lst y a)))))

  (local (defthm glcp-generic-geval-ev-lst-of-actual-cons
           (equal (glcp-generic-geval-ev-lst (cons x y) a)
                  (cons (glcp-generic-geval-ev x a)
                        (glcp-generic-geval-ev-lst y a)))))

  (local (in-theory (disable  append acl2::car-of-append
                              GLCP-GENERIC-GEVAL-EV-LST-OF-CONS)))

  (local (defthm hons-assoc-equal-when-not-member-alist-keys
           (implies (not (member v (alist-keys x)))
                    (not (hons-assoc-equal v x)))))

  (std::defret glmc-clause-check-clause-correct
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (disjoin clause-clause))
                    ;; (glcp-generic-geval-ev-theoremp
                    ;;  (disjoin (glmc-run-check-clause config)))
                    (not (glcp-generic-geval-ev (disjoin clause) alist))
                    (glmc-config-p config)
                    (not (glmc-syntax-checks config))
                    (not (glmc-clause-syntax-checks config)))
               (and (glcp-generic-geval-ev config.st-hyp
                                           (list (cons config.st-var
                                                       (cdr (hons-assoc-equal config.st-var alist)))))
                    (implies (consp (glmc-generic-term-level-alists config alist))
                             (let ((alist (car (glmc-generic-term-level-alists config alist))))
                               (glcp-generic-geval-ev config.initstp
                                                      (glmc-generic-ev-bindinglist
                                                       config.bindings alist))))
                    (not (glcp-generic-geval-ev config.run alist)))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-falsify-sufficient
                           (x (disjoin (glmc-clause-check-clause clause config)))
                           (a alist))
                          ;; (:instance glcp-generic-geval-ev-falsify-sufficient
                          ;;  (x (disjoin (glmc-run-check-clause config)))
                          ;;  (a alist))
                          ))
            (and stable-under-simplificationp
                 '(:expand ((glmc-generic-term-level-alists config alist)
                            ;; (glmc-run-check-clause config)
                            ))))))
                     
                    
(defsection glmc-check-st-hyp-inductive
  (local (in-theory (enable glmc-check-st-hyp-inductive)))
  (local (std::set-define-current-function glmc-check-st-hyp-inductive))
;; (define glmc-check-st-hyp-inductive ((config glmc-config-p)
;;                                      (fsm glmc-fsm-p)
;;                                      bvar-db
;;                                      state)
;;   :returns (mv er new-state)
;;   (b* (((glmc-fsm fsm))
;;        ((glmc-config+ config))
;;        ((unless (eq config.st-hyp-method :inductive-sat))
;;         ;; not our job to check here
;;         (mv nil state))
;;        (sat-problem (bfr-and (bfr-to-param-space fsm.hyp fsm.hyp)
;;                              (bfr-not fsm.st-hyp-next)))
;;        ((mv sat successp ctrex) (bfr-sat sat-problem))
;;        ((when (and sat successp))
;;         (b* (((mv er & state)
;;               (ec-call
;;                (glcp-gen/print-ctrexamples
;;                 ctrex "ERROR"
;;                 "Counterexample to state hyp inductiveness"
;;                 (change-glcp-config config.glcp-config
;;                                     :top-level-term `(implies (if ,config.in-hyp ,config.st-hyp 'nil)
;;                                                               ((lambda (,config.st-var)
;;                                                                  ,config.st-hyp)
;;                                                                ,config.nextst))
;;                                     :param-bfr fsm.hyp)
;;                 bvar-db state)))
;;              ((when er) (mv er state)))
;;           (mv (msg "Counterexamples for state hyp inductiveness found; aborting") state)))
;;        ((when successp)
;;         (mv nil state)))
;;     (mv (msg "SAT check for state hyp inductiveness failed; aborting") state)))
  (defthm glmc-check-st-hyp-inductive-correct
    (b* (((mv (glmc-fsm fsm) mcheck-er & &)
          (glmc-generic-mcheck-to-fsm config nil nil state1))
         ((mv er &) (glmc-check-st-hyp-inductive config fsm bvar-db2 state2))
         ((glmc-config+ config)))
      (implies (and (not er)
                    (not mcheck-er)
                    (equal config.st-hyp-method :inductive-sat)
                    ;; (glcp-generic-geval-ev config.st-hyp alist)
                    ;; (glcp-generic-geval-ev config.in-hyp alist)
                    (glmc-config-p config)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses fsm.interp-clauses))
                    (glcp-generic-geval-ev-theoremp (disjoin (glmc-cov-clause config)))
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state1))
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (bfr-mode))
               (glcp-generic-geval-ev config.st-hyp
                                      (list (cons config.st-var
                                                  (glcp-generic-geval-ev
                                                   config.nextst
                                                   (glmc-generic-ev-bindinglist
                                                    config.bindings alist)))))))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop (b* (((mv (glmc-fsm fsm) ?mcheck-er & &)
                                       (glmc-generic-mcheck-to-fsm config bvar-db1 nil state1)))
                                   (bfr-and (bfr-to-param-space fsm.hyp fsm.hyp)
                                            (bfr-not fsm.st-hyp-next))))
                           (env (car (glmc-generic-mcheck-env alist config state1)))))
             :in-theory (e/d (glmc-cov-clause-implies-oblig-term
                              bfr-unparam-env)
                             (bfr-sat-unsat))))))

(defsection glmc-state-hyp-is-inductive-clause
  (local (in-theory (enable glmc-state-hyp-is-inductive-clause)))
  (local (std::set-define-current-function glmc-state-hyp-is-inductive-clause))

  (std::defret glmc-state-hyp-is-inductive-clause-implies-rw
    (b* (((glmc-config+ config))
         (new-alist (list (cons config.st-var
                                (glcp-generic-geval-ev
                                 config.nextst
                                 (glmc-generic-ev-bindinglist config.bindings alist))))))
      (implies (and (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses))
                    (equal config.st-hyp-method :inductive-clause)
                    (not (glmc-syntax-checks config))
                    (glcp-generic-geval-ev config.st-hyp alist)
                    (glcp-generic-geval-ev config.in-hyp alist)
                    (glmc-config-p config))
               (glcp-generic-geval-ev config.st-hyp new-alist)))

    :hints (("goal" :use (;; (:instance glcp-generic-geval-ev-of-extract-variable-subset-incl-unbound
                          ;;  (x (glmc-config->st-hyp config))
                          ;;  (vars (list (glmc-config->st-var config)))
                          ;;  (env (list (cons config.st-var
                          ;;       (glcp-generic-geval-ev config.nextst alist)))))
                          (:instance GLCP-GENERIC-GEVAL-EV-FALSIFY-SUFFICIENT
                           (x (conjoin-clauses (glmc-state-hyp-is-inductive-clause config)))
                           (a alist)))
             :in-theory (e/d (;; alist-extract-incl-unbound hons-assoc-equal
                                                         )
                             (;; glcp-generic-geval-ev-of-extract-variable-subset-incl-unbound
                              ))))))

(defsection glmc-clause-check
  (local (in-theory (enable glmc-clause-check)))
  (local (std::set-define-current-function glmc-clause-check))
  ;; (define glmc-clause-check ((clause pseudo-term-listp)
  ;;                                    (config glmc-config-p))
  ;;   :returns (clauses pseudo-term-list-listp :hyp :guard)
  ;;   :guard (not (glmc-clause-syntax-checks config))
  ;;   ;; The clause should look something like
  ;;   ;; ((not (in-hyp-list ins))
  ;;   ;;  (not (st-hyp st))
  ;;   ;;  (not (initstp st))
  ;;   ;;  (check-run st ins))
  ;;   ;; where check-run is something like
  ;;   ;;   (cond ((atom ins) t)
  ;;   ;;         ((not (constr st (car ins))) t)
  ;;   ;;         ((not (prop st (car ins))) nil)
  ;;   ;;         (t (check-run (nextst st (car ins)) (cdr ins))))
  ;;   ;; We need to show that what we'll prove through model checking implies this clause.
  ;;   ;; We'll first show that check-run is of the appropriate form
  ;;   ;; 
  ;;   (b* (((glmc-config config)))
  ;;     (list* (glmc-clause-check-clause clause config)
  ;;            (glmc-run-check-clause config)
  ;;            (glmc-measure-clauses config)))
  ;;   ///

  (defthm glmc-clause-check-correct
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (glmc-clause-check clause config)))
                    (not (glcp-generic-geval-ev (disjoin clause) alist))
                    (glmc-config-p config)
                    (not (glmc-syntax-checks config))
                    (not (glmc-clause-syntax-checks config)))
               (not (glmc-generic-term-level-mcrun config
                                                   (cdr (hons-assoc-equal config.st-var alist))
                                                   (glmc-generic-term-level-alists
                                                    config alist)))))
    :hints (("goal" :do-not-induct t)))

  (defthm glmc-clause-check-implies-consp-alists
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (glmc-clause-check clause config)))
                    (not (glcp-generic-geval-ev (disjoin clause) alist))
                    (glmc-config-p config)
                    (not (glmc-syntax-checks config))
                    (not (glmc-clause-syntax-checks config))
                    ;; (glcp-generic-geval-ev config.st-hyp alist)
                    ;; (glcp-generic-geval-ev config.initstp alist)
                    )
               (consp (glmc-generic-term-level-alists config alist))))
    :hints (("goal" :do-not-induct t
             :use glmc-clause-check-correct
             :in-theory (disable glmc-clause-check-correct)
             :expand ((:free (st) (glmc-generic-term-level-mcrun config st nil))))))

  (defthm glmc-clause-check-correct-initst
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (glmc-clause-check clause config)))
                    (not (glcp-generic-geval-ev (disjoin clause) alist))
                    (glmc-config-p config)
                    (not (glmc-syntax-checks config))
                    (not (glmc-clause-syntax-checks config)))
               (let ((alist (car (glmc-generic-term-level-alists config alist))))
                 (glcp-generic-geval-ev config.initstp
                                        (glmc-generic-ev-bindinglist
                                         config.bindings alist)))))
    :hints (("goal" :do-not-induct t
             :use glmc-clause-check-implies-consp-alists
             :in-theory (disable glmc-clause-check-implies-consp-alists)
             ;; :expand ((glmc-generic-term-level-alists config alist))
             )))

  (defthm glmc-clause-check-correct-st-hyp
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (glmc-clause-check clause config)))
                    (not (glcp-generic-geval-ev (disjoin clause) alist))
                    (glmc-config-p config)
                    (not (glmc-syntax-checks config))
                    (not (glmc-clause-syntax-checks config)))
               (glcp-generic-geval-ev config.st-hyp (list (cons config.st-var
                                                                (cdr (hons-assoc-equal config.st-var alist)))))))
    :hints (("goal" :do-not-induct t
             :use glmc-clause-check-implies-consp-alists
             :in-theory (disable glmc-clause-check-implies-consp-alists)
             ;; :expand ((glmc-generic-term-level-alists config alist))
             )))

  (defthm glmc-clause-check-correct-st-hyp-first-alist
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (glmc-clause-check clause config)))
                    (not (glcp-generic-geval-ev (disjoin clause) alist))
                    (glmc-config-p config)
                    (not (glmc-syntax-checks config))
                    (not (glmc-clause-syntax-checks config)))
               (b* ((alist (car (glmc-generic-term-level-alists config alist))))
                 (glcp-generic-geval-ev config.st-hyp (list (cons config.st-var
                                                                  (cdr (hons-assoc-equal config.st-var alist))))))))
    :hints (("goal" :do-not-induct t
             :use glmc-clause-check-implies-consp-alists
             :in-theory (disable glmc-clause-check-implies-consp-alists))))

  (defthm glmc-clause-check-implies-in-hyp
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (glmc-clause-check clause config)))
                    (not (glcp-generic-geval-ev (disjoin clause) alist))
                    (glmc-config-p config)
                    (not (glmc-syntax-checks config))
                    (not (glmc-clause-syntax-checks config)))
               (let ((alist (car (glmc-generic-term-level-alists config alist))))
                 (glcp-generic-geval-ev config.in-hyp alist))))
    :hints (("goal" :do-not-induct t
             :use glmc-clause-check-implies-consp-alists
             :in-theory (disable glmc-clause-check-implies-consp-alists)
             ;; :expand ((glmc-generic-term-level-alists config alist))
             )))

  

  (local (defthm hons-assoc-equal-when-not-member-alist-keys
           (implies (not (member v (alist-keys x)))
                    (not (hons-assoc-equal v x)))))

  (defthm glmc-clause-check-correct-st-hyp-inductive
    (b* (((glmc-config+ config)))
      (implies (and (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses (glmc-clause-check clause config)))
                    (not (glcp-generic-geval-ev (disjoin clause) alist))
                    (glmc-config-p config)
                    (equal config.st-hyp-method :inductive-clause)
                    (not (glmc-syntax-checks config))
                    (not (glmc-clause-syntax-checks config)))
               (glcp-generic-geval-ev config.st-hyp (list (cons config.st-var
                                                                (glcp-generic-geval-ev
                                                                 config.nextst
                                                                 (glmc-generic-ev-bindinglist
                                                                  config.bindings
                                                                  (car (glmc-generic-term-level-alists
                                                                        config alist)))))))))
    :hints (("goal" :do-not-induct t
             :use glmc-clause-check-implies-consp-alists
             :in-theory (disable glmc-clause-check-implies-consp-alists)
             ;; :expand ((glmc-generic-term-level-alists config alist))
             )))

  (defthm glmc-clause-check-correct-implies-state-hyp-is-inductive-clause
    (implies (glcp-generic-geval-ev-theoremp
              (conjoin-clauses (glmc-clause-check clause config)))
             (glcp-generic-geval-ev-theoremp
              (conjoin-clauses (glmc-state-hyp-is-inductive-clause config)))))

  (std::defret glmc-clause-check-implies-measure
    (b* (((glmc-config+ config)))
      (implies (glcp-generic-geval-ev-theoremp 
                (conjoin-clauses (glmc-clause-check clause config)))
               (and (o-p (glcp-generic-geval-ev config.in-measure alist))
                    (implies (not (glcp-generic-geval-ev config.end-ins alist))
                             (o< (glcp-generic-geval-ev config.in-measure
                                                        (pairlis$ config.in-vars
                                                                  (glcp-generic-geval-ev-lst config.rest-ins alist)))
                                 (glcp-generic-geval-ev config.in-measure alist))))))))

(define glmc-mcrun-alists-to-envs ((config glmc-config-p)
                                   curr-st
                                   alists
                                   state)
  :verify-guards nil
  (b* (((when (atom alists)) nil)
       ((glmc-config config))
       (alist (cons (cons config.st-var curr-st) (car alists)))
       (bfr-env (car (glmc-generic-mcheck-env alist config state)))
       (nextst (glcp-generic-geval-ev config.nextst
                                      (glmc-generic-ev-bindinglist
                                       config.bindings alist))))
    (cons bfr-env
          (glmc-mcrun-alists-to-envs config nextst (cdr alists) state)))
  ///

  (local (defthm bfr-eval-updates-is-slice-to-bdd-env
           (implies (bfr-updates-p updates)
                    (equal (bfr-eval-updates updates env)
                           (slice-to-bdd-env (bfr-eval-alist updates env) nil)))
           :hints(("Goal" :in-theory (enable bfr-eval-alist bfr-eval-updates slice-to-bdd-env)))))

  (local (defcong bfr-env-equiv equal (bfr-eval-alist x env) 2))

  (local (in-theory (enable glmc-cov-clause-implies-oblig-term)))


  (local (defthm glmc-mcheck-full-property-when-not-prop
           (b* (((glmc-fsm fsm)))
             (implies (not (bfr-eval fsm.prop env))
                      (not (bfr-eval (glmc-mcheck-full-property config fsm) env))))
           :hints(("Goal" :in-theory (enable glmc-mcheck-full-property)))))


  (local (defthm st-hyp-next-by-all-possibilities
           (b* (((glmc-config+ config))
                ((mv (glmc-fsm fsm) er ?new-bvar-db &) (glmc-generic-mcheck-to-fsm config bvar-db interp-st state))
                ;; (envs (glmc-mcrun-alists-to-envs config curr-st alists state))
                )
             (implies (and (not er)
                           (bfr-mode)
                           (glcp-generic-geval-ev config.st-hyp `((,config.st-var . ,curr-st)))
                           (glcp-generic-geval-ev config.in-hyp alist)
                           (equal (cdr (hons-assoc-equal config.st-var alist)) curr-st)
                           (glmc-config-p config)
                           (glcp-generic-geval-ev-theoremp
                            (conjoin-clauses fsm.interp-clauses))
                           (glcp-generic-geval-ev-theoremp (disjoin (glmc-cov-clause config)))
                           (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                           (equal (w state0) (w state))
                           (glcp-generic-geval-ev-theoremp 
                            (conjoin-clauses (glmc-state-hyp-is-inductive-clause config)))
                           (not (mv-nth 0 (glmc-check-st-hyp-inductive config fsm bvar-db1 state1)))
                           (bfr-eval (glmc-mcheck-full-property config fsm)
                                     (car (glmc-generic-mcheck-env alist config state))))
                      (glcp-generic-geval-ev config.st-hyp
                                             (list (cons config.st-var
                                                         (glcp-generic-geval-ev
                                                          config.nextst
                                                          (glmc-generic-ev-bindinglist
                                                           config.bindings alist)))))))
           :hints (("goal" :cases ((equal (glmc-config->st-hyp-method config) :inductive-clause)
                                   (equal (glmc-config->st-hyp-method config) :inductive-sat))
                    :in-theory (enable glmc-mcheck-full-property)))))
                                  

  (local (defthmd alist-fix-of-append
           (equal (acl2::alist-fix (append a b))
                  (append (acl2::alist-fix a)
                          (acl2::alist-fix b)))))

  (local (in-theory (disable acl2::alist-fix-of-cons)))

  (defthm glmc-generic-ev-bindinglist-of-alist-fix
    (equal (glmc-generic-ev-bindinglist x (acl2::alist-fix a))
           (glmc-generic-ev-bindinglist x a))
    :hints(("Goal" :in-theory (enable glmc-generic-ev-bindinglist
                                      alist-fix-of-append))))

  (defthm glmc-generic-mcheck-to-fsm-translate-runs-correct
    (b* (((glmc-config+ config))
         ((mv (glmc-fsm fsm) er new-bvar-db &) (glmc-generic-mcheck-to-fsm config bvar-db interp-st state))
         (envs (glmc-mcrun-alists-to-envs config curr-st alists state)))
      (implies (and (not (glmc-generic-term-level-mcrun config curr-st alists))
                    (not er)
                    (bfr-mode)
                    (glcp-generic-geval-ev config.st-hyp `((,config.st-var . ,curr-st)))
                    (glmc-config-p config)
                    (glcp-generic-geval-ev-theoremp
                     (conjoin-clauses fsm.interp-clauses))
                    ;; in-alists checked by term-level-mcrun
                    (glcp-generic-geval-ev-theoremp (disjoin (glmc-cov-clause config)))
                    (glcp-generic-geval-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state))
                    (acl2::interp-defs-alistp config.overrides)
                    (glcp-generic-geval-ev-theoremp 
                     (conjoin-clauses (glmc-state-hyp-is-inductive-clause config)))
                    (not (mv-nth 0 (glmc-check-st-hyp-inductive config fsm bvar-db1 state1))))
               (not (bfr-constrained-mcrun
                     (glmc-mcheck-full-property config fsm)
                     (bfr-and fsm.fsm-constr fsm.bit-constr (bfr-to-param-space fsm.hyp fsm.hyp))
                     fsm.nextst
                     (slice-to-bdd-env
                      (glmc-generic-extract-state-bits
                       curr-st config new-bvar-db)
                      nil)
                     envs))))
    :hints(("Goal" :in-theory (enable glmc-generic-term-level-mcrun bfr-unparam-env)
            :induct (glmc-generic-term-level-mcrun config curr-st alists)
            :expand ((glmc-generic-term-level-mcrun config curr-st alists)
                     (glmc-mcrun-alists-to-envs config curr-st alists state)
                     (:free (prop constr nextst curr-st a b)
                      (bfr-constrained-mcrun prop constr nextst curr-st (cons a b))))
            :do-not-induct t))))






    

       
       
(local (defthm pseudo-term-list-listp-of-append
         (implies (and (pseudo-term-list-listp a)
                       (pseudo-term-list-listp b))
                  (pseudo-term-list-listp (append a b)))
         :hints(("Goal" :in-theory (enable pseudo-term-list-listp)))))

(defsection glmc-generic
  (local (in-theory (enable glmc-generic)))
  (local (std::set-define-current-function glmc-generic))
  (verify-guards glmc-generic)

  (std::defret pseudo-term-list-listp-of-glmc-generic-new-clauses
    (implies (pseudo-term-listp clause)
             (pseudo-term-list-listp new-clauses)))
;; (define glmc-generic ((clause pseudo-term-listp)
;;                              config
;;                              state)
;;   :returns (mv er
;;                (new-clauses pseudo-term-list-listp :hyp :guard)
;;                new-state)
;;   (b* (((unless (glmc-config-p config))
;;         (mv "Bad GLMC config" nil state))
;;        ((glmc-config+ config))
;;        ((unless (acl2::interp-defs-alistp config.overrides))
;;         (mv "Bad overrides in GLMC config" nil state))
;;        (er (glmc-clause-syntax-checks config))
;;        ((when er)
;;         (mv er nil state))
;;        ((unless (bfr-mode))
;;         (mv "Glmc only works in AIG mode" nil state))
;;        ((acl2::local-stobjs bvar-db)
;;         (mv er clauses bvar-db state))
;;        ((mv (glmc-fsm fsm) er bvar-db state)
;;         (glmc-generic-mcheck-to-fsm config bvar-db state))
;;        ((when er)
;;         (mv er nil bvar-db state))

;;        ((mv er state) (glmc-check-st-hyp-inductive config fsm bvar-db state))
;;        ((when er)
;;         (mv er nil bvar-db state))

;;        ((mv er state) (glmc-fsm-perform-mcheck config fsm bvar-db state))
;;        ((when er)
;;         (mv er nil bvar-db state))

;;        (clause-clauses (glmc-clause-check clause config))
;;        (cov-clause (glmc-cov-clause config)))
;;     (mv nil
;;         (cons cov-clause
;;               (append clause-clauses
;;                       (glmc-fsm->interp-clauses fsm)))
;;         bvar-db state))
;;   ///
   (local (defthm bfr-mcheck-correct-rw
           (b* (((mv result ?ctrex-initst ?ctrex-ins) (bfr-mcheck prop constr updates initstp max-bvar)))
             (implies (and (bind-free
                            `((init-st . (slice-to-bdd-env
                                          (glmc-generic-extract-state-bits
                                           (cdr (hons-assoc-equal
                                                 (glmc-config->st-var$inline
                                                  (mv-nth '1 (glmc-config-load-overrides config state)))
                                                 a))
                                           (mv-nth '1 (glmc-config-load-overrides config state))
                                           (mv-nth '2 (glmc-generic-mcheck-to-fsm
                                                       (mv-nth '1 (glmc-config-load-overrides config state))
                                                       'nil 'nil state)))
                                          'nil))
                              (ins . (glmc-mcrun-alists-to-envs
                                      (mv-nth '1 (glmc-config-load-overrides config state))
                                      (cdr (hons-assoc-equal
                                            (glmc-config->st-var$inline
                                             (mv-nth '1 (glmc-config-load-overrides config state)))
                                            a))
                                      (glmc-generic-term-level-alists
                                       (mv-nth '1 (glmc-config-load-overrides config state)) a)
                                      state))))
                           (bfr-eval initstp (bfr-env-override (bfr-updates->states updates)
                                                               init-st
                                                               (car ins)))
                           (pbfr-vars-bounded max-bvar t prop)
                           (pbfr-vars-bounded max-bvar t constr)
                           (pbfr-vars-bounded max-bvar t initstp)
                           (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                           (bfr-varlist-bounded max-bvar (bfr-updates->states updates)))
                      (iff (equal result :proved)
                           (and (hide (equal result :proved))
                                (bfr-constrained-mcrun prop constr updates init-st ins)))))
           :hints (("goal" :use bfr-mcheck-proof-correct
                    :in-theory (disable bfr-mcheck-proof-correct)
                    :expand ((:free (x) (hide x))))
                   (and stable-under-simplificationp
                        '(:expand ((bfr-constrained-mcrun prop constr updates init-st ins)))))))

  (local (defthm consp-of-glmc-mcrun-alists-to-envs
           (equal (consp (glmc-mcrun-alists-to-envs config curr-st alists state))
                  (consp alists))
           :hints(("Goal" :in-theory (enable glmc-mcrun-alists-to-envs)))))

  (local (defthm glcp-generic-geval-ev-of-state-only-terms
           (b* (((glmc-config+ config)))
             (implies (and (syntaxp (not (case-match env
                                           (('cons ('cons & &) ''nil) t)
                                           (& nil))))
                           (glmc-config-p config)
                           (not (glmc-syntax-checks config))
                           (equal new-env (list (cons config.st-var
                                                      (cdr (hons-assoc-equal config.st-var env)))))
                           (syntaxp (not (equal new-env env))))
                      (and ;; (equal (glcp-generic-geval-ev config.initstp env)
                           ;;        (glcp-generic-geval-ev config.initstp new-env))
                           (equal (glcp-generic-geval-ev config.st-hyp env)
                                  (glcp-generic-geval-ev config.st-hyp new-env)))))
           :hints (("goal" :use ((:instance GLCP-GENERIC-GEVAL-EV-OF-EXTRACT-VARIABLE-SUBSET-INCL-UNBOUND
                                  (x (b* (((glmc-config+ config))) config.initstp))
                                  (vars (b* (((glmc-config+ config))) (list config.st-var))))
                                 (:instance GLCP-GENERIC-GEVAL-EV-OF-EXTRACT-VARIABLE-SUBSET-INCL-UNBOUND
                                  (x (b* (((glmc-config+ config))) config.st-hyp))
                                  (vars (b* (((glmc-config+ config))) (list config.st-var)))))
                    :in-theory (enable alist-extract-incl-unbound)))))

  ;; (defthm glmc-clause-check-correct-state-only
  ;;   (b* (((glmc-config+ config)))
  ;;     (implies (and (glcp-generic-geval-ev-theoremp
  ;;                    (conjoin-clauses (glmc-clause-check clause config)))
  ;;                   (not (glcp-generic-geval-ev (disjoin clause) alist))
  ;;                   (glmc-config-p config)
  ;;                   (not (glmc-syntax-checks config))
  ;;                   (not (glmc-clause-syntax-checks config)))
  ;;              (let ((alist (list (cons config.st-var (cdr (hons-assoc-equal config.st-var alist))))))
  ;;                (and (glcp-generic-geval-ev config.st-hyp alist)
  ;;                     ;; (glcp-generic-geval-ev config.initstp alist)
  ;;                     ))))
  ;;   :hints (("goal" :do-not-induct t
  ;;            :use glmc-clause-check-correct
  ;;            :in-theory (disable glmc-clause-check-correct))))

  (local (defthm hons-assoc-equal-when-not-member-alist-keys
           (implies (not (member v (alist-keys x)))
                    (not (hons-assoc-equal v x)))))

  (local (defthm st-var-lookup-in-glmc-generic-term-level-alists
           (b* (((glmc-config+ config))
                (alists (glmc-generic-term-level-alists config a)))
             (implies (and (consp alists)
                           (not (glmc-clause-syntax-checks config)))
                      (equal (cdr (hons-assoc-equal config.st-var (car alists)))
                             (cdr (hons-assoc-equal config.st-var a)))))
           :hints (("goal" :expand ((glmc-generic-term-level-alists config a))))))


  (defthm car-of-glmc-mcrun-alists-to-envs
    (equal (car (glmc-mcrun-alists-to-envs config curr-st alists state))
           (and (consp alists)
                (car (glmc-generic-mcheck-env
                      (cons (cons (glmc-config->st-var config) curr-st)
                            (car alists))
                      config state))))
    :hints(("Goal" :expand ((glmc-mcrun-alists-to-envs config curr-st alists state))
            :do-not-induct t)))

  (local (in-theory (enable glmc-cov-clause-implies-oblig-term)))

  ;; (local (defthm base-bvar-of-glmc-generic-mcheck-to-fsm
  ;;          (b* (((mv & er new-bvar-db &)
  ;;                (glmc-generic-mcheck-to-fsm config bvar-db state))
  ;;               ((glmc-config+ config)))
  ;;            (implies (not er)
  ;;                     (equal (base-bvar$a new-bvar-db)
  ;;                            (shape-spec-max-bvar-list
  ;;                             (shape-spec-bindings->sspecs config.shape-spec-alist)))))
  ;;          :hints(("Goal" :in-theory (enable glmc-generic-mcheck-to-fsm
  ;;                                            glmc-generic-mcheck-main-interps)))))

  (local (defthm fsm-var-bound-is-bvar-db-next
           (b* (((mv (glmc-fsm fsm) er new-bvar-db &)
                 (glmc-generic-mcheck-to-fsm config bvar-db interp-st state)))
             (implies (not er)
                      (equal fsm.var-bound (next-bvar$a new-bvar-db))))
           :hints(("Goal" :in-theory (enable glmc-generic-mcheck-to-fsm)))))


  (local (defthm pbfr-vars-bounded-of-to-param-space-in-aig-mode
           (implies (and (pbfr-vars-bounded k t x)
                         (bfr-mode))
                    (pbfr-vars-bounded k t (bfr-to-param-space p x)))
           :hints (("goal" :use PBFR-VARS-BOUNDED-OF-BFR-TO-PARAM-SPACE
                    :in-theory (disable pbfr-vars-bounded-of-bfr-to-param-space)))))

  (local (defthm pbfr-vars-bounded-of-glmc-mcheck-full-property
           (b* (((glmc-fsm fsm)))
             (implies (and (pbfr-vars-bounded p t fsm.st-hyp-next)
                           (pbfr-vars-bounded p t fsm.prop))
                      (pbfr-vars-bounded p t (glmc-mcheck-full-property config fsm))))
           :hints(("Goal" :in-theory (enable glmc-mcheck-full-property)))))

  (local
   (defthm glmc-generic-ev-bindinglist-of-remove-extra-st-var-binding
     (b* (((glmc-config+ config))
          (alist (car (glmc-generic-term-level-alists config a))))
       (implies (and ;; (acl2::bindinglist-p x)
                     ;; (pseudo-termp body)
                     (not (glmc-clause-syntax-checks config))
                     (consp (glmc-generic-term-level-alists config a)))
                (equal (glcp-generic-geval-ev
                        body
                        (glmc-generic-ev-bindinglist
                         x
                         (cons (cons config.st-var (cdr (hons-assoc-equal
                                                         config.st-var a)))
                               alist)))
                       (glcp-generic-geval-ev
                        body
                        (glmc-generic-ev-bindinglist
                         x alist)))))
     :hints(("Goal" :use ((:instance glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars
                           (a (b* (((glmc-config config)))
                                (cons (cons config.st-var (cdr (hons-assoc-equal
                                                                config.st-var a)))
                                      (car (glmc-generic-term-level-alists config a)))))
                           (b (car (glmc-generic-term-level-alists config a)))))
             :in-theory (e/d (acl2::eval-alists-agree-by-bad-guy)
                             (glmc-generic-ev-bindinglist-when-eval-alists-agree-on-free-vars))))))


  (defthm glmc-generic-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (glcp-generic-geval-ev-meta-extract-global-facts :state state)
                  (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::clauses-result
                     (glmc-generic clause config interp-st state)))))
             (glcp-generic-geval-ev (disjoin clause) a))
    ;; :hints (("goal" :cases ((CONSP (GLMC-GENERIC-TERM-LEVEL-ALISTS CONFIG A)))))
    :otf-flg t
    :rule-classes nil))
