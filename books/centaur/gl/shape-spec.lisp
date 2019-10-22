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
(include-book "shape-spec-defs")
(include-book "gtypes")
(include-book "gl-util")
(include-book "symbolic-arithmetic")
(include-book "centaur/misc/starlogic" :dir :system)
(local (include-book "gtype-thms"))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/misc/fast-alists" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/util/support" :dir :system))

(defund slice-to-bdd-env (slice env)
  (declare (xargs :guard (and (alistp slice)
                              (nat-listp (alist-keys slice)))
                  :verify-guards nil))
  (if (atom slice)
      env
    (if (mbt (Consp (car slice)))
        (bfr-set-var (caar slice) (cdar slice)
                     (slice-to-bdd-env (cdr slice) env))
      (slice-to-bdd-env (cdr slice) env))))

;; (local
;;  (defthm true-listp-slice-to-bdd-env
;;    (implies (true-listp env)
;;             (true-listp (slice-to-bdd-env slice env)))
;;    :hints(("Goal" :in-theory (enable slice-to-bdd-env)))))

(verify-guards slice-to-bdd-env
               :hints (("goal" :in-theory (enable nat-listp))))

(local
 (defthm nat-listp-true-listp
   (implies (nat-listp x)
            (true-listp x))
   :hints(("Goal" :in-theory (enable nat-listp)))
   :rule-classes (:rewrite :forward-chaining)))


(local
 (defthm nat-listp-append
   (implies (and (nat-listp a)
                 (nat-listp b))
            (nat-listp (append a b)))
   :hints(("Goal" :in-theory (enable nat-listp append)))))

(local
 (defthm true-listp-append
   (implies (true-listp b)
            (true-listp (append a b)))))



(defthm-shape-spec-flag
  (defthm nat-listp-shape-spec-indices
    (implies (shape-specp x)
             (nat-listp (shape-spec-indices x)))
    :flag ss)
  (defthm nat-listp-shape-spec-list-indices
    (implies (shape-spec-listp x)
             (nat-listp (shape-spec-list-indices x)))
    :flag list)
  :hints(("Goal" :in-theory (enable shape-specp shape-spec-listp
                                    shape-spec-indices
                                    nat-listp))))

(verify-guards shape-spec-indices
  :hints (("goal" :in-theory (enable shape-specp shape-spec-listp))))

(in-theory (disable shape-spec-indices shape-spec-list-indices))

(mutual-recursion
 (defun shape-spec-vars (x)
   (declare (xargs :guard (shape-specp x)
                   :verify-guards nil))
   (if (atom x)
       nil
     (pattern-match x
       ((g-integer &) nil)
       ((g-number &) nil)
       ((g-boolean &) nil)
       ((g-var v) (list v))
       ((g-ite if then else)
        (append (shape-spec-vars if)
                (shape-spec-vars then)
                (shape-spec-vars else)))
       ((g-concrete &) nil)
       ((g-call & args &) (shape-spec-list-vars args))
       (& (append (shape-spec-vars (car x))
                  (shape-spec-vars (cdr x)))))))
 (defun shape-spec-list-vars (x)
   (declare (xargs :guard (shape-spec-listp x)))
   (if (atom x)
       nil
     (append (shape-spec-vars (car x))
             (shape-spec-list-vars (cdr x))))))


(defthm-shape-spec-flag
  (defthm true-listp-shape-spec-vars
    (true-listp (shape-spec-vars x))
    :rule-classes :type-prescription
    :flag ss)
  (defthm true-listp-shape-spec-list-vars
    (true-listp (shape-spec-list-vars x))
    :rule-classes :type-prescription
    :flag list)
  :hints(("Goal" :in-theory (enable shape-spec-vars shape-spec-list-vars
                                    true-listp))))

(verify-guards shape-spec-vars
               :hints(("Goal" :in-theory (enable shape-specp shape-spec-listp))))

(in-theory (disable shape-spec-vars shape-spec-list-vars))






(in-theory (disable shape-spec-to-gobj
                    shape-spec-to-gobj-list))




;; (local
;;  (defthm bfr-listp-numlist-to-vars
;;    (implies (nat-listp x)
;;             (bfr-listp (numlist-to-vars x)))
;;    :hints(("Goal" :in-theory (enable numlist-to-vars nat-listp)))))

;; (local
;;  (defthm wf-g-numberp-num-spec-to-num-gobj
;;    (implies (number-specp x)
;;             (wf-g-numberp (num-spec-to-num-gobj x)))
;;    :hints(("Goal" :in-theory (enable wf-g-numberp num-spec-to-num-gobj
;;                                      number-specp)))))

;; (defthm gobjectp-shape-spec-to-gobj
;;   (implies (shape-specp x)
;;            (gobjectp (shape-spec-to-gobj x)))
;;   :hints(("Goal" :in-theory
;;           (enable gobjectp-def shape-specp shape-spec-to-gobj g-var-p
;;                   g-concrete-p tag))))


(local
 (defthm subsetp-equal-append
   (equal (subsetp-equal (append x y) z)
          (and (subsetp-equal x z)
               (subsetp-equal y z)))))


(local
 (defthm hons-assoc-equal-append
   (implies (and (alistp v1)
                 (member-equal key (alist-keys v1)))
            (equal (hons-assoc-equal key (append v1 v2))
                   (hons-assoc-equal key v1)))
   :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(local
 (defthm hons-assoc-equal-append-2
   (implies (and (alistp v1)
                 (not (member-equal key (alist-keys v1))))
            (equal (hons-assoc-equal key (append v1 v2))
                   (hons-assoc-equal key v2)))
   :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(defthm member-alist-keys-nth-slice-1
  (implies (and (integerp n)
                (<= 0 n)
                (member-equal n (alist-keys bsl1)))
           (equal (bfr-lookup n (slice-to-bdd-env (append bsl1 bsl2) env))
                  (bfr-lookup n (slice-to-bdd-env bsl1 env))))
  :hints(("Goal" :in-theory (enable slice-to-bdd-env))))

(defthm member-alist-keys-nth-slice-2
  (implies (and (integerp n)
                (<= 0 n)
                (nat-listp (alist-keys bsl1))
                (not (member-equal n (alist-keys bsl1))))
           (equal (bfr-lookup n (slice-to-bdd-env (append bsl1 bsl2) env))
                  (bfr-lookup n (slice-to-bdd-env bsl2 env))))
  :hints(("Goal" :in-theory (enable alist-keys slice-to-bdd-env nat-listp alist-keys))))



;; (local
(defthm bfr-list->s-numlist-subset-append
  (implies (and (nat-listp lst)
                (subsetp-equal lst (alist-keys bsl1)))
           (equal (bfr-list->s (numlist-to-vars lst)
                               (slice-to-bdd-env (append bsl1 bsl2) env))
                  (bfr-list->s (numlist-to-vars lst)
                               (slice-to-bdd-env bsl1 env))))
  :hints(("Goal" :in-theory (enable numlist-to-vars scdr s-endp
                                    slice-to-bdd-env
                                    subsetp-equal
                                    nat-listp)
          :induct (numlist-to-vars lst))))

(defthm bfr-list->s-numlist-no-intersect-append
  (implies (and (nat-listp lst)
                (nat-listp (alist-keys bsl1))
                (not (intersectp-equal lst (alist-keys bsl1))))
           (equal (bfr-list->s (numlist-to-vars lst)
                               (slice-to-bdd-env (append bsl1 bsl2) env))
                  (bfr-list->s (numlist-to-vars lst)
                               (slice-to-bdd-env bsl2 env))))
  :hints(("Goal" :in-theory (enable numlist-to-vars scdr s-endp
                                    slice-to-bdd-env
                                    nat-listp)
          :induct (numlist-to-vars lst)
          :expand ((:free (a b env) (bfr-list->s (cons a b) env))))))

;; (defthm bfr-list->u-numlist-subset-append
;;   (implies (and (nat-listp lst)
;;                 (subsetp-equal lst (alist-keys bsl1)))
;;            (equal (bfr-list->u (numlist-to-vars lst)
;;                                (slice-to-bdd-env (append bsl1 bsl2) env))
;;                   (bfr-list->u (numlist-to-vars lst)
;;                                (slice-to-bdd-env bsl1 env))))
;;   :hints(("Goal" :in-theory (enable numlist-to-vars scdr s-endp
;;                                     slice-to-bdd-env
;;                                     subsetp-equal
;;                                     nat-listp)
;;           :induct (numlist-to-vars lst))))

;; (defthm bfr-list->u-numlist-no-intersect-append
;;   (implies (and (nat-listp lst)
;;                 (nat-listp (alist-keys bsl1))
;;                 (not (intersectp-equal lst (alist-keys bsl1))))
;;            (equal (bfr-list->u (numlist-to-vars lst)
;;                                (slice-to-bdd-env (append bsl1 bsl2) env))
;;                   (bfr-list->u (numlist-to-vars lst)
;;                                (slice-to-bdd-env bsl2 env))))
;;   :hints(("Goal" :in-theory (enable numlist-to-vars scdr s-endp
;;                                     slice-to-bdd-env
;;                                     nat-listp)
;;           :induct (numlist-to-vars lst))))

;; (local
;;  (defthm g-boolean-p-gobj-fix
;;    (equal (g-boolean-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-boolean-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-number-p-gobj-fix
;;    (equal (g-number-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-number-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-ite-p-gobj-fix
;;    (equal (g-ite-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-ite-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-var-p-gobj-fix
;;    (equal (g-var-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-var-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-apply-p-gobj-fix
;;    (equal (g-apply-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-apply-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-concrete-p-gobj-fix
;;    (equal (g-concrete-p (gobj-fix x))
;;           (or (not (gobjectp x))
;;               (g-concrete-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))




(def-eval-g sspec-geval
  (logapp int-set-sign maybe-integer
          cons car cdr consp if not equal nth len iff
          shape-spec-slice-to-env
          ss-append-envs
          shape-spec-obj-in-range-iff
          shape-spec-obj-in-range
          shape-spec-env-slice
          shape-spec-iff-env-slice
          < acl2::logtail$inline integerp logbitp))



(local (in-theory (disable logapp integer-length
                           loghead logtail sspec-geval
                           ;;acl2::member-equal-of-alist-keys-when-member-equal-of-hons-duplicated-members-aux
                           acl2::consp-of-car-when-alistp
                           set::double-containment)))

(defun expands-with-hint (def expands)
  (if (atom expands)
      nil
    (cons `(:with ,def ,(car expands))
          (expands-with-hint def (cdr expands)))))


(local (defcong acl2::list-equiv equal (bfr-list->s x env) 1
         :hints(("Goal" :in-theory (e/d (acl2::list-equiv)
                                        (bfr-list->s-of-list-fix))
                 :use ((:instance bfr-list->s-of-list-fix)
                       (:instance bfr-list->s-of-list-fix (x x-equiv)))))))

(defthm bfr-list->s-of-append
  (implies (consp b)
           (equal (bfr-list->s (append a b) env)
                  (logapp (len a) (bfr-list->s a env)
                          (bfr-list->s b env))))
  :hints(("Goal" :in-theory (enable scdr s-endp acl2::logapp** append)
          :induct (append a b)
          :expand ((:free (a b) (bfr-list->s (cons a b) env))))))

;; (defthm bfr-list->u-of-append
;;   (equal (bfr-list->u (append a b) env)
;;          (logapp (len a) (bfr-list->u a env)
;;                  (bfr-list->u b env)))
;;   :hints(("Goal" :in-theory (enable  acl2::logapp** append)
;;           :induct (append a b)
;;           :expand ((:free (a b) (bfr-list->u (cons a b) env))))))

(local (in-theory (enable gl-cons)))

(defthm-shape-spec-flag
  (defthm shape-spec-to-gobj-eval-slice-subset-append-1
    (implies (and (shape-specp x)
                  (alistp vsl1)
                  (subsetp-equal (shape-spec-indices x)
                                 (alist-keys bsl1)))
             (equal (sspec-geval
                     (shape-spec-to-gobj x)
                     (cons (slice-to-bdd-env
                            (append bsl1 bsl2) env)
                           vsl1))
                    (sspec-geval
                     (shape-spec-to-gobj x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           vsl1))))
    :flag ss)
  (defthm shape-spec-to-gobj-list-eval-slice-subset-append-1
    (implies (and (shape-spec-listp x)
                  (alistp vsl1)
                  (subsetp-equal (shape-spec-list-indices x)
                                 (alist-keys bsl1)))
             (equal (sspec-geval-list
                     (shape-spec-to-gobj-list x)
                     (cons (slice-to-bdd-env
                            (append bsl1 bsl2) env)
                           vsl1))
                    (sspec-geval-list
                     (shape-spec-to-gobj-list x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           vsl1))))
    :flag list)
  :hints(("Goal" :in-theory (e/d (;; break-g-number
                                  ;; num-spec-to-num-gobj
                                  ;; number-spec-indices
                                  ;; number-specp
                                  subsetp-equal
                                  (:induction shape-spec-to-gobj))
                                 (member-equal
                                  acl2::list-fix-when-true-listp
                                  acl2::list-fix-when-len-zero
;acl2::consp-by-len
                                  boolean-listp
                                  binary-append))
          :expand ((shape-spec-to-gobj x)
                   (shape-spec-to-gobj-list x)
                   (shape-spec-indices x)
                   (shape-spec-list-indices x)
                   (shape-spec-vars x)
                   (shape-spec-list-vars x)
                   (shape-specp x)
                   (shape-spec-listp x)))
         (and stable-under-simplificationp
              (let ((calls1 (std::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval) nil))
                    (calls2 (std::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval-list) nil)))
                (and (or calls1 calls2)
                     `(:computed-hint-replacement t
                       :expand (,@(expands-with-hint 'sspec-geval calls1)
                                  ,@(expands-with-hint 'sspec-geval-list calls2))))))))


(defthm-shape-spec-flag
  (defthm shape-spec-to-gobj-eval-slice-subset-append-2
    (implies (and (shape-specp x)
                  (alistp vsl1)
                  (subsetp-equal (shape-spec-vars x)
                                 (alist-keys vsl1)))
             (equal (sspec-geval
                     (shape-spec-to-gobj x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           (append vsl1 vsl2)))
                    (sspec-geval
                     (shape-spec-to-gobj x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           vsl1))))
    :flag ss)
  (defthm shape-spec-to-gobj-list-eval-slice-subset-append-2
    (implies (and (shape-spec-listp x)
                  (alistp vsl1)
                  (subsetp-equal (shape-spec-list-vars x)
                                 (alist-keys vsl1)))
             (equal (sspec-geval-list
                     (shape-spec-to-gobj-list x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           (append vsl1 vsl2)))
                    (sspec-geval-list
                     (shape-spec-to-gobj-list x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           vsl1))))
    :flag list)
  :hints(("Goal" :in-theory (e/d (subsetp-equal
                                  (:induction shape-spec-to-gobj))
                                 (member-equal
                                  acl2::list-fix-when-true-listp
                                  acl2::list-fix-when-len-zero
;acl2::consp-by-len
                                  boolean-listp
                                  binary-append))
          :expand ((shape-spec-to-gobj x)
                   (shape-spec-to-gobj-list x)
                   (shape-spec-indices x)
                   (shape-spec-list-indices x)
                   (shape-spec-vars x)
                   (shape-spec-list-vars x)
                   (shape-specp x)
                   (shape-spec-listp x)))
         (and stable-under-simplificationp
              (let ((calls1 (std::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval) nil))
                    (calls2 (std::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval-list) nil)))
                (and (or calls1 calls2)
                     `(:computed-hint-replacement t
                       :expand (,@(expands-with-hint 'sspec-geval calls1)
                                  ,@(expands-with-hint 'sspec-geval-list calls2))))))))

(defthm-shape-spec-flag
  (defthm shape-spec-to-gobj-eval-slice-no-intersect-append-1
    (implies (and (shape-specp x)
                  (alistp vsl1)
                  (nat-listp (alist-keys bsl1))
                  (not (intersectp-equal
                        (shape-spec-indices x)
                        (alist-keys bsl1))))
             (equal (sspec-geval
                     (shape-spec-to-gobj x)
                     (cons (slice-to-bdd-env
                            (append bsl1 bsl2) env)
                           vsl1))
                    (sspec-geval
                     (shape-spec-to-gobj x)
                     (cons (slice-to-bdd-env
                            bsl2 env)
                           vsl1))))
    :flag ss)
  (defthm shape-spec-list-to-gobj-eval-slice-no-intersect-append-1
    (implies (and (shape-spec-listp x)
                  (alistp vsl1)
                  (nat-listp (alist-keys bsl1))
                  (not (intersectp-equal
                        (shape-spec-list-indices x)
                        (alist-keys bsl1))))
             (equal (sspec-geval-list
                     (shape-spec-to-gobj-list x)
                     (cons (slice-to-bdd-env
                            (append bsl1 bsl2) env)
                           vsl1))
                    (sspec-geval-list
                     (shape-spec-to-gobj-list x)
                     (cons (slice-to-bdd-env
                            bsl2 env)
                           vsl1))))
    :flag list)
  :hints(("Goal" :in-theory (e/d (subsetp-equal
                                  (:induction shape-spec-to-gobj))
                                 (member-equal
                                  acl2::list-fix-when-true-listp
                                  acl2::list-fix-when-len-zero
;acl2::consp-by-len
                                  boolean-listp
                                  binary-append))
          :expand ((shape-spec-to-gobj x)
                   (shape-spec-to-gobj-list x)
                   (shape-spec-indices x)
                   (shape-spec-list-indices x)
                   (shape-spec-vars x)
                   (shape-spec-list-vars x)
                   (shape-specp x)
                   (shape-spec-listp x)))
         (and stable-under-simplificationp
              (let ((calls1 (std::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval) nil))
                    (calls2 (std::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval-list) nil)))
                (and (or calls1 calls2)
                     `(:computed-hint-replacement t
                       :expand (,@(expands-with-hint 'sspec-geval calls1)
                                  ,@(expands-with-hint 'sspec-geval-list calls2))))))))


(defthm-shape-spec-flag
  (defthm shape-spec-to-gobj-eval-slice-no-intersect-append-2
    (implies (and (shape-specp x)
                  (alistp vsl1)
                  (not (intersectp-equal (shape-spec-vars x)
                                         (alist-keys vsl1))))
             (equal (sspec-geval
                     (shape-spec-to-gobj x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           (append vsl1 vsl2)))
                    (sspec-geval
                     (shape-spec-to-gobj x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           vsl2))))
    :flag ss)
  (defthm shape-spec-list-to-gobj-eval-slice-no-intersect-append-2
    (implies (and (shape-spec-listp x)
                  (alistp vsl1)
                  (not (intersectp-equal (shape-spec-list-vars x)
                                         (alist-keys vsl1))))
             (equal (sspec-geval-list
                     (shape-spec-to-gobj-list x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           (append vsl1 vsl2)))
                    (sspec-geval-list
                     (shape-spec-to-gobj-list x)
                     (cons (slice-to-bdd-env
                            bsl1 env)
                           vsl2))))
    :flag list)
  :hints(("Goal" :in-theory (e/d (subsetp-equal
                                  (:induction shape-spec-to-gobj))
                                 (member-equal
                                  acl2::list-fix-when-true-listp
                                  acl2::list-fix-when-len-zero
;acl2::consp-by-len
                                  boolean-listp
                                  binary-append))
          :expand ((shape-spec-to-gobj x)
                   (shape-spec-to-gobj-list x)
                   (shape-spec-indices x)
                   (shape-spec-list-indices x)
                   (shape-spec-vars x)
                   (shape-spec-list-vars x)
                   (shape-specp x)
                   (shape-spec-listp x)))
         (and stable-under-simplificationp
              (let ((calls1 (std::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval) nil))
                    (calls2 (std::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval-list) nil)))
                (and (or calls1 calls2)
                     `(:computed-hint-replacement t
                       :expand (,@(expands-with-hint 'sspec-geval calls1)
                                  ,@(expands-with-hint 'sspec-geval-list calls2))))))))

(local
 (defthm alist-keys-append
   (equal (alist-keys (append a b))
          (append (alist-keys a) (alist-keys b)))))


(local
 (defthm subsetp-equal-append2
   (implies (or (subsetp-equal x y)
                (subsetp-equal x z))
            (subsetp-equal x (append y z)))))

(local
 (defthm-shape-spec-flag
   (defthm shape-spec-vars-subset-cars-arbitrary-env-slice
     (equal (alist-keys (mv-nth 1 (shape-spec-arbitrary-slice x)))
            (shape-spec-vars x))
     :hints('(:expand ((shape-spec-arbitrary-slice x)
                       (shape-spec-vars x))))
     :flag ss)
   (defthm shape-spec-list-vars-subset-cars-arbitrary-env-slice
     (equal (alist-keys (mv-nth 1 (shape-spec-list-arbitrary-slice x)))
            (shape-spec-list-vars x))
     :flag list)
   :hints(("Goal" :in-theory (enable shape-spec-vars
                                     shape-spec-list-vars
                                     shape-spec-arbitrary-slice
                                     shape-spec-list-arbitrary-slice)))))

(local
 (defthm shape-spec-vars-subset-cars-iff-env-slice
   (equal
    (alist-keys (mv-nth 1 (shape-spec-iff-env-slice x obj)))
    (shape-spec-vars x))
   :hints(("Goal" :in-theory (enable shape-spec-iff-env-slice
                                     shape-spec-vars)))))

(local
 (defthm shape-spec-vars-subset-cars-env-slice
   (equal
    (alist-keys (mv-nth 1 (shape-spec-env-slice x obj)))
    (shape-spec-vars x))
   :hints(("Goal" :in-theory (enable shape-spec-env-slice
                                     shape-spec-vars)))))

(local
 (defthm subsetp-cars-integer-env-slice
   (implies (nat-listp n)
            (equal (alist-keys (integer-env-slice n m)) n))
   :hints(("Goal" :in-theory (enable integer-env-slice nat-listp)))))



(local
 (defthm nat-listp-append-nil
   (implies (nat-listp x)
            (equal (append x nil) x))
   :hints(("Goal" :in-theory (enable nat-listp)))))



(local
 (defthm-shape-spec-flag
   (defthm shape-spec-indices-subset-cars-arbitrary-env-slice
     (implies (shape-specp x)
              (equal (alist-keys (mv-nth 0 (shape-spec-arbitrary-slice x)))
                     (shape-spec-indices x)))
     :flag ss)
   (defthm shape-spec-list-indices-subset-cars-arbitrary-env-slice
     (implies (shape-spec-listp x)
              (equal (alist-keys (mv-nth 0 (shape-spec-list-arbitrary-slice x)))
                     (shape-spec-list-indices x)))
     :flag list)
   :hints (("goal" :in-theory (enable shape-spec-list-arbitrary-slice
                                      shape-spec-arbitrary-slice
                                      shape-spec-list-indices
                                      shape-spec-indices
                                      shape-spec-listp
                                      shape-specp)))))


(local
 (defthm shape-spec-indices-subset-cars-iff-env-slice
   (implies (shape-specp x)
            (equal (alist-keys (mv-nth 0 (shape-spec-iff-env-slice x obj)))
                   (shape-spec-indices x)))
   :hints (("goal" :in-theory (enable shape-spec-iff-env-slice
                                      shape-spec-indices
                                      shape-specp)))))

(local
 (defthm shape-spec-indices-subset-cars-env-slice
   (implies (shape-specp x)
            (equal (alist-keys (mv-nth 0 (shape-spec-env-slice x obj)))
                   (shape-spec-indices x)))
   :hints (("goal" :in-theory (enable shape-spec-env-slice
                                      shape-spec-indices
                                      shape-specp)))))

(local
 (defthm subsetp-equal-cons-cdr
   (implies (subsetp-equal x y)
            (subsetp-equal x (cons z y)))))

(local
 (defthm subsetp-equal-when-equal
   (subsetp-equal x x)))


;; (local(defthm no-intersect-cons-cdr
;;   (implies (and (not (intersectp-equal a b))
;;                 (not (member-equal c a)))
;;            (not (intersectp-equal a (cons c b)))))

;; (defthm no-intersect-non-cons
;;   (implies (atom b)
;;            (not (intersectp-equal a b))))

(local
 (defthm nat-listp-append
   (implies (and (nat-listp a)
                 (nat-listp b))
            (nat-listp (append a b)))
   :hints(("Goal" :in-theory (enable nat-listp)))))





(local
 (defthm sspec-geval-of-g-ite
   (equal (sspec-geval (g-ite if then else) env)
          (if (sspec-geval if env)
              (sspec-geval then env)
            (sspec-geval else env)))
   :hints(("Goal" :in-theory (enable sspec-geval)))))


(local
 (encapsulate nil

   (defthm sspec-geval-when-g-concrete-tag
     (implies (equal (tag x) :g-concrete)
              (equal (sspec-geval x env)
                     (g-concrete->obj x)))
     :hints(("Goal" :in-theory (e/d (tag sspec-geval))))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))))


(local
 (encapsulate nil
   (defthm sspec-geval-when-g-var-tag
     (implies (equal (tag x) :g-var)
              (equal (sspec-geval x env)
                     (cdr (hons-assoc-equal (g-var->name x) (cdr env)))))
     :hints(("Goal" :in-theory (enable tag sspec-geval))))))

(local (in-theory (disable member-equal equal-of-booleans-rewrite binary-append
                           intersectp-equal subsetp-equal)))

;; (in-theory (disable no-duplicates-append-implies-no-intersect))

(local (defcong iff iff (shape-spec-obj-in-range-iff x obj) 2
         :hints(("Goal" :in-theory (enable shape-spec-obj-in-range-iff)))))




(local
 (encapsulate nil
   (local (in-theory (disable set::double-containment
                              acl2::no-duplicatesp-equal-non-cons
                              ;acl2::no-duplicatesp-equal-when-atom
                              acl2::subsetp-car-member
                              acl2::append-when-not-consp
                              tag-when-atom
                              sspec-geval)))
   (defthm shape-spec-to-gobj-eval-iff-slice
     (implies (and (shape-specp x)
                   (no-duplicatesp (shape-spec-indices x))
                   (no-duplicatesp (shape-spec-vars x))
                   (shape-spec-obj-in-range-iff x obj))
              (iff (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           (mv-nth 0 (shape-spec-iff-env-slice x obj))
                           env)
                          (mv-nth 1 (shape-spec-iff-env-slice x obj))))
                   obj))
     :hints(("Goal" :in-theory (enable (:induction shape-spec-iff-env-slice))
             :induct (shape-spec-iff-env-slice x obj)
             :expand ((:free (obj) (shape-spec-iff-env-slice x obj))
                      (shape-spec-obj-in-range-iff x obj)
                      (shape-spec-obj-in-range-iff x nil)
                      (shape-spec-obj-in-range-iff x t)
                      (shape-spec-indices x)
                      (shape-spec-vars x)
                      (shape-spec-to-gobj x)
                      (shape-specp x)
                      (:free (a b env)
                             (sspec-geval (cons a b) env))))
            (and stable-under-simplificationp
                 '(:in-theory (enable slice-to-bdd-env sspec-geval sspec-geval-list)))))))

(local
 (defthm bfr-eval-list-numlist-update-non-member
   (implies (and (natp n) (nat-listp lst)
                 (not (member-equal n lst)))
            (equal (bfr-eval-list (numlist-to-vars lst)
                                  (bfr-set-var n x env))
                   (bfr-eval-list (numlist-to-vars lst) env)))
   :hints(("Goal" :in-theory (enable numlist-to-vars bfr-eval-list
                                     nat-listp member-equal)))))

(local
 (defthm bfr-list->s-numlist-update-non-member
   (implies (and (natp n) (nat-listp lst)
                 (not (member-equal n lst)))
            (equal (bfr-list->s (numlist-to-vars lst)
                                  (bfr-set-var n x env))
                   (bfr-list->s (numlist-to-vars lst) env)))
   :hints(("Goal" :in-theory (enable numlist-to-vars bfr-list->s
                                     scdr s-endp
                                     nat-listp member-equal)
          :expand ((:free (a b env) (bfr-list->s (cons a b) env)))))))




(local
 (defthm consp-numlist-to-vars
   (equal (consp (numlist-to-vars x))
          (consp x))
   :hints(("Goal" :in-theory (enable numlist-to-vars)))))



;; (local
;;  (defthm v2i-redef
;;    (equal (v2i x)
;;           (if (atom x)
;;               0
;;             (if (atom (cdr x))
;;                 (if (car x) -1 0)
;;               (logcons (if (car x) 1 0) (v2i (cdr x))))))
;;    :hints(("Goal" :in-theory (enable v2i acl2::ash**))
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable logcons))))
;;    :rule-classes ((:definition :clique (v2i)
;;                    :controller-alist ((v2i t))))))

;; (local
;;  (defthm v2n-redef
;;    (equal (v2n x)
;;           (if (atom x)
;;               0
;;             (logcons (if (car x) 1 0) (v2n (cdr x)))))
;;    :hints(("Goal" :in-theory (enable v2n acl2::ash**))
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable logcons))))
;;    :rule-classes ((:definition :clique (v2n)
;;                    :controller-alist ((v2n t))))))

(local
 (encapsulate nil
   (local (in-theory (e/d* (acl2::ihsext-recursive-redefs) (floor))))
   (defthm eval-slice-integer-env-slice
     (implies (and (integer-in-range lst n)
                   (no-duplicatesp lst)
                   (integerp n)
                   (nat-listp lst))
              (equal (bfr-list->s
                      (numlist-to-vars lst)
                      (slice-to-bdd-env (integer-env-slice lst n) env))
                     n))
     :hints(("Goal" :in-theory (enable integer-env-slice
                                       integer-in-range
                                       numlist-to-vars
                                       bfr-eval-list
                                       nat-listp scdr s-endp
                                       slice-to-bdd-env
                                       integer-env-slice
                                       logbitp
                                       logcons)
             :induct (integer-env-slice lst n)
             :expand ((:free (a b env) (bfr-list->s (cons a b) env))))))

   ;; (defthm eval-slice-bfr-list->s-natural-env-slice
   ;;   (implies (and (mv-nth 0 (natural-env-slice lst n))
   ;;                 (no-duplicatesp lst)
   ;;                 (natp n)
   ;;                 (nat-listp lst))
   ;;            (equal (bfr-list->s
   ;;                         (numlist-to-vars lst)
   ;;                         (slice-to-bdd-env (mv-nth 1 (natural-env-slice lst n)) env))
   ;;                   n))
   ;;   :hints(("Goal" :in-theory (enable natural-env-slice
   ;;                                     numlist-to-vars
   ;;                                     bfr-eval-list
   ;;                                     nat-listp
   ;;                                     slice-to-bdd-env
   ;;                                     natural-env-slice
   ;;                                     logbitp)
   ;;           :induct (natural-env-slice lst n))))

))


;; (local
;;  (defthmd g-var-p-implies-gobjectp
;;    (implies (g-var-p x)
;;             (gobjectp x))
;;    :hints (("goal" :in-theory (enable gobjectp-def g-var-p tag)))
;;    :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local
;;  (defthm gobjectp-g-number
;;    (implies (wf-g-numberp x)
;;             (gobjectp (g-number x)))
;;    :hints(("Goal" :in-theory (enable gobjectp-def g-number-p tag)))))

;; (local
;;  (defthmd g-concrete-p-gobjectp1
;;    (implies (g-concrete-p x)
;;             (gobjectp x))
;;    :hints(("Goal" :in-theory (enable gobjectp-def g-concrete-p tag)))
;;    :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local (defthm loghead-non-integer
;;          (implies (not (integerp x))
;;                   (equal (loghead n x) 0))
;;          :hints(("Goal" :in-theory (enable loghead)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local (defthm logcdr-non-integer
;;          (implies (not (integerp x))
;;                   (equal (logcdr x) 0))
;;          :hints(("Goal" :in-theory (enable logcdr)))))


(local (defun cdr-logcdr (bits x)
         (if (atom bits)
             x
           (cdr-logcdr (cdr bits) (logcdr x)))))


;; (defthm v2i-of-append
;;   (implies (consp b)
;;            (equal (v2i (append a b))
;;                   (logapp (len a) (v2n a) (v2i b))))
;;   :hints(("Goal" :in-theory (e/d* (acl2::ihsext-recursive-redefs append len))
;;           :induct (append a b))))

(defthm len-bfr-eval-list
  (equal (len (bfr-eval-list x env)) (len x)))

(defthm len-numlist-to-vars
  (equal (len (numlist-to-vars bits)) (len bits))
  :hints(("Goal" :in-theory (enable numlist-to-vars))))


(local
 (encapsulate nil
   (local (in-theory
           (e/d () (;; gobjectp-tag-rw-to-types
                    ;; gobjectp-ite-case
                    ;; sspec-geval-non-gobjectp
                    ;; break-g-number
                    set::double-containment))))

   (local (defthm g-keyword-symbolp-of-shape-spec-to-gobj
            (equal (g-keyword-symbolp (shape-spec-to-gobj x))
                   (g-keyword-symbolp x))
            :hints(("Goal" :expand ((shape-spec-to-gobj x))))))
   (local (defthm not-equal-shape-spec-to-gobj-keyword
            (implies (and (not (g-keyword-symbolp x))
                          (g-keyword-symbolp y))
                     (not (equal (shape-spec-to-gobj x) y)))
            :rule-classes ((:rewrite :backchain-limit-lst (0 1)))))
   (local (defthm g-keyword-symbolp-compound-recognizer
            (implies (g-keyword-symbolp x)
                     (and (symbolp x)
                          (not (booleanp x))))
            :rule-classes :compound-recognizer))
   (local (defthm shape-spec-to-gobj-when-atom
            (implies (atom x)
                     (equal (shape-spec-to-gobj x) x))
            :hints(("Goal" :in-theory (enable shape-spec-to-gobj)))
            :rule-classes ((:rewrite :backchain-limit-lst 0))))

   (local (defthm integer-in-range-of-nil
            (equal (integer-in-range nil obj) (equal obj 0))
            :hints(("Goal" :in-theory (enable integer-in-range)))))

   (local (defthm kwote-lst-of-cons
            (equal (kwote-lst (cons a b))
                   (cons (kwote a) (kwote-lst b)))))
   (local (in-theory (disable kwote-lst)))

   (local (defthm integerp-when-integer-in-range
            (implies (integer-in-range bits x)
                     (integerp x))
            :hints(("Goal" :in-theory (enable integer-in-range)))
            :rule-classes :forward-chaining))

   (defthm shape-spec-to-gobj-eval-slice
     (implies (and (shape-specp x)
                   (no-duplicatesp (shape-spec-indices x))
                   (no-duplicatesp (shape-spec-vars x))
                   (shape-spec-obj-in-range x obj))
              (equal (sspec-geval
                      (shape-spec-to-gobj x)
                      (cons (slice-to-bdd-env
                             (mv-nth 0 (shape-spec-env-slice x obj))
                             env)
                            (mv-nth 1 (shape-spec-env-slice x obj))))
                     obj))
     :hints(("Goal" ;; :in-theory (enable shape-spec-to-gobj
                    ;;                    shape-spec-indices
                    ;;                    shape-spec-vars
                    ;;                    shape-spec-env-slice
                    ;;                    shape-specp)
             :in-theory (enable (:i shape-spec-env-slice))
             :expand ((shape-spec-to-gobj x)
                      (shape-spec-to-gobj obj)
                      (shape-spec-obj-in-range x obj)
                      (shape-spec-indices x)
                      (shape-spec-vars x)
                      (shape-specp x)
                      (shape-spec-env-slice x obj))
             :induct (shape-spec-env-slice x obj))
            (and stable-under-simplificationp
                 '(:in-theory (enable slice-to-bdd-env)
                   :expand ((:free (x y env)
                             (sspec-geval (cons x y) env))
                            (:free (x y env)
                             (sspec-geval-list (cons x y) env)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable sspec-geval)))))))


(defund shape-spec-to-env (x obj)
  (declare (xargs :guard (shape-specp x)))
  (mv-let (bsl vsl)
    (shape-spec-env-slice x obj)
    (cons (slice-to-bdd-env bsl nil) vsl)))




(defthm shape-spec-to-gobj-eval-env
  (implies (and (shape-specp x)
                (no-duplicatesp (shape-spec-indices x))
                (no-duplicatesp (shape-spec-vars x))
                (shape-spec-obj-in-range x obj))
           (equal (sspec-geval
                   (shape-spec-to-gobj x)
                   (shape-spec-to-env x obj))
                  obj))
  :hints(("Goal" :in-theory (enable shape-spec-to-env))))




;; (defun shape-spec-to-gobj-list (x)
;;   (if (atom x)
;;       nil
;;     (cons (shape-spec-to-gobj (car x))
;;           (shape-spec-to-gobj-list (cdr x)))))

;; (defun shape-spec-listp (x)
;;   (if (atom x)
;;       (equal x nil)
;;     (and (shape-specp (car x))
;;          (shape-spec-listp (cdr x)))))

;; (defthm shape-spec-listp-impl-shape-spec-to-gobj-list
;;   (implies (shape-spec-listp x)
;;            (equal (shape-spec-to-gobj x)
;;                   (shape-spec-to-gobj-list x)))
;;   :hints(("Goal" :induct (shape-spec-to-gobj-list x)
;;           :expand ((shape-spec-to-gobj x))
;;           :in-theory (enable tag))))





(defthm shape-spec-listp-implies-shape-specp
  (implies (shape-spec-listp x)
           (shape-specp x))
  :hints(("Goal" :expand ((shape-specp x)
                          (shape-spec-listp x))
          :in-theory (enable tag)
          :induct (len x))))

















;; (defthm shape-spec-alt-definition
;;   (equal (shape-spec-obj-in-range x obj)
;;          (if (atom x)
;;              (equal obj x)
;;            (case (car x)
;;              (:g-number (number-spec-in-range (cdr x) obj))
;;              (:g-boolean (booleanp obj))
;;              (:g-var t)
;;              (:g-concrete (equal obj (cdr x)))
;;              (:g-ite (let ((test (cadr x)) (then (caddr x)) (else (cdddr x)))
;;                        (or (and (shape-spec-obj-in-range-iff test t)
;;                                 (shape-spec-obj-in-range then obj))
;;                            (and (shape-spec-obj-in-range-iff test nil)
;;                                 (shape-spec-obj-in-range else obj)))))
;;              (t (and (consp obj)
;;                      (shape-spec-obj-in-range (car x) (car obj))
;;                      (shape-spec-obj-in-range (cdr x) (cdr obj)))))))
;;   :hints(("Goal" :in-theory (enable tag g-number->num g-concrete->obj
;;                                     g-ite->test g-ite->then g-ite->else)
;;           :expand ((shape-spec-obj-in-range x obj))))
;;   :rule-classes ((:definition :controller-alist ((shape-spec-obj-in-range t
;;                                                                           nil)))))

;; (local
;;  (defun shape-spec-alt-induction (x obj)
;;    (if (atom x)
;;        (equal obj x)
;;      (case (car x)
;;        (:g-number (number-spec-in-range (cdr x) obj))
;;        (:g-boolean (booleanp obj))
;;        (:g-var t)
;;        (:g-concrete (equal obj (cdr x)))
;;        (:g-ite (let ((then (caddr x)) (else (cdddr x)))
;;                  (list (shape-spec-alt-induction then obj)
;;                        (shape-spec-alt-induction else obj))))
;;        (t (list (shape-spec-alt-induction (car x) (car obj))
;;                 (shape-spec-alt-induction (cdr x) (cdr obj))))))))



(in-theory (disable shape-spec-obj-in-range))

;; (local (in-theory (disable shape-spec-alt-definition)))


(defthm shape-spec-obj-in-range-open-cons
  (implies (and (not (g-keyword-symbolp (car obj)))
                (not (eq (car obj) :g-number))
                (not (eq (car obj) :g-call))
                (consp obj))
           (equal (shape-spec-obj-in-range obj (cons carx cdrx))
                  (and (shape-spec-obj-in-range (car obj) carx)
                       (shape-spec-obj-in-range (cdr obj) cdrx))))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range
                                    g-keyword-symbolp-def
                                    member-equal)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 0 0 0))))

(defthmd ash-1-is-expt-2
  (implies (natp n)
           (equal (ash 1 n) (expt 2 n)))
  :hints(("Goal" :in-theory (enable ash floor))))

(defthmd natp-len-minus-one
  (implies (consp X)
           (natp (+ -1 (len x)))))



(defthm shape-spec-obj-in-range-open-integer
  (and (equal (shape-spec-obj-in-range `(:g-number ,bits) x)
              (if (consp bits)
                  (and* (integerp x)
                        (<= (- (expt 2 (1- (len bits)))) x)
                        (< x (expt 2 (1- (len bits)))))
                (equal x 0)))
       (equal (shape-spec-obj-in-range `(:g-integer . ,bits) x)
              (if (consp bits)
                  (and* (integerp x)
                        (<= (- (expt 2 (1- (len bits)))) x)
                        (< x (expt 2 (1- (len bits)))))
                (equal x 0))))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range
                                    integer-in-range
                                    g-number->num
                                    g-integer->bits
                                    natp-len-minus-one
                                    ash-1-is-expt-2))))

(defthm shape-spec-obj-in-range-open-boolean
  (equal (shape-spec-obj-in-range `(:g-boolean . ,bit) x)
         (booleanp x))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range))))



(defthm shape-spec-obj-in-range-open-atom
  (implies (atom a)
           (equal (shape-spec-obj-in-range a x)
                  (equal x a)))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range
                                    g-concrete->obj)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm shape-spec-obj-in-range-backchain-atom
  (implies (and (atom a)
                (equal x a))
           (equal (shape-spec-obj-in-range a x) t))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range
                                    g-concrete->obj)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defund list-of-g-booleansp (lst)
  (if (atom lst)
      (eq lst nil)
    (and (consp (car lst))
         (eq (caar lst) :g-boolean)
         (list-of-g-booleansp (cdr lst)))))

(defthm shape-spec-obj-in-range-open-list-of-g-booleans
  (implies (list-of-g-booleansp lst)
           (equal (shape-spec-obj-in-range lst obj)
                  (and* (boolean-listp obj)
                        (equal (len obj) (len lst)))))
  :hints(("Goal" ; :induct (shape-spec-obj-in-range lst obj)
          :induct (shape-spec-obj-in-range lst obj)
          :in-theory (enable shape-spec-obj-in-range tag
                             list-of-g-booleansp
                             boolean-listp))))


(defthm shape-spec-obj-in-range-backchain-list-of-g-booleans
  (implies (and (list-of-g-booleansp lst)
                (boolean-listp obj)
                (equal (len obj) (len lst)))
           (equal (shape-spec-obj-in-range lst obj) t)))


(defthm shape-spec-obj-in-range-backchain-integer-1
  (implies (and (consp bits)
                (integerp x)
                (<= (- (expt 2 (1- (len bits)))) x)
                (< x (expt 2 (1- (len bits)))))
           (and (equal (shape-spec-obj-in-range `(:g-number ,bits) x) t)
                (equal (shape-spec-obj-in-range `(:g-integer . ,bits) x) t)))
  :hints (("goal" :use shape-spec-obj-in-range-open-integer))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil))))

(defthm shape-spec-obj-in-range-backchain-integer-2
  (implies (and (not (consp bits))
                (equal x 0))
           (and (equal (shape-spec-obj-in-range `(:g-number ,bits) x) t)
                (equal (shape-spec-obj-in-range `(:g-integer . ,bits) x) t)))
  :hints (("goal" :use shape-spec-obj-in-range-open-integer))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm shape-spec-obj-in-range-backchain-boolean
  (implies (booleanp x)
           (equal (shape-spec-obj-in-range `(:g-boolean . ,bit) x) t)))

(defthm shape-spec-obj-in-range-var
  (equal (shape-spec-obj-in-range `(:g-var . ,v) x) t)
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range tag))))

(defthm shape-spec-obj-in-range-open-concrete
  (equal (shape-spec-obj-in-range `(:g-concrete . ,obj) x)
         (equal x obj))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range tag
                                    g-concrete->obj))))



(defthm shape-spec-obj-in-range-backchain-concrete
  (implies (equal x obj)
           (equal (shape-spec-obj-in-range `(:g-concrete . ,obj) x)
                  t)))

(defthmd len-plus-one
  (implies (and (syntaxp (quotep n))
                (integerp n))
           (equal (equal (+ 1 (len lst)) n)
                  (equal (len lst) (1- n)))))

(defthmd len-zero
  (equal (equal (len lst) 0)
         (not (consp lst))))



;; These two rulesets will be used in the default coverage hints as a phased
;; simplification approach.  The backchain ruleset will be tried first to
;; reduce the goals to as few as possible clauses with conclusions that are
;; calls of shape-spec-obj-in-range on "atomic" shape specs (numbers, booleans,
;; concretes.)  Then shape-spec-obj-in-range-open will
(def-ruleset! shape-spec-obj-in-range-backchain
  '(shape-spec-obj-in-range-open-cons
    shape-spec-obj-in-range-backchain-integer-1
    shape-spec-obj-in-range-backchain-integer-2
    shape-spec-obj-in-range-backchain-boolean
    shape-spec-obj-in-range-backchain-concrete
    shape-spec-obj-in-range-backchain-atom
    shape-spec-obj-in-range-backchain-list-of-g-booleans
    shape-spec-obj-in-range-var
    car-cons cdr-cons natp-compound-recognizer
    (shape-spec-obj-in-range) (g-keyword-symbolp) (ash)
    (expt) (unary--) (binary-+) (consp) (integerp) (len)
    (car) (cdr) (booleanp) (list-of-g-booleansp) (tag)
    eql len-plus-one len-zero (zp) (boolean-listp) (true-listp)
    unsigned-byte-p signed-byte-p acl2::integer-range-p))

(def-ruleset! shape-spec-obj-in-range-open
  '(shape-spec-obj-in-range-open-cons
    shape-spec-obj-in-range-open-integer
    shape-spec-obj-in-range-open-boolean
    shape-spec-obj-in-range-open-concrete
    shape-spec-obj-in-range-open-atom
    shape-spec-obj-in-range-open-list-of-g-booleans
    shape-spec-obj-in-range-var
    acl2::and*-rem-first acl2::and*-rem-second
    acl2::iff-implies-equal-and*-1
    acl2::iff-implies-iff-and*-2
    car-cons cdr-cons natp-compound-recognizer
    (shape-spec-obj-in-range) (g-keyword-symbolp) (ash)
    (expt) (unary--) (binary-+) (consp) (integerp) (len)
    (car) (cdr) (booleanp) (list-of-g-booleansp) (tag) eql
    len-plus-one len-zero (zp) (boolean-listp) (true-listp)
    unsigned-byte-p signed-byte-p acl2::integer-range-p))



(defxdoc shape-specs
  :parents (reference)
  :short "Simplified symbolic objects useful for coverage proofs in GL."

  :long "<p>Shape specifiers are a simplified format of GL symbolic objects,
capable of representing Booleans, numbers, conses, free variables, and function
calls.  While less expressive than full-fledged symbolic objects, shape spec
objects make it easier to prove coverage lemmas necessary for proving theorems
by symbolic simulation.  Here, we document common constructions of shape-spec
objects and what it means to prove coverage.</p>

<h3>Creating Shape Spec Objects</h3>

<p>Shape spec objects are analogues of <see topic=\"@(url
gl::symbolic-objects)\">symbolic objects</see>, but with several tweaks that make
it more straightforward to prove that a given concrete object is covered:</p>
<ul>
<li>Symbolic objects contain arbitrary Boolean formulas (BDDs or AIGs), whereas
shape specifiers are restricted to contain only independent Boolean variables.
Therefore, every bit in a shape specifier is independent from every other
bit.</li>
<li>The @(':g-apply') symbolic object construct is replaced by the @(':g-call')
shape specifier construct.  The @(':g-call') object has an additional field that holds a
user-provided inverse function, which is useful for proving coverage; see @(see
g-call).</li>
</ul>

<p>Shape spec objects may be created using the following constructors
 (roughly in order of usefulness).  Additionally, a non-keyword atom is a shape
spec representing itself:</p>

<dl>

<dt>@('(G-BOOLEAN <num>)')</dt>

<dd>Represents a Boolean.  @('num') (a natural number) may not be repeated in
any other @(':G-BOOLEAN') or @(':G-NUMBER') construct in the shape-spec.</dd>

<dt>@('(G-INTEGER <list-of-nums>)')</dt>

<dd>Represents a two's-complement integer with bits corresponding to the list,
least significant bit first.  Rationals and complex rationals are also
available; see @(see SYMBOLIC-OBJECTS).  A :G-INTEGER construct with a list of
length @('N') represents integers @('X') where @('(<= (- (expt 2 (+ -1 n))) x)') and
@('(< x (expt 2 (+ -1 n)))').  The @('list-of-nums') must be natural numbers, may not
repeat, and may not occur in any other @(':G-BOOLEAN') or @(':G-INTEGER')/
@(':G-NUMBER') construct.</dd>

<dt>@('(G-NUMBER (list <list-of-nums>))')</dt>
<dd>Same as the @('G-INTEGER') form above, for backward compatibility.</dd>

<dt>@('(cons <Car> <Cdr>)')</dt>

<dd>Represents a cons; Car and Cdr should be well-formed shape specifiers.</dd>

<dt>@('(G-VAR <name>)')</dt>

<dd>A free variable that may represent any object.  This is primarily useful
when using GL's term-level capabilities; see @(see term-level-reasoning).</dd>

<dt>@('(G-CALL <fnname> <arglist> <inverse>)')</dt>

<dd>Represents a call of the named function applied to the given arguments.
The @('inverse') does not affect the symbolic object generated, which is
@('(:G-APPLY <fnname> . <arglist>)'), but is used in the coverage proof; see
@(see g-call). This construct is primarily useful when using GL's term-level
capabilities; see @(see term-level-reasoning).</dd>

<dt>@('(G-ITE <test> <then> <else>)')</dt>
<dd>Represents an if/then/else, where @('test'), @('then'), and @('else') are
shape specs.</dd>

</dl>


<h3>What is a Coverage Proof?</h3>

<p>In order to prove a theorem by symbolic simulation, one binds each variable
mentioned in the theorem to a symbolic object and then symbolically simulates
the conclusion of the theorem on these symbolic objects.  If the result is
true, what can we conclude?  It depends on the coverage of the symbolic inputs.
For example, one might symbolically simulate the term @('(< (+ A B) 7)') with
@('A') and @('B') bound to symbolic objects representing two-bit natural
numbers and recieve a result of @('T').  From this, it would be fallacious to
conclude @('(< (+ 6 8) 7)'), because the symbolic simulation didn't cover the
case where @('A') was 6 and @('B') 7.  In fact, it isn't certain that we can
conclude @('(< (+ 2 2) 7)') from our symbolic simulation, because the symbolic
object bindings for @('A') and @('B') might have interedependencies such that
@('A') and @('B') can't simultaneously represent 2.  (For example, the bindings
could be such that bit 0 of @('A') and @('B') are always opposite.)  In order
to prove a useful theorem from the result of such a symbolic simulation, we
must show that some set of concrete input vectors is covered by the symbolic
objects bound to @('A') and @('B').  But in general, it is a tough
computational problem to determine the set of concrete input vectors that are
covered by a given symbolic input vector.</p>

<p>To make these determinations easier, shape spec objects are somewhat
restricted.  Whereas symbolic objects generally use BDDs (or AIGs, depending on
the <see topic=\"@(url modes)\">mode</see>) to represent
individual Booleans or bits of numeric values (see @(see symbolic-objects)),
shape specs instead use natural numbers representing Boolean variables.
Additionally, shape specs are restricted such that no Boolean variable number may
be used more than once among the bindings for the variables of a theorem; this
prevents interdependencies among them.</p>

<p>While in general it is a difficult problem to determine whether a symbolic
object can evaluate to a given concrete object, a function
@('SHAPE-SPEC-OBJ-IN-RANGE') can make that determination about shape specs.
@('SHAPE-SPEC-OBJ-IN-RANGE') takes two arguments, a shape spec and some object,
and returns T if that object is in the coverage set of the shape spec, and NIL
otherwise.  Therefore, if we wish to conclude that shape specs bound to @('A')
and @('B') cover all two-bit natural numbers, we may prove the following
theorem:</p>

@({
 (implies (and (natp a) (< a 4)
               (natp b) (< b 4))
          (shape-spec-obj-in-range (list a-binding b-binding)
                                   (list a b)))
})

<p>When proving a theorem using the GL clause processor, variable bindings are
given as shape specs so that coverage obligations may be stated in terms of
@('SHAPE-SPEC-OBJ-IN-RANGE').  The shape specs are converted to symbolic
objects and may be parametrized based on some restrictions from the hypotheses,
restricting their range further.  Thus, in order to prove a theorem about
fixed-length natural numbers, for example, one may provide a shape specifier
that additionally covers negative integers of the given length; parametrization
can then restrict the symbolic inputs used in the simulation to only cover the
naturals, while the coverage proof may still be done using the simpler,
unparametrized shape spec.</p>")

(defxdoc g-call
  :parents (shape-specs term-level-reasoning)
  :short "A shape-spec representing a function call."
  :long
  "<p>Note: This is an advanced topic.  You should first read @(see
term-level-reasoning) to see whether this is of interest, then be familiar with
@(see shape-specs) before reading this.</p>

<p>@('G-CALL') is the constructor for a shape-spec representing a function
call.  Usage:</p>

@({
  (g-call <function name>
          <list of argument shape-specs>
          <inverse function>)
 })

<p>This yields a G-APPLY object (see @(see symbolic-objects)):</p>
@({
  (g-apply <function name>
           <list of argument symbolic objects>)
 })

<p>The inverse function field does not affect the symbolic object that is
generated from the g-call object, but it determines how we attempt to prove the
coverage obligation.</p>

<p>The basic coverage obligation for assigning some variable V a shape spec SS
is that for every possible value of V satisfying the hypotheses, there must be
an environment under which the symbolic object derived from SS evaluates to
that value.  The coverage proof must show that there exists such an
environment.</p>

<p>Providing an inverse function INV basically says:</p>

<p><box>
   \"If we need (FN ARGS) to evaluate to VAL, then ARGS should be (INV VAL).\"
</box></p>

<p>So to prove that (G-CALL FN ARGS INV) covers VAL, we first prove that ARGS
cover (INV VAL), then that (FN (INV VAL)) equals VAL.  The argument that this
works is:</p>

<ul>

<li>We first prove ARGS covers (INV VAL) -- that is, there exists some
environment E under which the symbolic objects derived from ARGS evaluate
to (INV VAL).</li>

<li>Since (FN (INV VAL)) equals VAL, this same environment E suffices to make
the symbolic object (FN ARGS) evaluate to VAL.</li>

</ul>

<p>We'll now show an example. We build on the memory example discussed in @(see
term-level-reasoning).  Suppose we want to initially assign a memory object
@('mem') a symbolic value under which address 1 has been assigned a 10-bit
integer.  That is, we want to be able to assume only the following about
@('mem'):</p>

@({
  (signed-byte-p 10 (access-mem 1 mem))
 })

<p>Assuming our memory follows the standard record rules, i.e.</p>

@({
  (update-mem addr (access-mem addr mem) mem) = mem,
})

<p>we can represent any such memory as</p>

@({
  (update-mem 1 <some 10-bit integer> <some memory>)
})

<p>Our shape-spec for this will therefore be:</p>

@({
 (g-call 'update-mem
         (list 1
               (g-integer (list 0 1 2 3 4 5 6 7 8 9)) ;; 10-bit integer
               (g-var 'mem)) ;; free variable
         <some inverse function>)
})

<p>What is an appropriate inverse?  The inverse needs to take any memory
satisfying our assumption and generate the list of necessary arguments to
update-mem that fit this template.  The following works:</p>

@({
   (lambda (m) (list 1 (access-mem 1 m) m))
})

<p>because for any value m satisfying our assumptions,</p>

<ul>

<li>the first argument returned is 1, which is covered by our shape-spec 1</li>

<li>the second argument returned will (by the assumption) be a 10-bit integer,
which is covered by our g-number shape-spec</li>

<li>the third argument returned matches our g-var shape-spec since anything at
all is covered by it</li>

<li>the final term we end up with is:
@({
        (update-mem 1 (access-mem 1 m) m)
})
    which (by the record rule above) equals m.</li>

</ul>

<p>GL tries to manage coverage proofs itself, and when using G-CALL constructs
some rules besides the ones it typically uses may be necessary -- for example,
the redundant record update rule used here.  You may add these rules to the
rulesets used for coverage proofs as follows:</p>

@({
 (acl2::add-to-ruleset gl::shape-spec-obj-in-range-backchain
                       redundant-mem-update)
 (acl2::add-to-ruleset gl::shape-spec-obj-in-range-open
                       redundant-mem-update)
})

<p>There are two rulesets because these are used in slightly different phases of
the coverage proof.</p>

<p>This feature has not yet been widely used and the detailed mechanisms
for (e.g.)  adding rules to the coverage strategy are likely to change.</p>")





(defund shape-spec-call-free (x)
  (declare (xargs :guard t))
  (or (atom x)
      (pattern-match x
        ((g-number &) t)
        ((g-boolean &) t)
        ((g-integer &) t)
        ((g-var &) t)
        ((g-ite test then else)
         (and (shape-spec-call-free test)
              (shape-spec-call-free then)
              (shape-spec-call-free else)))
        ((g-concrete &) t)
        ((g-call & & &) nil)
        (& (and (shape-spec-call-free (car x))
                (shape-spec-call-free (cdr x)))))))

(local
 (defsection shape-spec-call-free


   (local (in-theory (enable shape-spec-call-free)))

   (defthm shape-spec-call-free-by-tag
     (implies (and (or (g-keyword-symbolp (tag x))
                       (member (tag x) '(:g-number)))
                   (not (eq (tag x) :g-ite))
                   (not (eq (tag x) :g-apply))
                   (not (eq (tag x) :g-call)))
              (shape-spec-call-free x))
     :hints(("Goal" :in-theory (enable g-keyword-symbolp))))

   (Defthm shape-spec-call-free-when-atom
     (implies (not (consp x))
              (shape-spec-call-free x))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))))

(defsection car-term
  (defund car-term (x)
    (declare (xargs :guard (pseudo-termp x)))
    (if (and (consp x)
             (eq (car x) 'cons))
        (cadr x)
      `(car ,x)))
  (local (in-theory (enable car-term)))
  (defthm pseudo-termp-car-term
    (implies (pseudo-termp x)
             (pseudo-termp (car-term x))))

  (defthm car-term-correct
    (equal (sspec-geval-ev (car-term x) a)
           (car (sspec-geval-ev x a)))))

(defsection cdr-term
  (defund cdr-term (x)
    (declare (xargs :guard (pseudo-termp x)))
    (if (and (consp x)
             (eq (car x) 'cons))
        (caddr x)
      `(cdr ,x)))
  (local (in-theory (enable cdr-term)))
  (defthm pseudo-termp-cdr-term
    (implies (pseudo-termp x)
             (pseudo-termp (cdr-term x))))

  (defthm cdr-term-correct
    (equal (sspec-geval-ev (cdr-term x) a)
           (cdr (sspec-geval-ev x a)))))



(defsection make-nth-terms
  (defund make-nth-terms (x start n)
    (declare (xargs :guard (and (natp start) (natp n))))
    (if (zp n)
        nil
      (cons `(nth ',(lnfix start) ,x)
            (make-nth-terms x (1+ (lnfix start)) (1- n)))))

  (local (in-theory (enable make-nth-terms)))

  (defthm pseudo-term-listp-make-nth-terms
    (implies (and (pseudo-termp x)
                  (natp start))
             (pseudo-term-listp (make-nth-terms x start n)))
    :hints(("Goal" :in-theory (enable make-nth-terms))))

  (defthm ev-of-make-nth-terms
    (equal (sspec-geval-ev-lst (make-nth-terms x start n) a)
           (take n (nthcdr start (sspec-geval-ev x a))))
    :hints(("Goal" :in-theory (enable acl2::take
                                      nthcdr))))

  (defthm len-of-make-nth-terms
    (equal (len (make-nth-terms x start n))
           (nfix n)))

  (defthm consp-of-make-nth-terms
    (equal (consp (make-nth-terms x start n))
           (posp n)))

  (defthm true-listp-of-make-nth-terms
    (true-listp (make-nth-terms x start n))
    :rule-classes :type-prescription))


(define ss-unary-function-fix ((x ss-unary-functionp))
  :returns (new-x ss-unary-functionp)
  (mbe :logic (if (ss-unary-functionp x)
                  x
                nil)
       :exec x)
  ///
  (std::defret ss-unary-function-fix-when-ss-unary-functionp
    (implies (ss-unary-functionp x)
             (equal new-x x))))

(defthm pseudo-termp-with-unary-function
  (implies (and (ss-unary-functionp f)
                (pseudo-termp arg))
           (pseudo-termp (list f arg)))
  :hints(("Goal" :in-theory (enable ss-unary-functionp))))

(defthm not-shape-spec-call-free-implies-ite-cons-or-call
  (implies (not (shape-spec-call-free x))
           (and (consp x)
                (or (equal (tag x) :g-ite)
                    (equal (tag x) :g-call)
                    (and (not (equal (tag x) :g-number))
                         (not (equal (tag x) :g-integer))
                         (not (equal (tag x) :g-boolean))
                         (not (equal (tag x) :g-var))
                         (not (equal (tag x) :g-concrete))
                         (not (equal (tag x) :g-ite))
                         (not (equal (tag x) :g-call))))))
  :hints(("Goal" :in-theory (enable shape-spec-call-free)))
  :rule-classes :forward-chaining)

(defines shape-spec-oblig-term
  (define shape-spec-oblig-term ((x shape-specp)
                                 (obj-term pseudo-termp))
    :guard-hints (("goal" :expand ((shape-specp x)
                                   (shape-spec-listp x))))
    :returns (oblig-term pseudo-termp :hyp :guard
                         :hints ('(:expand ((shape-specp x)))))
    (if (shape-spec-call-free x)
        `(shape-spec-obj-in-range ',x ,obj-term)
      (pattern-match x
        ((g-ite test then else)
         `(if (if ,(shape-spec-oblig-term-iff test ''t)
                  ,(shape-spec-oblig-term then obj-term)
                'nil)
              't
            (if ,(shape-spec-oblig-term-iff test ''nil)
                ,(shape-spec-oblig-term else obj-term)
              'nil)))
        ((g-call fn args inverse)
         (b* ((inverse (ss-unary-function-fix inverse))
              (arity (len args))
              (inverse-term `(,inverse ,obj-term))
              (nths (make-nth-terms inverse-term 0 arity)))
           `(if ,(shape-spec-list-oblig-term args nths)
                (equal (,fn . ,nths) ,obj-term)
              'nil)))
        (& `(if (consp ,obj-term)
                (if ,(shape-spec-oblig-term (car x) (car-term obj-term))
                    ,(shape-spec-oblig-term (cdr x) (cdr-term obj-term))
                  'nil)
              'nil)))))
  (define shape-spec-oblig-term-iff ((x shape-specp)
                                     (obj-term pseudo-termp))
    :returns (oblig-term pseudo-termp :hyp :guard
                         :hints ('(:expand ((shape-specp x)))))
    (if (shape-spec-call-free x)
        `(shape-spec-obj-in-range-iff ',x ,obj-term)
      (pattern-match x
        ((g-ite test then else)
         `(if (if ,(shape-spec-oblig-term-iff test ''t)
                  ,(shape-spec-oblig-term-iff then obj-term)
                'nil)
              't
            (if ,(shape-spec-oblig-term-iff test ''nil)
                ,(shape-spec-oblig-term-iff else obj-term)
              'nil)))
        ((g-call fn args inverse)
         (b* ((inverse (ss-unary-function-fix inverse))
              (arity (len args))
              (inverse-term `(,inverse (if ,obj-term 't 'nil)))
              (nths (make-nth-terms inverse-term 0 arity)))
           `(if ,(shape-spec-list-oblig-term args nths)
                (iff (,fn . ,nths) ,obj-term)
              'nil)))
        (& `(if ,obj-term 't 'nil)))))
  (define shape-spec-list-oblig-term ((x shape-spec-listp)
                                      (obj-terms pseudo-term-listp))
    :returns (oblig-term pseudo-termp :hyp :guard
                         :hints ('(:expand ((pseudo-term-listp obj-terms)
                                            (shape-spec-listp x)))))
    (if (atom x)
        (if (eq obj-terms nil)
            ''t
          ''nil)
      (if (consp obj-terms)
          `(if ,(shape-spec-oblig-term (car x) (car obj-terms))
               ,(shape-spec-list-oblig-term (cdr x) (cdr obj-terms))
             'nil)
        ''nil)))
  ///
  (local (defthm open-simple-term-vars
           (equal (simple-term-vars (cons fn args))
                  (and (not (eq fn 'quote))
                       (simple-term-vars-lst args)))
           :hints(("Goal" :in-theory (enable simple-term-vars)))))

  (local (defthm simple-term-vars-lst-of-consp
           (implies (consp x)
                    (equal (simple-term-vars-lst x)
                           (union-eq (simple-term-vars-lst (cdr x))
                                     (simple-term-vars (car x)))))
           :hints(("Goal" :in-theory (enable simple-term-vars-lst)))))

  (local (defthm simple-term-vars-lst-of-append
           (acl2::set-equiv (simple-term-vars-lst (append a b))
                            (append (simple-term-vars-lst a) (simple-term-vars-lst b)))
           :hints(("Goal" :in-theory (enable simple-term-vars-lst append)))))

  (local (defthm simple-term-vars-lst-of-make-nth-terms
           (implies (not (member v (simple-term-vars x)))
                    (not (member v (simple-term-vars-lst (make-nth-terms x start n)))))
           :hints(("Goal" :in-theory (enable make-nth-terms simple-term-vars)))))

  (local (defthm member-vars-of-car-term
           (implies (not (member v (simple-term-vars x)))
                    (not (member v (simple-term-vars (car-term x)))))
           :hints(("Goal" :in-theory (enable car-term)))))
  (local (defthm member-vars-of-cdr-term
           (implies (not (member v (simple-term-vars x)))
                    (not (member v (simple-term-vars (cdr-term x)))))
           :hints(("Goal" :in-theory (enable cdr-term)))))

  (local (defthm not-quote-of-ss-unary-function-fix
           (not (equal (ss-unary-function-fix x) 'quote))))

  (defthm-shape-spec-oblig-term-flag
    (defthm vars-of-shape-spec-oblig-term-bvars
      (implies (not (member v (simple-term-vars obj-term)))
               (not (member v (simple-term-vars (shape-spec-oblig-term x obj-term)))))
      :hints ('(:expand ((shape-spec-oblig-term x obj-term))))
      :flag shape-spec-oblig-term)
    (defthm vars-of-shape-spec-oblig-term-iff-bvars
      (implies (not (member v (simple-term-vars obj-term)))
               (not (member v (simple-term-vars (shape-spec-oblig-term-iff x obj-term)))))
      :hints ('(:expand ((shape-spec-oblig-term-iff x obj-term))
                :in-theory (enable car-term cdr-term)))
      :flag shape-spec-oblig-term-iff)
    (defthm vars-of-shape-spec-list-oblig-term-bvars
      (implies (not (member v (simple-term-vars-lst obj-terms)))
               (not (member v (simple-term-vars (shape-spec-list-oblig-term x obj-terms)))))
      :hints ('(:expand ((shape-spec-list-oblig-term x obj-terms)
                         (shape-spec-list-oblig-term x nil))))
      :flag shape-spec-list-oblig-term)))

(defines shape-spec-oblig-term-eval-ind
  (define shape-spec-oblig-term-ind (x obj-term a)
    :verify-guards nil
    :hints ((and stable-under-simplificationp
                 '(:expand ((shape-spec-call-free x)))))
    (if (shape-spec-call-free x)
        (list obj-term)
      (pattern-match x
        ((g-ite test then else)
         (list (shape-spec-oblig-term-iff-ind test ''t a)
               (shape-spec-oblig-term-ind then obj-term a)
               (shape-spec-oblig-term-iff-ind test ''nil a)
               (shape-spec-oblig-term-ind else obj-term a)))
        ((g-call & args inverse)
         (b* ((inverse (ss-unary-function-fix inverse))
              (arity (len args))
              (inverse-term `(,inverse ,obj-term))
              (nths (make-nth-terms inverse-term 0 arity))
              (nths1 (make-nth-terms `(,inverse ,(kwote (sspec-geval-ev obj-term a))) 0 arity)))
           (list (shape-spec-list-oblig-term-ind args nths a)
                 (shape-spec-list-oblig-term-ind args nths1 a))))
        (& (list (shape-spec-oblig-term-ind (car x) (car-term obj-term) a)
                 (shape-spec-oblig-term-ind (car x) (car-term (kwote (sspec-geval-ev obj-term a))) a)
                 (shape-spec-oblig-term-ind (cdr x) (cdr-term obj-term) a)
                 (shape-spec-oblig-term-ind (cdr x) (cdr-term (kwote (sspec-geval-ev obj-term a))) a))))))

  (define shape-spec-oblig-term-iff-ind (x obj-term a)
    :verify-guards nil
    (if (shape-spec-call-free x)
        (list obj-term)
      (pattern-match x
        ((g-ite test then else)
         (list (shape-spec-oblig-term-iff-ind test ''t a)
               (shape-spec-oblig-term-iff-ind then obj-term a)
               (shape-spec-oblig-term-iff-ind test ''nil a)
               (shape-spec-oblig-term-iff-ind else obj-term a)))
        ((g-call & args inverse)
         (b* ((inverse (ss-unary-function-fix inverse))
              (arity (len args))
              (inverse-term `(,inverse (if ,obj-term 't 'nil)))
              (nths (make-nth-terms inverse-term 0 arity))
              (nths1 (make-nth-terms `(,inverse (if ,(kwote (bool-fix (sspec-geval-ev obj-term a))) 't 'nil)) 0 arity)))
           (list (shape-spec-list-oblig-term-ind args nths a)
                 (shape-spec-list-oblig-term-ind args nths1 a))))
        (& (list obj-term)))))


  (define shape-spec-list-oblig-term-ind (x obj-terms a)
    (if (atom x)
        obj-terms
      (list (shape-spec-oblig-term-ind (car x) (car obj-terms) a)
            (shape-spec-list-oblig-term-ind (cdr x) (cdr obj-terms) a))))
  ///
  (local
   (defthm-shape-spec-oblig-term-eval-ind-flag
     (defthm shape-spec-oblig-term-eval-lemma
       (implies (shape-specp x)
                (equal (sspec-geval-ev (shape-spec-oblig-term x obj-term) a)
                       (sspec-geval-ev (shape-spec-oblig-term x (kwote (sspec-geval-ev obj-term a))) a)))
       :hints ('(:expand ((:free (obj-term iff-flg) (shape-spec-oblig-term x obj-term))
                          (shape-specp x))
                 :in-theory (enable sspec-geval-ev-of-fncall-args)
                 :do-not-induct t)
               ;; (and stable-under-simplificationp
               ;;      '(:expand ( )))
               (and stable-under-simplificationp
                    (member-equal '(not (equal (tag$inline x) ':g-call)) clause)
                    '(:cases ((equal (g-call->inverse x) 'quote))))
               )
       :rule-classes nil
       :flag shape-spec-oblig-term-ind)
     (defthm shape-spec-oblig-term-iff-eval-lemma
       (implies (shape-specp x)
                (equal (sspec-geval-ev (shape-spec-oblig-term-iff x obj-term) a)
                       (sspec-geval-ev (shape-spec-oblig-term-iff x (kwote (bool-fix (sspec-geval-ev obj-term a)))) a)))
       :hints ('(:expand ((:free (obj-term iff-flg) (shape-spec-oblig-term-iff x obj-term))
                          (shape-specp x))
                 :in-theory (enable sspec-geval-ev-of-fncall-args)
                 :do-not-induct t)
               ;; (and stable-under-simplificationp
               ;;      '(:expand ( )))
               (and stable-under-simplificationp
                    (member-equal '(not (equal (tag$inline x) ':g-call)) clause)
                    '(:cases ((equal (g-call->inverse x) 'quote))))
               )
       :rule-classes nil
       :flag shape-spec-oblig-term-iff-ind)
     (defthm shape-spec-list-oblig-term-eval-lemma
       (implies (and (shape-spec-listp x)
                     (true-listp obj-terms))
                (equal (sspec-geval-ev (shape-spec-list-oblig-term x obj-terms) a)
                       (sspec-geval-ev (shape-spec-list-oblig-term x (kwote-lst (sspec-geval-ev-lst obj-terms a))) a)))
       :hints ('(:expand ((:free (obj-terms) (shape-spec-list-oblig-term x obj-terms))
                          (:free (obj-terms) (shape-spec-list-oblig-term nil obj-terms))
                          (shape-spec-listp x))))
       :rule-classes nil
       :flag shape-spec-list-oblig-term-ind)))

  (defthmd shape-spec-oblig-term-eval
    (implies (and (equal new-obj-term (kwote (sspec-geval-ev obj-term a)))
                  (syntaxp (not (equal new-obj-term obj-term)))
                  (shape-specp x))
             (equal (sspec-geval-ev (shape-spec-oblig-term x obj-term) a)
                    (sspec-geval-ev (shape-spec-oblig-term x new-obj-term) a)))
    :hints (("goal" :use shape-spec-oblig-term-eval-lemma)))

  (defthmd shape-spec-oblig-term-iff-eval
    (implies (and (equal new-obj-term (kwote (bool-fix (sspec-geval-ev obj-term a))))
                  (syntaxp (not (equal new-obj-term obj-term)))
                  (shape-specp x))
             (equal (sspec-geval-ev (shape-spec-oblig-term-iff x obj-term) a)
                    (sspec-geval-ev (shape-spec-oblig-term-iff x new-obj-term) a)))
    :hints (("goal" :use shape-spec-oblig-term-iff-eval-lemma)))

  (defthmd shape-spec-list-oblig-term-eval
    (implies (and (equal new-obj-terms (kwote-lst (sspec-geval-ev-lst obj-terms a)))
                  (syntaxp (not (equal new-obj-terms obj-terms)))
                  (shape-spec-listp x)
                  (true-listp obj-terms))
             (equal (sspec-geval-ev (shape-spec-list-oblig-term x obj-terms) a)
                    (sspec-geval-ev (shape-spec-list-oblig-term x new-obj-terms) a)))
    :hints (("goal" :use shape-spec-list-oblig-term-eval-lemma))))



(defthm sspec-geval-ev-lst-of-kwote-lst
  (equal (sspec-geval-ev-lst (kwote-lst x) a)
         (list-fix x))
  :hints(("Goal" :in-theory (enable kwote-lst))))


(defsection sspec-geval-of-shape-spec-rules
  (local (in-theory (e/d (g-keyword-symbolp)
                         (bfr-list->s))))

  ;; (local (include-book "clause-processors/just-expand" :dir :system))

  (defthm sspec-geval-of-cons-shape-spec
    (implies (and (consp x)
                  (not (equal (tag x) :g-number))
                  (not (equal (tag x) :g-integer))
                  (not (equal (tag x) :g-boolean))
                  (not (equal (tag x) :g-var))
                  (not (equal (tag x) :g-concrete))
                  (not (equal (tag x) :g-ite))
                  (not (equal (tag x) :g-call)))
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    (cons (sspec-geval (shape-spec-to-gobj (car x)) env)
                          (sspec-geval (shape-spec-to-gobj (cdr x)) env))))
    :hints(("goal" :in-theory (enable shape-spec-to-gobj sspec-geval))))

  (defthm sspec-geval-of-g-ite-shape-spec
    (implies (equal (tag x) :g-ite)
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    (if (sspec-geval (shape-spec-to-gobj (g-ite->test x)) env)
                        (sspec-geval (shape-spec-to-gobj (g-ite->then x)) env)
                      (sspec-geval (shape-spec-to-gobj (g-ite->else x)) env))))
    :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj))))

  (defthm sspec-geval-of-g-concrete-shape-spec
    (implies (equal (tag x) :g-concrete)
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    (g-concrete->obj x)))
    :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj))))

  (defthm sspec-geval-of-g-call-shape-spec
    (implies (equal (tag x) :g-call)
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    (if (eq (g-call->fn x) 'quote)
                        nil
                      (sspec-geval-ev (cons (g-call->fn x)
                                            (kwote-lst (sspec-geval-list
                                                        (shape-spec-to-gobj-list (g-call->args x))
                                                        env)))
                                      nil))))
    :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj))))

  (defthm sspec-geval-of-g-var-shape-spec
    (implies (equal (tag x) :g-var)
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    (cdr (hons-assoc-equal (g-var->name x) (cdr env)))))
    :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj))))

  (defthm sspec-geval-of-g-boolean-shape-spec
    (implies (equal (tag x) :g-boolean)
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    (bfr-lookup (nfix (g-boolean->bool x)) (car env))))
    :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj))))

  (defthm sspec-geval-of-atom-shape-spec
    (implies (not (consp x))
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    x))
    :hints(("Goal" :in-theory (enable sspec-geval shape-spec-to-gobj))))

  (defthm sspec-geval-of-g-integer-shape-spec
    (implies (equal (tag x) :g-integer)
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    (bfr-list->s (numlist-to-vars (g-integer->bits x)) (car env))))
    :hints(("Goal" :in-theory (enable sspec-geval sspec-geval-list shape-spec-to-gobj))))

  (defthm sspec-geval-of-g-number-shape-spec
    (implies (equal (tag x) :g-number)
             (equal (sspec-geval (shape-spec-to-gobj x) env)
                    (bfr-list->s (numlist-to-vars (car (g-number->num x))) (car env))))
    :hints(("Goal" :in-theory (enable sspec-geval sspec-geval-list shape-spec-to-gobj))))

  (defthm sspec-geval-list-of-cons-shape-spec-list
    (implies (consp x)
             (equal (sspec-geval-list (shape-spec-to-gobj-list x) env)
                    (cons (sspec-geval (shape-spec-to-gobj (car x)) env)
                          (sspec-geval-list (shape-spec-to-gobj-list (cdr x)) env))))
    :hints(("Goal" :in-theory (enable sspec-geval-list shape-spec-to-gobj-list))))

  (defthm sspec-geval-list-of-cons-shape-spec-list
    (implies (consp x)
             (equal (sspec-geval-list (shape-spec-to-gobj-list x) env)
                    (cons (sspec-geval (shape-spec-to-gobj (car x)) env)
                          (sspec-geval-list (shape-spec-to-gobj-list (cdr x)) env))))
    :hints(("Goal" :in-theory (enable sspec-geval-list shape-spec-to-gobj-list))))

  (defthm sspec-geval-list-of-atom-shape-spec-list
    (implies (atom x)
             (equal (sspec-geval-list (shape-spec-to-gobj-list x) env)
                    nil))
    :hints(("Goal" :in-theory (enable sspec-geval-list shape-spec-to-gobj-list))))

  (def-ruleset! sspec-geval-of-shape-spec-rules
    '(sspec-geval-of-g-integer-shape-spec
      sspec-geval-of-g-number-shape-spec
      sspec-geval-of-g-boolean-shape-spec
      sspec-geval-of-g-var-shape-spec
      sspec-geval-of-g-ite-shape-spec
      sspec-geval-of-g-concrete-shape-spec
      sspec-geval-of-g-call-shape-spec
      sspec-geval-of-cons-shape-spec
      sspec-geval-of-atom-shape-spec
      sspec-geval-list-of-cons-shape-spec-list
      sspec-geval-list-of-atom-shape-spec-list)))


(defsection no-duplicatesp-of-shape-spec-indices/vars
  (defthm no-duplicatesp-of-g-ite-shape-spec-indices-implies
    (implies (and (equal (tag x) :g-ite)
                  (no-duplicatesp (shape-spec-indices x)))
             (and (no-duplicatesp (shape-spec-indices (g-ite->test x)))
                  (no-duplicatesp (shape-spec-indices (g-ite->then x)))
                  (no-duplicatesp (shape-spec-indices (g-ite->else x)))
                  (not (intersectp-equal (shape-spec-indices (g-ite->test x))
                                         (shape-spec-indices (g-ite->then x))))
                  (not (intersectp-equal (shape-spec-indices (g-ite->test x))
                                         (shape-spec-indices (g-ite->else x))))
                  (not (intersectp-equal (shape-spec-indices (g-ite->then x))
                                         (shape-spec-indices (g-ite->else x))))
                  (not (intersectp-equal (shape-spec-indices (g-ite->then x))
                                         (shape-spec-indices (g-ite->test x))))
                  (not (intersectp-equal (shape-spec-indices (g-ite->else x))
                                         (shape-spec-indices (g-ite->test x))))
                  (not (intersectp-equal (shape-spec-indices (g-ite->else x))
                                         (shape-spec-indices (g-ite->then x))))))
    :hints(("Goal" :expand ((shape-spec-indices x)))))

  (defthm no-duplicatesp-of-g-ite-shape-spec-vars-implies
    (implies (and (equal (tag x) :g-ite)
                  (no-duplicatesp (shape-spec-vars x)))
             (and (no-duplicatesp (shape-spec-vars (g-ite->test x)))
                  (no-duplicatesp (shape-spec-vars (g-ite->then x)))
                  (no-duplicatesp (shape-spec-vars (g-ite->else x)))
                  (not (intersectp-equal (shape-spec-vars (g-ite->test x))
                                         (shape-spec-vars (g-ite->then x))))
                  (not (intersectp-equal (shape-spec-vars (g-ite->test x))
                                         (shape-spec-vars (g-ite->else x))))
                  (not (intersectp-equal (shape-spec-vars (g-ite->then x))
                                         (shape-spec-vars (g-ite->else x))))
                  (not (intersectp-equal (shape-spec-vars (g-ite->then x))
                                         (shape-spec-vars (g-ite->test x))))
                  (not (intersectp-equal (shape-spec-vars (g-ite->else x))
                                         (shape-spec-vars (g-ite->test x))))
                  (not (intersectp-equal (shape-spec-vars (g-ite->else x))
                                         (shape-spec-vars (g-ite->then x))))))
    :hints(("Goal" :expand ((shape-spec-vars x)))))

  (defthm no-duplicatesp-of-g-call-shape-spec-indices-implies
    (implies (and (equal (tag x) :g-call)
                  (no-duplicatesp (shape-spec-indices x)))
             (no-duplicatesp (shape-spec-list-indices (g-call->args x))))
    :hints(("Goal" :expand ((shape-spec-indices x)))))

  (defthm no-duplicatesp-of-g-call-shape-spec-vars-implies
    (implies (and (equal (tag x) :g-call)
                  (no-duplicatesp (shape-spec-vars x)))
             (no-duplicatesp (shape-spec-list-vars (g-call->args x))))
    :hints(("Goal" :expand ((shape-spec-vars x)))))

  (defthm no-duplicatesp-of-g-number-shape-spec-indices-implies
    (implies (and (equal (tag x) :g-number)
                  (no-duplicatesp (shape-spec-indices x)))
             (no-duplicatesp (car (g-number->num x))))
    :hints(("Goal" :expand ((shape-spec-indices x)))))

  (defthm no-duplicatesp-of-cons-non-call-free-shape-spec-indices-implies
    (implies (and (not (equal (tag x) :g-ite))
                  (not (equal (tag x) :g-call))
                  (not (equal (tag x) :g-apply))
                  (not (shape-spec-call-free x))
                  (no-duplicatesp (shape-spec-indices x)))
             (and (no-duplicatesp (shape-spec-indices (car x)))
                  (no-duplicatesp (shape-spec-indices (cdr x)))
                  (not (intersectp-equal (shape-spec-indices (car x))
                                         (shape-spec-indices (cdr x))))
                  (not (intersectp-equal (shape-spec-indices (cdr x))
                                         (shape-spec-indices (car x))))))
    :hints (("goal" :expand ((shape-spec-indices x)))))

  (defthm no-duplicatesp-of-cons-shape-spec-indices-implies
    (implies (and (consp x)
                  (not (equal (tag x) :g-ite))
                  (not (equal (tag x) :g-call))
                  (not (equal (tag x) :g-apply))
                  (not (equal (tag x) :g-number))
                  (not (equal (tag x) :g-integer))
                  (not (equal (tag x) :g-boolean))
                  (not (equal (tag x) :g-concrete))
                  (not (equal (tag x) :g-var))
                  (no-duplicatesp (shape-spec-indices x)))
             (and (no-duplicatesp (shape-spec-indices (car x)))
                  (no-duplicatesp (shape-spec-indices (cdr x)))
                  (not (intersectp-equal (shape-spec-indices (car x))
                                         (shape-spec-indices (cdr x))))
                  (not (intersectp-equal (shape-spec-indices (cdr x))
                                         (shape-spec-indices (car x))))))
    :hints (("goal" :expand ((shape-spec-indices x)))))

  (defthm no-duplicatesp-of-cons-non-call-free-shape-spec-vars-implies
    (implies (and (not (equal (tag x) :g-ite))
                  (not (equal (tag x) :g-call))
                  (not (equal (tag x) :g-apply))
                  (not (shape-spec-call-free x))
                  (no-duplicatesp (shape-spec-vars x)))
             (and (no-duplicatesp (shape-spec-vars (car x)))
                  (no-duplicatesp (shape-spec-vars (cdr x)))
                  (not (intersectp-equal (shape-spec-vars (car x))
                                         (shape-spec-vars (cdr x))))
                  (not (intersectp-equal (shape-spec-vars (cdr x))
                                         (shape-spec-vars (car x))))))
    :hints (("goal" :expand ((shape-spec-vars x)))))

  (defthm no-duplicatesp-of-cons-shape-spec-vars-implies
    (implies (and (consp x)
                  (not (equal (tag x) :g-ite))
                  (not (equal (tag x) :g-call))
                  (not (equal (tag x) :g-apply))
                  (not (equal (tag x) :g-number))
                  (not (equal (tag x) :g-integer))
                  (not (equal (tag x) :g-boolean))
                  (not (equal (tag x) :g-concrete))
                  (not (equal (tag x) :g-var))
                  (no-duplicatesp (shape-spec-vars x)))
             (and (no-duplicatesp (shape-spec-vars (car x)))
                  (no-duplicatesp (shape-spec-vars (cdr x)))
                  (not (intersectp-equal (shape-spec-vars (car x))
                                         (shape-spec-vars (cdr x))))
                  (not (intersectp-equal (shape-spec-vars (cdr x))
                                         (shape-spec-vars (car x))))))
    :hints (("goal" :expand ((shape-spec-vars x)))))


  (defthm no-duplicatesp-of-cons-shape-spec-list-indices-implies
    (implies (and (consp x)
                  (no-duplicatesp (shape-spec-list-indices x)))
             (and (no-duplicatesp (shape-spec-indices (car x)))
                  (no-duplicatesp (shape-spec-list-indices (cdr x)))
                  (not (intersectp-equal (shape-spec-indices (car x))
                                         (shape-spec-list-indices (cdr x))))
                  (not (intersectp-equal (shape-spec-list-indices (cdr x))
                                         (shape-spec-indices (car x))))))
    :hints (("goal" :expand ((shape-spec-list-indices x)))))

  (defthm no-duplicatesp-of-cons-shape-spec-list-vars-implies
    (implies (and (consp x)
                  (no-duplicatesp (shape-spec-list-vars x)))
             (and (no-duplicatesp (shape-spec-vars (car x)))
                  (no-duplicatesp (shape-spec-list-vars (cdr x)))
                  (not (intersectp-equal (shape-spec-vars (car x))
                                         (shape-spec-list-vars (cdr x))))
                  (not (intersectp-equal (shape-spec-list-vars (cdr x))
                                         (shape-spec-vars (car x))))))
    :hints (("goal" :expand ((shape-spec-list-vars x)))))

  (defthm no-duplicatesp-of-g-integer-shape-spec-indices-implies
    (implies (and (equal (tag x) :g-integer)
                  (no-duplicatesp (shape-spec-indices x)))
             (no-duplicatesp (g-integer->bits x)))
    :hints (("goal" :expand ((shape-spec-indices x))))))


(defines shape-spec-env-term
  (define shape-spec-env-term ((x shape-specp)
                               (obj-term pseudo-termp))
    :guard-hints (("goal" :expand ((shape-specp x)
                                   (shape-spec-listp x)
                                   (:free (a b) (pseudo-termp
                                                 (cons a b))))
                   :in-theory (disable pseudo-termp)))
    :returns (env-term pseudo-termp :hyp :guard
                       :hints ('(:expand ((shape-specp x)))))
    :flag ss
    (if (shape-spec-call-free x)
        `(shape-spec-slice-to-env
          (shape-spec-env-slice ',x ,obj-term))
      (pattern-match x
        ((g-ite test then else)
         (b* ((then-term (shape-spec-env-term then obj-term))
              (else-term (shape-spec-env-term else obj-term))
              (both `(ss-append-envs ,then-term ,else-term))
              (test-env (shape-spec-env-term-iff test (shape-spec-oblig-term then obj-term))))
           `(ss-append-envs ,test-env ,both)))
        ((g-call & args inverse)
         (b* ((inverse (ss-unary-function-fix inverse))
              (inverse-term `(,inverse ,obj-term))
              (nths (make-nth-terms inverse-term 0 (len args))))
           (shape-spec-list-env-term args nths)))
        (& `(ss-append-envs
             ,(shape-spec-env-term (car x) (car-term obj-term))
             ,(shape-spec-env-term (cdr x) (cdr-term obj-term)))))))
  (define shape-spec-env-term-iff ((x shape-specp)
                                   (obj-term pseudo-termp))
    :returns (env-term pseudo-termp :hyp :guard
                       :hints ('(:expand ((shape-specp x)))))
    :flag iff
    (if (shape-spec-call-free x)
        `(shape-spec-slice-to-env
          (shape-spec-iff-env-slice ',x ,obj-term))
      (pattern-match x
        ((g-ite test then else)
         (b* ((then-term (shape-spec-env-term-iff then obj-term))
              (else-term (shape-spec-env-term-iff else obj-term))
              (both `(ss-append-envs ,then-term ,else-term))
              (test-env (shape-spec-env-term-iff test (shape-spec-oblig-term-iff then obj-term))))
           `(ss-append-envs ,test-env ,both)))
        ((g-call & args inverse)
         (b* ((inverse (ss-unary-function-fix inverse))
              (inverse-term `(,inverse (if ,obj-term 't 'nil)))
              (nths (make-nth-terms inverse-term 0 (len args))))
           (shape-spec-list-env-term args nths)))
        (& `(shape-spec-slice-to-env
             (shape-spec-iff-env-slice ',x ,obj-term))))))
  (define shape-spec-list-env-term ((x shape-spec-listp)
                                    (obj-terms pseudo-term-listp))
    :returns (env-term pseudo-termp :hyp :guard
                       :hints ('(:expand ((shape-spec-listp x)
                                          (pseudo-term-listp obj-terms)))))
    :flag list
    (if (atom x)
        ''(nil)
      `(ss-append-envs
        ,(shape-spec-env-term (car x) (car obj-terms))
        ,(shape-spec-list-env-term (cdr x) (cdr obj-terms)))))
  ///

  (defthm-shape-spec-env-term-flag
    (defthm indices-of-shape-spec-env-term
      (implies (shape-specp x)
               (equal (alist-keys
                       (car (sspec-geval-ev (shape-spec-env-term x obj-term) a)))
                      (shape-spec-indices x)))
      :hints ('(:expand ((shape-spec-env-term x obj-term)
                         (shape-spec-indices x))))
      :flag ss)
    (defthm indices-of-shape-spec-env-term-iff
      (implies (shape-specp x)
               (equal (alist-keys
                       (car (sspec-geval-ev (shape-spec-env-term-iff x obj-term) a)))
                      (shape-spec-indices x)))
      :hints ('(:expand ((shape-spec-env-term-iff x obj-term)
                         (shape-spec-indices x))))
      :flag iff)
    (defthm indices-of-shape-spec-list-env-term
      (implies (shape-spec-listp x)
               (equal (alist-keys
                       (car (sspec-geval-ev (shape-spec-list-env-term x obj-terms) a)))
                      (shape-spec-list-indices x)))
      :hints ('(:expand ((shape-spec-list-env-term x obj-terms)
                         (shape-spec-list-env-term nil obj-terms)
                         (shape-spec-list-indices x))))
      :flag list))

  (defthm-shape-spec-env-term-flag
    (defthm vars-of-shape-spec-env-term
      (implies (shape-specp x)
               (equal (alist-keys
                       (cdr (sspec-geval-ev (shape-spec-env-term x obj-term) a)))
                      (shape-spec-vars x)))
      :hints ('(:expand ((shape-spec-env-term x obj-term)
                         (shape-spec-vars x))))
      :flag ss)
    (defthm vars-of-shape-spec-env-term-iff
      (implies (shape-specp x)
               (equal (alist-keys
                       (cdr (sspec-geval-ev (shape-spec-env-term-iff x obj-term) a)))
                      (shape-spec-vars x)))
      :hints ('(:expand ((shape-spec-env-term-iff x obj-term)
                         (shape-spec-vars x))))
      :flag iff)
    (defthm vars-of-shape-spec-list-env-term
      (implies (shape-spec-listp x)
               (equal (alist-keys
                       (cdr (sspec-geval-ev (shape-spec-list-env-term x obj-terms) a)))
                      (shape-spec-list-vars x)))
      :hints ('(:expand ((shape-spec-list-env-term x obj-terms)
                         (shape-spec-list-env-term nil obj-terms)
                         (shape-spec-list-vars x))))
      :flag list))


  (defthm-shape-spec-env-term-flag
    (defthm alistp-car-shape-spec-env-term
      (alistp (car (sspec-geval-ev (shape-spec-env-term x obj-term)
                                   a)))
      :hints ('(:expand ((shape-spec-env-term x obj-term))))
      :flag ss)
    (defthm alistp-car-shape-spec-env-term-iff
      (alistp (car (sspec-geval-ev (shape-spec-env-term-iff x obj-term)
                                   a)))
      :hints ('(:expand ((shape-spec-env-term-iff x obj-term))))
      :flag iff)
    (defthm alistp-car-shape-spec-list-env-term
      (alistp (car (sspec-geval-ev (shape-spec-list-env-term x obj-terms)
                                   a)))
      :hints ('(:expand ((shape-spec-list-env-term x obj-terms))))
      :flag list))

  (defthm-shape-spec-env-term-flag
    (defthm alistp-cdr-shape-spec-env-term
      (alistp (cdr (sspec-geval-ev (shape-spec-env-term x obj-term)
                                   a)))
      :hints ('(:expand ((shape-spec-env-term x obj-term))))
      :flag ss)
    (defthm alistp-cdr-shape-spec-env-term-iff
      (alistp (cdr (sspec-geval-ev (shape-spec-env-term-iff x obj-term)
                                   a)))
      :hints ('(:expand ((shape-spec-env-term-iff x obj-term))))
      :flag iff)
    (defthm alistp-cdr-shape-spec-list-env-term
      (alistp (cdr (sspec-geval-ev (shape-spec-list-env-term x obj-terms)
                                   a)))
      :hints ('(:expand ((shape-spec-list-env-term x obj-terms))))
      :flag list))

  (local (defthm g-keyword-symbolp-of-shape-spec-to-gobj
           (equal (g-keyword-symbolp (shape-spec-to-gobj x))
                  (g-keyword-symbolp x))
           :hints(("Goal" :expand ((shape-spec-to-gobj x))))))

  ;; (local (defthm equal-keyword-shape-spec-to-gobj
  ;;          (implies (and (syntaxp (quotep key))
  ;;                        (g-keyword-symbolp key))
  ;;                   (equal (equal (shape-spec-to-gobj x) key)
  ;;                          (equal x key)))
  ;;          :hints(("Goal" :in-theory (enable shape-spec-to-gobj)))))

  ;; (defthm sspec-geval-of-gl-cons
  ;;   (equal (sspec-geval (gl-cons a b) env)
  ;;          (cons (sspec-geval a env)
  ;;                (sspec-geval b env)))
  ;;   :hints(("Goal" :in-theory (enable sspec-geval g-keyword-symbolp))))

  ;; (defthm sspec-geval-of-g-apply
  ;;   (implies (not (eq fn 'quote))
  ;;            (equal (sspec-geval (g-apply fn args) env)
  ;;                   (sspec-geval-ev (cons fn (kwote-lst (sspec-geval-list args env))) nil)))
  ;;   :hints(("Goal" :in-theory (enable sspec-geval g-keyword-symbolp))))


  ;; ;; (local (defthm non-keyword-symbol-by-shape-spec-call-free
  ;; ;;          (implies (and (not (shape-spec-call-free x))
  ;; ;;                        (not (eq (tag x) :g-ite))
  ;; ;;                        (not (eq (tag x) :g-apply)))
  ;; ;;                   (not (g-keyword-symbolp (tag x))))
  ;; ;;          :hints(("Goal" :in-theory (enable g-keyword-symbolp)))))


  ;; (local (in-theory (disable shape-spec-call-free)))

  ;; (local (in-theory (disable iff kwote-lst)))

  ;; (local
  ;;  (progn

  ;;    (defthm shape-spec-to-gobj-of-cons
  ;;      (implies (and (not (shape-spec-call-free x))
  ;;                    (not (member (tag x) '(:g-ite :g-call))))
  ;;               (equal (shape-spec-to-gobj x)
  ;;                      (gl-cons (shape-spec-to-gobj (car x))
  ;;                               (shape-spec-to-gobj (cdr x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-to-gobj))))

  ;;    (defthm shape-spec-indices-of-cons
  ;;      (implies (and (not (shape-spec-call-free x))
  ;;                    (not (member (tag x) '(:g-ite :g-call))))
  ;;               (equal (shape-spec-indices x)
  ;;                      (append (shape-spec-indices (car x))
  ;;                              (shape-spec-indices (cdr x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-indices))))

  ;;    (defthm shape-spec-vars-of-cons
  ;;      (implies (and (not (shape-spec-call-free x))
  ;;                    (not (member (tag x) '(:g-ite :g-call))))
  ;;               (equal (shape-spec-vars x)
  ;;                      (append (shape-spec-vars (car x))
  ;;                              (shape-spec-vars (cdr x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-vars))))

  ;;    (defthm shape-specp-car/cdr
  ;;      (implies (and (not (shape-spec-call-free x))
  ;;                    (not (member (tag x) '(:g-ite :g-call)))
  ;;                    (shape-specp x))
  ;;               (and (shape-specp (car x))
  ;;                    (shape-specp (cdr x))))
  ;;      :hints(("Goal" :in-theory (enable shape-specp))))

  ;;    (defthm shape-spec-to-gobj-of-g-call
  ;;      (implies (equal (tag x) :g-call)
  ;;               (equal (shape-spec-to-gobj x)
  ;;                      (g-apply (g-call->fn x)
  ;;                               (shape-spec-to-gobj-list (g-call->args x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-to-gobj))))

  ;;    (defthm shape-spec-indices-of-g-call
  ;;      (implies (equal (tag x) :g-call)
  ;;               (equal (shape-spec-indices x)
  ;;                      (shape-spec-list-indices (g-call->args x))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-indices))))

  ;;    (defthm shape-spec-vars-of-g-call
  ;;      (implies (equal (tag x) :g-call)
  ;;               (equal (shape-spec-vars x)
  ;;                      (shape-spec-list-vars (g-call->args x))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-vars))))

  ;;    (defthm shape-specp-g-call
  ;;      (implies (and (equal (tag x) :g-call)
  ;;                    (shape-specp x))
  ;;               (and (shape-spec-listp (g-call->args x))
  ;;                    (symbolp (g-call->fn x))
  ;;                    (not (equal (g-call->fn x) 'quote))
  ;;                    (ss-unary-functionp (g-call->inverse x))))
  ;;      :hints(("Goal" :in-theory (enable shape-specp))))

  ;;    (defthm shape-spec-to-gobj-of-g-ite
  ;;      (implies (equal (tag x) :g-ite)
  ;;               (equal (shape-spec-to-gobj x)
  ;;                      (g-ite (shape-spec-to-gobj (g-ite->test x))
  ;;                             (shape-spec-to-gobj (g-ite->then x))
  ;;                             (shape-spec-to-gobj (g-ite->else x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-to-gobj))))

  ;;    (defthm shape-spec-indices-of-g-ite
  ;;      (implies (equal (tag x) :g-ite)
  ;;               (equal (shape-spec-indices x)
  ;;                      (append (shape-spec-indices (g-ite->test x))
  ;;                              (shape-spec-indices (g-ite->then x))
  ;;                              (shape-spec-indices (g-ite->else x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-indices))))

  ;;    (defthm shape-spec-vars-of-g-ite
  ;;      (implies (equal (tag x) :g-ite)
  ;;               (equal (shape-spec-vars x)
  ;;                      (append (shape-spec-vars (g-ite->test x))
  ;;                              (shape-spec-vars (g-ite->then x))
  ;;                              (shape-spec-vars (g-ite->else x)))))
  ;;      :hints(("Goal" :in-theory (enable shape-spec-vars))))

  ;;    (defthm shape-specp-g-ite
  ;;      (implies (and (equal (tag x) :g-ite)
  ;;                    (shape-specp x))
  ;;               (and (shape-specp (g-ite->test x))
  ;;                    (shape-specp (g-ite->then x))
  ;;                    (shape-specp (g-ite->else x))))
  ;;      :hints(("Goal" :in-theory (enable shape-specp))))))

  ;; (local (in-theory (disable not)))

  ;; (local (in-theory (disable (:t shape-spec-oblig-term)
  ;;                            (:t shape-spec-env-term)
  ;;                            shape-spec-call-free-by-tag
  ;;                            ;acl2::consp-by-len
  ;;                            acl2::true-listp-append
  ;;                            ;acl2::no-duplicatesp-equal-when-atom
  ;;                            acl2::no-duplicatesp-equal-non-cons
  ;;                            acl2::consp-of-append
  ;;                            default-car
  ;;                            tag-when-atom
  ;;                            default-cdr)))

  (local (in-theory (disable true-listp acl2::list-fix-when-true-listp)))

  (defthm-shape-spec-env-term-flag
    (defthm shape-spec-oblig-term-correct
      (let ((env (sspec-geval-ev (shape-spec-env-term x obj-term) a)))
        (implies (and (sspec-geval-ev (shape-spec-oblig-term x obj-term) a)
                      (shape-specp x)
                      (no-duplicatesp (shape-spec-indices x))
                      (no-duplicatesp (shape-spec-vars x)))
                 (equal (sspec-geval (shape-spec-to-gobj x)
                                     (cons (slice-to-bdd-env (car env) ee)
                                           (cdr env)))
                        (sspec-geval-ev obj-term a))))
      :hints ('(:expand ((shape-spec-env-term x obj-term)
                         (shape-spec-oblig-term x obj-term))
                :in-theory (enable sspec-geval-ev-of-fncall-args
                                   shape-spec-oblig-term-eval
                                   shape-spec-oblig-term-iff-eval)))
      :flag ss)
    (defthm shape-spec-oblig-term-iff-correct
      (let ((env (sspec-geval-ev (shape-spec-env-term-iff x obj-term) a)))
        (implies (and (sspec-geval-ev (shape-spec-oblig-term-iff x obj-term) a)
                      (shape-specp x)
                      (no-duplicatesp (shape-spec-indices x))
                      (no-duplicatesp (shape-spec-vars x)))
                 (iff (sspec-geval (shape-spec-to-gobj x)
                                   (cons (slice-to-bdd-env (car env) ee)
                                         (cdr env)))
                      (sspec-geval-ev obj-term a))))
      :hints ('(:expand ((shape-spec-env-term-iff x obj-term)
                         (shape-spec-oblig-term-iff x obj-term))
                :in-theory (enable sspec-geval-ev-of-fncall-args
                                   shape-spec-oblig-term-eval
                                   shape-spec-oblig-term-iff-eval)))
      :flag iff)
    (defthm shape-spec-list-oblig-term-correct
      (let ((env (sspec-geval-ev (shape-spec-list-env-term
                                  x obj-terms)
                                 a)))
        (implies (and (sspec-geval-ev (shape-spec-list-oblig-term x obj-terms) a)
                      (shape-spec-listp x)
                      (no-duplicatesp (shape-spec-list-indices x))
                      (no-duplicatesp (shape-spec-list-vars x)))
                 (equal (sspec-geval-list (shape-spec-to-gobj-list x)
                                          (cons (slice-to-bdd-env (car env) ee)
                                                (cdr env)))
                        (sspec-geval-ev-lst obj-terms a))))
      :hints ('(:expand ((shape-spec-list-env-term x obj-terms)
                         (shape-spec-list-oblig-term x obj-terms)
                         (:free (env) (sspec-geval-list nil env)))
                :do-not-induct t))
      :flag list))


  )
