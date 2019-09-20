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
(include-book "glcp-unify-defs")
(include-book "glcp-geval-thms")
(include-book "var-bounds")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "clause-processors/find-matching" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))


(defsection glcp-generic-geval-alist

  (local (in-theory (enable glcp-generic-geval-alist)))

  (defthm glcp-generic-geval-alist-pairlis$
    (equal (glcp-generic-geval-alist
            (pairlis$ formals actuals)
            env)
           (pairlis$ formals
                     (glcp-generic-geval-list actuals env)))
    :hints(("Goal" :in-theory (enable default-cdr pairlis$ gobj-listp
                                      glcp-generic-geval-list)
            :expand ((glcp-generic-geval nil env))
            :induct (pairlis$ formals actuals))))

  (defthm glcp-generic-geval-alist-lookup
    (equal (hons-assoc-equal k (glcp-generic-geval-alist al env))
           (and (hons-assoc-equal k al)
                (cons k (glcp-generic-geval (cdr (hons-assoc-equal k al))
                                            env)))))

  (defthm glcp-generic-geval-alist-of-acons
    (equal (glcp-generic-geval-alist (cons (cons k v) al) env)
           (cons (cons k (glcp-generic-geval v env))
                 (glcp-generic-geval-alist al env)))))


(defsection all-keys-bound
  (defund all-keys-bound (keys alist)
    (declare (xargs :guard t))
    (if (atom keys)
        t
      (and (hons-assoc-equal (car keys) alist)
           (all-keys-bound (cdr keys) alist))))

  (local (in-theory (enable all-keys-bound)))

  (defthmd all-keys-bound-member-implies
    (implies (and (member k keys)
                  (not (hons-assoc-equal k alist)))
             (not (all-keys-bound keys alist))))

  (defthmd all-keys-bound-subset
    (implies (and (subsetp keys1 keys)
                  (all-keys-bound keys alist))
             (all-keys-bound keys1 alist))
    :hints(("Goal" :in-theory (enable all-keys-bound-member-implies
                                      subsetp))))

  (defcong acl2::set-equiv equal (all-keys-bound keys alist) 1
    :hints(("Goal" :in-theory (enable acl2::set-equiv)
            :use ((:instance all-keys-bound-subset
                   (keys1 keys) (keys keys-equiv))
                  (:instance all-keys-bound-subset
                   (keys1 keys-equiv) (keys keys)))
            :do-not-induct t)))

  (defthm all-keys-bound-append
    (equal (all-keys-bound (append a b) alist)
           (and (all-keys-bound a alist)
                (all-keys-bound b alist))))


  (acl2::defthm-simple-term-vars-flag
    (defthm glcp-generic-geval-ev-of-acons-when-all-vars-bound
      (implies (and (all-keys-bound (acl2::simple-term-vars x) a)
                    (not (hons-assoc-equal k a))
                    (pseudo-termp x))
               (equal (glcp-generic-geval-ev x (cons (cons k v) a))
                      (glcp-generic-geval-ev x a)))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable glcp-generic-geval-ev-of-fncall-args
                                        acl2::simple-term-vars))))
      :flag acl2::simple-term-vars)
    (defthm glcp-generic-geval-ev-lst-of-acons-when-all-vars-bound
      (implies (and (all-keys-bound (acl2::simple-term-vars-lst x) a)
                    (not (hons-assoc-equal k a))
                    (pseudo-term-listp x))
               (equal (glcp-generic-geval-ev-lst x (cons (cons k v) a))
                      (glcp-generic-geval-ev-lst x a)))
      :hints ('(:expand (acl2::simple-term-vars-lst x)))
      :flag acl2::simple-term-vars-lst))

  (defthm all-keys-bound-of-glcp-generic-geval-alist
    (equal (all-keys-bound keys (glcp-generic-geval-alist alist env))
           (all-keys-bound keys alist))))

(defsection glcp-unify-concrete
  (local (defthm assoc-when-nonnil-key
           (implies key
                    (equal (assoc key alist)
                           (hons-assoc-equal key alist)))
           :rule-classes ((:rewrite :backchain-limit-lst 1))))

  (local (in-theory (enable glcp-unify-concrete)))

  (defthm glcp-unify-concrete-preserves-assoc
    (b* (((mv ok alist1) (glcp-unify-concrete pat x alist)))
      (implies (and ok (hons-assoc-equal k alist))
               (equal (hons-assoc-equal k alist1)
                      (hons-assoc-equal k alist)))))

  (defthm alistp-glcp-unify-concrete
    (b* (((mv ok alist1) (glcp-unify-concrete pat x alist)))
      (equal (alistp alist1)
             (or (not ok) (alistp alist)))))


  (defthm glcp-unify-concrete-preserves-all-keys-bound
    (b* (((mv ok alist1) (glcp-unify-concrete pat x alist)))
      (implies (and ok (all-keys-bound keys alist))
               (all-keys-bound keys alist1)))
    :hints (("goal" :induct (all-keys-bound keys alist)
             :in-theory (enable all-keys-bound))))

  (local (defthm equal-len
           (implies (syntaxp (quotep y))
                    (Equal (equal (len x) y)
                           (if (zp y)
                               (and (equal y 0) (atom x))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- y))))))))

  (defthm all-keys-bound-of-glcp-unify-concrete
    (b* (((mv ok newalist) (glcp-unify-concrete pat x alist)))
      (implies ok
               (all-keys-bound (acl2::simple-term-vars pat) newalist)))
    :hints (("goal" :induct (glcp-unify-concrete pat x alist)
             :in-theory (enable all-keys-bound
                                acl2::simple-term-vars
                                acl2::simple-term-vars-lst))))



  (defthm glcp-unify-concrete-preserves-eval
    (b* (((mv ok newalist) (glcp-unify-concrete pat x alist)))
      (implies (and ok
                    (pseudo-termp term)
                    (all-keys-bound (acl2::simple-term-vars term) alist))
               (equal (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                   newalist env))
                      (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                   alist env))))))

  (defthmd glcp-unify-concrete-correct
    (b* (((mv ok alist)
          (glcp-unify-concrete pat x alist)))
      (implies (and ok
                    (pseudo-termp pat))
               (equal (glcp-generic-geval-ev pat
                                             (glcp-generic-geval-alist alist
                                                                       env))
                      x)))
    :hints(("Goal" :in-theory (disable general-concretep))))

  (defthm gobj-depends-on-of-glcp-unify-concrete
    (implies (not (gobj-alist-depends-on k p alist))
             (not (gobj-alist-depends-on
                   k p (mv-nth 1 (glcp-unify-concrete pat x alist)))))
    :hints(("Goal" :in-theory (enable g-concrete-quote))))

  (local (defthm hons-assoc-equal-to-member-alist-keys
           (iff (hons-assoc-equal k a)
                (member k (acl2::alist-keys a)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal
                                             acl2::alist-keys)))))

  (local (defthm associativity-of-union-equal
           (equal (union-equal (union-equal a b) c)
                  (union-equal a (union-equal b c)))))

  ;; (defthm alist-keys-of-glcp-unify-concrete
  ;;   (b* (((mv ok alist1) (glcp-unify-concrete pat x alist)))
  ;;     (implies ok
  ;;              (equal (acl2::alist-keys alist1)
  ;;                     (union-equal (acl2::simple-term-vars pat)
  ;;                                  (acl2::alist-keys alist)))))
  ;;   :hints(("Goal" :in-theory (enable acl2::alist-keys))))
  )

(defsection glcp-unify-term/gobj
  (local (in-theory (enable pseudo-termp)))
  (local (defthm assoc-when-nonnil-key
           (implies key
                    (equal (assoc key alist)
                           (hons-assoc-equal key alist)))
           :rule-classes ((:rewrite :backchain-limit-lst 1))))


  (local (in-theory (enable glcp-unify-term/gobj
                            glcp-unify-term/gobj-list)))

  (flag::make-flag glcp-unify-term/gobj-flg glcp-unify-term/gobj
                   :flag-mapping ((glcp-unify-term/gobj . term)
                                  (glcp-unify-term/gobj-list . list)))

  (local (in-theory (disable glcp-unify-term/gobj
                             glcp-unify-term/gobj-list)))


  (defthm-glcp-unify-term/gobj-flg
    (defthm glcp-unify-term/gobj-preserves-assoc
      (b* (((mv ok alist1) (glcp-unify-term/gobj pat x alist)))
        (implies (and ok (hons-assoc-equal k alist))
                 (equal (hons-assoc-equal k alist1)
                        (hons-assoc-equal k alist))))
      :hints ('(:in-theory (enable all-keys-bound)
                :expand ((:free (x) (glcp-unify-term/gobj pat x alist))
                         (:free (x) (glcp-unify-term/gobj nil x alist)))))
      :flag term)
    (defthm glcp-unify-term/gobj-list-preserves-assoc
      (b* (((mv ok alist1) (glcp-unify-term/gobj-list pat x alist)))
        (implies (and ok (hons-assoc-equal k alist))
                 (equal (hons-assoc-equal k alist1)
                        (hons-assoc-equal k alist))))
      :hints ('(:in-theory (enable all-keys-bound)
                :expand ((:free (x) (glcp-unify-term/gobj-list pat x alist)))))
      :flag list))

  (defthm-glcp-unify-term/gobj-flg
    (defthm glcp-unify-term/gobj-preserves-alistp
      (b* (((mv ok alist1) (glcp-unify-term/gobj pat x alist)))
        (equal (alistp alist1)
               (or (not ok) (alistp alist))))
      :hints ('(:in-theory (enable all-keys-bound)
                :expand ((:free (x) (glcp-unify-term/gobj pat x alist))
                         (:free (x) (glcp-unify-term/gobj nil x alist)))))
      :flag term)
    (defthm glcp-unify-term/gobj-list-preserves-alistp
      (b* (((mv ok alist1) (glcp-unify-term/gobj-list pat x alist)))
        (equal (alistp alist1)
               (or (not ok) (alistp alist))))
      :hints ('(:in-theory (enable all-keys-bound)
                :expand ((:free (x) (glcp-unify-term/gobj-list pat x alist)))))
      :flag list))

  (defthm glcp-unify-term/gobj-preserves-all-keys-bound
    (b* (((mv ok alist1) (glcp-unify-term/gobj pat x alist)))
      (implies (and ok (all-keys-bound keys alist))
               (all-keys-bound keys alist1)))
    :hints (("goal" :induct (all-keys-bound keys alist)
             :in-theory (enable all-keys-bound))))

  (defthm glcp-unify-term/gobj-list-preserves-all-keys-bound
    (b* (((mv ok alist1) (glcp-unify-term/gobj-list pat x alist)))
      (implies (and ok (all-keys-bound keys alist))
               (all-keys-bound keys alist1)))
    :hints (("goal" :induct (all-keys-bound keys alist)
             :in-theory (enable all-keys-bound))))

  (local (defthm equal-len
           (implies (syntaxp (quotep y))
                    (Equal (equal (len x) y)
                           (if (zp y)
                               (and (equal y 0) (atom x))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- y))))))))

  (defthm-glcp-unify-term/gobj-flg
    (defthm all-keys-bound-of-glcp-unify-term/gobj
      (b* (((mv ok newalist) (glcp-unify-term/gobj pat x alist)))
        (implies ok
                 (all-keys-bound (acl2::simple-term-vars pat) newalist)))
      :hints ('(:in-theory (enable all-keys-bound acl2::simple-term-vars
                                   acl2::simple-term-vars-lst)
                :expand ((:free (x) (glcp-unify-term/gobj pat x alist))
                         (:free (x) (glcp-unify-term/gobj nil x alist)))))
      :flag term)
    (defthm all-keys-bound-of-glcp-unify-term/gobj-list
      (b* (((mv ok newalist) (glcp-unify-term/gobj-list pat x alist)))
        (implies ok
                 (all-keys-bound (acl2::simple-term-vars-lst pat) newalist)))
      :hints ('(:in-theory (enable all-keys-bound)
                :expand ((:free (x) (glcp-unify-term/gobj-list pat x alist))
                         (acl2::simple-term-vars-lst pat))))
      :flag list))


  (defthm-glcp-unify-term/gobj-flg
    (defthm glcp-unify-term/gobj-preserves-eval
      (b* (((mv ok newalist) (glcp-unify-term/gobj pat x alist)))
        (implies (and ok
                      (pseudo-termp term)
                      (all-keys-bound (acl2::simple-term-vars term) alist))
                 (equal (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                     newalist env))
                        (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                     alist env)))))
      :hints ('(:expand ((:free (x) (glcp-unify-term/gobj pat x alist))
                         (:free (x) (glcp-unify-term/gobj nil x alist)))))
      :flag term)
    (defthm glcp-unify-term/gobj-list-preserves-eval
      (b* (((mv ok newalist) (glcp-unify-term/gobj-list pat x alist)))
        (implies (and ok
                      (pseudo-termp term)
                      (all-keys-bound (acl2::simple-term-vars term) alist))
                 (equal (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                     newalist env))
                        (glcp-generic-geval-ev term (glcp-generic-geval-alist
                                                     alist env)))))
      :hints ('(:expand ((:free (x) (glcp-unify-term/gobj-list pat x alist)))))
      :flag list))

  (defthm glcp-unify-term/gobj-preserves-eval-list
    (b* (((mv ok newalist) (glcp-unify-term/gobj pat x alist)))
      (implies (and ok
                    (pseudo-term-listp term)
                    (all-keys-bound (acl2::simple-term-vars-lst term) alist))
               (equal (glcp-generic-geval-ev-lst term (glcp-generic-geval-alist
                                                   newalist env))
                      (glcp-generic-geval-ev-lst term (glcp-generic-geval-alist
                                                       alist env)))))
    :hints (("goal" :induct (len term)
             :in-theory (e/d (acl2::simple-term-vars-lst) (glcp-unify-term/gobj)))))

  (defthm glcp-unify-term/gobj-list-preserves-eval-list
    (b* (((mv ok newalist) (glcp-unify-term/gobj-list pat x alist)))
      (implies (and ok
                    (pseudo-term-listp term)
                    (all-keys-bound (acl2::simple-term-vars-lst term) alist))
               (equal (glcp-generic-geval-ev-lst term (glcp-generic-geval-alist
                                                   newalist env))
                      (glcp-generic-geval-ev-lst term (glcp-generic-geval-alist
                                                       alist env)))))
    :hints (("goal" :induct (len term)
             :in-theory (e/d (acl2::simple-term-vars-lst)
                             (glcp-unify-term/gobj-list)))))

  (local (defthm glcp-generic-geval-of-non-kw-cons
           (implies (and (consp x)
                         (not (equal (tag x) :g-concrete))
                         (not (equal (tag x) :g-boolean))
                         (not (equal (tag x) :g-integer))
                         (not (equal (tag x) :g-ite))
                         (not (equal (tag x) :g-var))
                         (not (equal (tag x) :g-apply)))
                    (equal (glcp-generic-geval x env)
                           (cons (glcp-generic-geval (car x) env)
                                 (glcp-generic-geval (cdr x) env))))
           :hints(("Goal" :expand ((:with glcp-generic-geval
                                    (glcp-generic-geval x env)))))))

  (local (defthm glcp-generic-geval-of-non-kw-symbolp
           (implies (and (consp x)
                         (not (g-keyword-symbolp (tag x))))
                    (equal (glcp-generic-geval x env)
                           (cons (glcp-generic-geval (car x) env)
                                 (glcp-generic-geval (cdr x) env))))
           :hints(("Goal" :expand ((:with glcp-generic-geval
                                    (glcp-generic-geval x env)))))))

  (local (defthm glcp-generic-geval-of-g-apply
           (implies (and (eq (tag x) :g-apply)
                         (not (equal (g-apply->fn x) 'quote)))
                    (equal (glcp-generic-geval x env)
                           (glcp-generic-geval-ev
                            (cons (g-apply->fn x)
                                  (kwote-lst (glcp-generic-geval-list
                                              (g-apply->args x) env)))
                            nil)))
           :hints(("Goal" :expand ((:with glcp-generic-geval
                                    (glcp-generic-geval x env)))))))

  (local (defthm glcp-generic-geval-of-g-concrete
           (implies (eq (tag x) :g-concrete)
                    (equal (glcp-generic-geval x env)
                           (g-concrete->obj x)))
           :hints(("Goal" :expand ((:with glcp-generic-geval
                                    (glcp-generic-geval x env)))
                   :in-theory (disable glcp-generic-geval-general-concrete-obj-correct)))))

  (local (in-theory (enable glcp-generic-geval-ev-of-fncall-args)))

  (local (defthm pseudo-terms-of-args
           (implies (and (pseudo-termp x)
                         (consp x)
                         (not (eq (car x) 'quote)))
                    (and (pseudo-termp (cadr x))
                         (pseudo-termp (caddr x))
                         (pseudo-termp (cadddr x))))
           :hints (("goal" :expand ((pseudo-termp x)
                                    (pseudo-term-listp (cdr x))
                                    (pseudo-term-listp (cddr x))
                                    (pseudo-term-listp (cdddr x)))))))

  (local (defthm symbolp-when-pseudo-termp
           (implies (not (consp x))
                    (equal (pseudo-termp x)
                           (symbolp x)))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (local (defthm pseudo-term-listp-cdr-when-pseudo-termp
           (implies (and (pseudo-termp x)
                         (not (eq (car x) 'quote)))
                    (pseudo-term-listp (cdr x)))))

  (local (in-theory (disable pseudo-term-listp
                             pseudo-termp
                             acl2::cancel_times-equal-correct
                             acl2::cancel_plus-equal-correct
                             tag-when-atom
                             len)))


  (defthm-glcp-unify-term/gobj-flg
    (defthm glcp-unify-term/gobj-correct
      (b* (((mv ok alist)
            (glcp-unify-term/gobj pat x alist)))
        ;; env: boolean vars of x -> boolean values, g-vars of x -> values
        ;; alist: variables of pat -> symbolic objects (subobjects of x)
        (implies (and ok
                      (pseudo-termp pat))
                 (equal (glcp-generic-geval-ev pat
                                               (glcp-generic-geval-alist
                                                alist env))
                        (glcp-generic-geval x env))))
      :hints ('(:expand ((glcp-unify-term/gobj pat x alist)
                         (glcp-unify-term/gobj nil x alist)))
              (and stable-under-simplificationp
                   (b* (((mv ok lit)
                         (acl2::find-matching-literal-in-clause
                          '(not (mv-nth '0 (glcp-unify-concrete pat x alist)))
                          clause nil))
                        ((unless ok) nil)
                        (pat (second (third (second lit))))
                        (x (third (third (second lit))))
                        (alist (fourth (third (second lit)))))
                     `(:use ((:instance glcp-unify-concrete-correct
                              (pat ,pat) (x ,x) (alist ,alist))))))
              (and stable-under-simplificationp
                   '(:expand ((:with glcp-generic-geval
                               (glcp-generic-geval x env))))))
      :flag term)
    (defthm glcp-unify-term/gobj-list-correct
      (b* (((mv ok alist)
            (glcp-unify-term/gobj-list pat x alist)))
        (implies (and ok
                      (pseudo-term-listp pat))
                 (equal (glcp-generic-geval-ev-lst pat
                                                   (glcp-generic-geval-alist alist
                                                                             env))
                        (glcp-generic-geval-list x env))))
      :hints ('(:expand ((glcp-unify-term/gobj-list pat x alist)))
              (and stable-under-simplificationp
                   '(:expand ((pseudo-term-listp pat)))))
      :flag list))

  (local (in-theory (disable gobj-depends-on gobj-list-depends-on)))

  (defthm-glcp-unify-term/gobj-flg
    (defthm gobj-depends-on-of-glcp-unify-term/gobj
      (implies (and (not (gobj-alist-depends-on k p alist))
                    (not (gobj-depends-on k p x)))
               (not (gobj-alist-depends-on
                     k p (mv-nth 1 (glcp-unify-term/gobj pat x alist)))))
      :hints ('(:expand ((:free (x) (glcp-unify-term/gobj pat x alist))
                         (:free (x) (glcp-unify-term/gobj nil x alist))
                         (gobj-depends-on k p x)
                         (gobj-depends-on k p nil)
                         (gobj-depends-on k p (cdr (hons-assoc-equal pat alist))))))
      :flag term)
    (defthm gobj-depends-on-of-glcp-unify-term/gobj-list
      (implies (and (not (gobj-alist-depends-on k p alist))
                    (not (gobj-list-depends-on k p x)))
               (not (gobj-alist-depends-on
                     k p (mv-nth 1 (glcp-unify-term/gobj-list pat x alist)))))
      :hints ('(:expand ((:free (x) (glcp-unify-term/gobj-list pat x alist))
                         (gobj-list-depends-on k p x)
                         (gobj-list-depends-on k p nil))))
      :flag list)))
