; Centaur Meta-reasoning Library
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

(in-package "CMR")

(include-book "subst")
(include-book "clause-processors/eval-alist-equiv" :dir :system)

;; must be below the definition of pseudo-var-list if it's to be local
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "assoc-is-hons-assoc"))

(local (defthm member-of-union
         (iff (member x (union-eq a b))
              (or (member x a)
                  (member x b)))))

(local (defthm union-eq-associative
         (equal (union-eq (union-eq a b) c)
                (union-eq a (union-eq b c)))))

;; pick up some set lemmas
(local (deflist pseudo-var-list :elt-type pseudo-var :true-listp t))

(defines term-vars-acc
  (define term-vars-acc ((x pseudo-termp)
                         (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :verify-guards nil
    :measure (pseudo-term-count x)
    (b* ((acc (pseudo-var-list-fix acc)))
      (pseudo-term-case x
        :const acc
        :var (add-to-set-eq x.name acc)
        :call (termlist-vars-acc x.args acc))))

  (define termlist-vars-acc ((x pseudo-term-listp)
                             (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        (pseudo-var-list-fix acc)
      (termlist-vars-acc (cdr x)
                         (term-vars-acc (car x) acc))))
  ///
  (verify-guards term-vars-acc))

(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (pseudo-var-list-p x)
                  (symbol-listp x))))

(defines term-vars
  (define term-vars ((x pseudo-termp))
    :returns (vars pseudo-var-list-p)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (mbe :logic (pseudo-term-case x
                  :const nil
                  :var (list x.name)
                  :call (termlist-vars x.args))
         :exec (term-vars-acc x nil)))
  (define termlist-vars ((x pseudo-term-listp))
    :returns (vars pseudo-var-list-p)
    :measure (pseudo-term-list-count x)
    (mbe :logic (if (atom x)
                    nil
                  (union-eq (termlist-vars (cdr x))
                            (term-vars (car x))))
         :exec (termlist-vars-acc x nil)))
  :flag-local nil
  ///
  (local (defun-sk term-vars-acc-is-term-vars-sk (x)
           (forall acc
                   (equal (term-vars-acc x acc)
                          (union-eq (term-vars x) (pseudo-var-list-fix acc))))
           :rewrite :direct))
  (local (defun-sk termlist-vars-acc-is-termlist-vars-sk (x)
           (forall acc
                   (equal (termlist-vars-acc x acc)
                          (union-eq (termlist-vars x) (pseudo-var-list-fix acc))))
           :rewrite :direct))
  (local (in-theory (disable term-vars-acc-is-term-vars-sk
                             termlist-vars-acc-is-termlist-vars-sk)))

  (local
   (defthm-term-vars-flag
     (defthm term-vars-acc-is-term-vars-lemma
       (term-vars-acc-is-term-vars-sk x)
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (term-vars x)
                               (:free (acc) (term-vars-acc x acc))
                               (:free (acc) (term-vars-acc nil acc))))))
       :flag term-vars
       :rule-classes nil)
     (defthm termlist-vars-acc-is-termlist-vars-lemma
       (termlist-vars-acc-is-termlist-vars-sk x)
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (termlist-vars x)
                               (:free (acc) (termlist-vars-acc x acc))))))
       :flag termlist-vars
       :rule-classes nil)))

  (defthm term-vars-acc-is-term-vars
    (equal (term-vars-acc x acc)
           (union-eq (term-vars x) (pseudo-var-list-fix acc)))
    :hints (("goal" :use term-vars-acc-is-term-vars-lemma)))
  (defthm termlist-vars-acc-is-termlist-vars
    (equal (termlist-vars-acc x acc)
           (union-eq (termlist-vars x) (pseudo-var-list-fix acc)))
    :hints (("goal" :use termlist-vars-acc-is-termlist-vars-lemma)))

  (defthm termlist-vars-of-atom
    (implies (not (consp x))
             (equal (termlist-vars x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))
  
  (defthm-term-vars-flag
    (defthm true-listp-of-term-vars
      (true-listp (term-vars x))
      :hints ((and stable-under-simplificationp
                   '(:expand ((term-vars x)))))
      :flag term-vars
      :rule-classes :type-prescription)
    (defthm true-listp-of-termlist-vars
      (true-listp (termlist-vars x))
      :hints ((and stable-under-simplificationp
                   '(:expand ((termlist-vars x)))))
      :flag termlist-vars
      :rule-classes :type-prescription))

  (local (defthm union-eq-nil
           (implies (true-listp x)
                    (equal (union-eq x nil) x))))

  (verify-guards term-vars)

  (deffixequiv-mutual term-vars)

  (defthm-term-vars-flag
    (defthm no-duplicatesp-of-term-vars
      (no-duplicatesp (term-vars x))
      :hints ((and stable-under-simplificationp
                   '(:expand ((term-vars x)))))
      :flag term-vars
      :rule-classes :type-prescription)
    (defthm no-duplicatesp-of-termlist-vars
      (no-duplicatesp (termlist-vars x))
      :hints ((and stable-under-simplificationp
                   '(:expand ((termlist-vars x)))))
      :flag termlist-vars
      :rule-classes :type-prescription))

  (local (defthm subsetp-of-union-1
           (subsetp a (union-eq a b))))

  (local (defthm subsetp-of-union-2
           (subsetp b (union-eq a b))))

  (defthm-term-vars-flag
    (defthm base-ev-when-agree-on-term-vars
      (implies (eval-alists-agree (term-vars x) a b)
               (equal (base-ev x a)
                      (base-ev x b)))
      :hints ('(:expand ((term-vars x))
                :in-theory (enable acl2::lookup-when-eval-alists-agree
                                   acl2::base-ev-when-pseudo-term-call)))
      :flag term-vars)
    (defthm base-ev-list-when-agree-on-termlist-vars
      (implies (eval-alists-agree (termlist-vars x) a b)
               (equal (base-ev-list x a)
                      (base-ev-list x b)))
      :hints ('(:expand ((termlist-vars x))))
      :flag termlist-vars)))


(defines term-free-vars-acc
  (define term-free-vars-acc ((x pseudo-termp)
                              (bound-vars symbol-listp)
                              (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :verify-guards nil
    :measure (pseudo-term-count x)
    (b* ((acc (pseudo-var-list-fix acc)))
      (pseudo-term-case x
        :const acc
        :var (if (member-eq x.name bound-vars)
                 acc
               (add-to-set-eq x.name acc))
        :call (termlist-free-vars-acc x.args bound-vars acc))))

  (define termlist-free-vars-acc ((x pseudo-term-listp)
                                  (bound-vars symbol-listp)
                                  (acc pseudo-var-list-p))
    :returns (vars pseudo-var-list-p)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        (pseudo-var-list-fix acc)
      (termlist-free-vars-acc (cdr x) bound-vars
                              (term-free-vars-acc (car x) bound-vars acc))))
  ///
  (verify-guards term-free-vars-acc))


(defines term-free-vars
  (define term-free-vars ((x pseudo-termp)
                          (bound-vars symbol-listp))
    :returns (vars pseudo-var-list-p)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (mbe :logic (pseudo-term-case x
                  :const nil
                  :var (and (not (member x.name bound-vars))
                            (list x.name))
                  :call (termlist-free-vars x.args bound-vars))
         :exec (term-free-vars-acc x bound-vars nil)))
  (define termlist-free-vars ((x pseudo-term-listp)
                              (bound-vars symbol-listp))
    :returns (vars pseudo-var-list-p)
    :measure (pseudo-term-list-count x)
    (mbe :logic (if (atom x)
                    nil
                  (union-eq (termlist-free-vars (cdr x) bound-vars)
                            (term-free-vars (car x) bound-vars)))
         :exec (termlist-free-vars-acc x bound-vars nil)))
  ///

  (local (defun-sk term-free-vars-acc-is-term-free-vars-sk (x bound-vars)
           (forall acc
                   (equal (term-free-vars-acc x bound-vars acc)
                          (union-eq (term-free-vars x bound-vars)
                                    (pseudo-var-list-fix acc))))
           :rewrite :direct))
  (local (defun-sk termlist-free-vars-acc-is-termlist-free-vars-sk (x bound-vars)
           (forall acc
                   (equal (termlist-free-vars-acc x bound-vars acc)
                          (union-eq (termlist-free-vars x bound-vars)
                                    (pseudo-var-list-fix acc))))
           :rewrite :direct))
  (local (in-theory (disable term-free-vars-acc-is-term-free-vars-sk
                             termlist-free-vars-acc-is-termlist-free-vars-sk)))

  (local
   (defthm-term-free-vars-flag
     (defthm term-free-vars-acc-is-term-free-vars-lemma
       (term-free-vars-acc-is-term-free-vars-sk x bound-vars)
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (term-free-vars x bound-vars)
                               (:free (acc) (term-free-vars-acc x bound-vars acc))
                               (:free (acc) (term-free-vars-acc nil bound-vars acc))))))
       :flag term-free-vars
       :rule-classes nil)
     (defthm termlist-free-vars-acc-is-termlist-free-vars-lemma
       (termlist-free-vars-acc-is-termlist-free-vars-sk x bound-vars)
       :hints ((and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (termlist-free-vars x bound-vars)
                               (:free (acc) (termlist-free-vars-acc x bound-vars acc))))))
       :flag termlist-free-vars
       :rule-classes nil)))

  (defthm term-free-vars-acc-is-term-free-vars
    (equal (term-free-vars-acc x bound-vars acc)
           (union-eq (term-free-vars x bound-vars)
                     (pseudo-var-list-fix acc)))
    :hints (("goal" :use term-free-vars-acc-is-term-free-vars-lemma)))
  (defthm termlist-free-vars-acc-is-termlist-free-vars
    (equal (termlist-free-vars-acc x bound-vars acc)
           (union-eq (termlist-free-vars x bound-vars)
                     (pseudo-var-list-fix acc)))
    :hints (("goal" :use termlist-free-vars-acc-is-termlist-free-vars-lemma)))

  (defthm-term-free-vars-flag
    (defthm true-listp-of-term-free-vars
      (true-listp (term-free-vars x bound-vars))
      :hints ((and stable-under-simplificationp
                   '(:expand ((term-free-vars x bound-vars)))))
      :flag term-free-vars
      :rule-classes :type-prescription)
    (defthm true-listp-of-termlist-free-vars
      (true-listp (termlist-free-vars x bound-vars))
      :hints ((and stable-under-simplificationp
                   '(:expand ((termlist-free-vars x bound-vars)))))
      :flag termlist-free-vars
      :rule-classes :type-prescription))

  (local (defthm union-equal-nil
           (implies (true-listp x)
                    (equal (union-equal x nil) x))))

  (verify-guards term-free-vars)

  (defthm-term-free-vars-flag
    (defthm term-free-vars-in-terms-of-term-vars
      (equal (term-free-vars x bound-vars)
             (set-difference-eq (term-vars x)
                                bound-vars))
      :hints ('(:expand ((term-vars x))))
      :flag term-free-vars)
    (defthm termlist-free-vars-in-terms-of-term-vars
      (equal (termlist-free-vars x bound-vars)
             (set-difference-eq (termlist-vars x)
                                bound-vars))
      :hints ('(:expand ((termlist-vars x))))
      :flag termlist-free-vars))

  (deffixequiv-mutual term-free-vars :omit (bound-vars)))


(local (defthm consp-of-member-is-member
         (equal (consp (member k x))
                (and (member k x) t))))
         

(defines member-term-vars
  :flag nil
  (define member-term-vars ((v pseudo-var-p) (x pseudo-termp))
    :measure (pseudo-term-count x)
    :enabled t
    :guard-hints (("goal" :expand ((term-vars x)
                                   (termlist-vars x))))
    (mbe :logic (consp (member (pseudo-var-fix v)
                               (term-vars x)))
         :exec (pseudo-term-case x
                 :const nil
                 :var (eq v x.name)
                 :call (member-termlist-vars v x.args))))
  
  (define member-termlist-vars ((v pseudo-var-p) (x pseudo-term-listp))
    :measure (pseudo-term-list-count x)
    :enabled t
    (mbe :logic (consp (member (pseudo-var-fix v) (termlist-vars x)))
         :exec (if (atom x)
                   nil
                 (or (member-term-vars v (car x))
                     (member-termlist-vars v (cdr x)))))))

