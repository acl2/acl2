;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "CMR")

(include-book "unify-strict")
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (defthm member-of-union
         (iff (member x (union-eq a b))
              (or (member x a)
                  (member x b)))))

(local (defthm union-eq-associative
         (equal (union-eq (union-eq a b) c)
                (union-eq a (union-eq b c)))))

;; pick up some set lemmas
(local (deflist pseudo-var-list :elt-type pseudo-var :true-listp t))

(define term-subst-vars-acc ((x pseudo-term-subst-p)
                             (acc pseudo-var-list-p))
  :returns (vars pseudo-var-list-p)
  :verify-guards nil
  (if (atom x)
      (pseudo-var-list-fix acc)
    (term-subst-vars-acc
     (cdr x)
     (if (mbt (and (consp (Car x))
                   (pseudo-var-p (caar x))))
         (term-vars-acc (cdar x) acc)
       (pseudo-var-list-fix acc))))
  ///
  (verify-guards term-subst-vars-acc)
  (local (in-theory (enable pseudo-term-subst-fix))))

(local (defthm union-nil
         (equal (union-eq x nil)
                (true-list-fix x))))

(define term-subst-vars ((x pseudo-term-subst-p))
  :returns (vars pseudo-var-list-p)
  :verify-guards nil
  (mbe :logic (if (atom x)
                  nil
                (if (mbt (and (consp (car x))
                              (pseudo-var-p (caar x))))
                    (union-eq (term-subst-vars (cdr x))
                              (term-vars (cdar x)))
                  (term-subst-vars (cdr x))))
       :exec (term-subst-vars-acc x nil))
  ///
  (local (defthm true-listp-when-pseudo-var-list-p-rw
           (implies (pseudo-var-list-p x)
                    (true-listp x))))
  
  (defthm term-subst-vars-acc-is-term-subst-vars
    (equal (term-subst-vars-acc x acc)
           (union-eq (term-subst-vars x) (pseudo-var-list-fix acc)))
    :hints(("Goal" :in-theory (enable term-subst-vars-acc)
            :induct (term-subst-vars-acc x acc))))
  (verify-guards term-subst-vars)

  (defthm member-term-vars-of-lookup-when-not-member-term-subst-vars
    (implies (and (not (member v (term-subst-vars x)))
                  (pseudo-var-p k))
             (not (member v (term-vars (cdr (assoc-equal k x))))))
    :hints(("Goal" :in-theory (enable term-subst-vars))))
  (local (in-theory (enable pseudo-term-subst-fix))))



(defret-mutual member-vars-of-term-subst-strict
  (defret member-vars-of-term-subst-strict
    (implies (not (member v (term-subst-vars a)))
             (not (member v (term-vars new-x))))
    :hints ('(:expand (<call>
                       (:free (fn args) (term-vars (pseudo-term-call fn args)))))
            (and stable-under-simplificationp
                 '(:expand ((term-vars x)))))
    :fn term-subst-strict)
  (defret member-vars-of-termlist-subst-strict
    (implies (not (member v (term-subst-vars a)))
             (not (member v (termlist-vars new-x))))
    :hints ('(:expand (<call>
                       (:free (a b) (termlist-vars (cons a b))))))
    :fn termlist-subst-strict)
  :mutual-recursion term-subst-strict)

(local (flag::make-flag term-unify-strict-flag term-unify-strict))

(defret-mutual member-vars-of-unify-strict-subst
  (defret member-vars-of-term-unify-strict
    (implies (and (not (member v (term-vars x)))
                  (not (member v (term-subst-vars alist))))
             (not (member v (term-subst-vars new-alist))))
    :hints ('(:expand (<call>
                       (term-vars x)
                       (:free (pair rest) (term-subst-vars (cons pair rest))))))
    :fn term-unify-strict)

  (defret member-vars-of-termlist-unify-strict
    (implies (and (not (member v (termlist-vars x)))
                  (not (member v (term-subst-vars alist))))
             (not (member v (term-subst-vars new-alist))))
    :hints ('(:expand (<call>
                       (termlist-vars x))))
    :fn termlist-unify-strict))

                         
