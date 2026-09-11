; Centaur Meta-reasoning Library
; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
; SPDX-License-Identifier: BSD-3-Clause
; 
; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holder nor the names of
;   its contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Author: Sol Swords <sol.swords@arm.com>

(in-package "CMR")

(include-book "substitute")
(include-book "term-vars")

(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local
 (defthm assoc-is-hons-assoc
   (implies k
            (equal (assoc k x)
                   (hons-assoc-equal k x)))))

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(defevaluator unify-ev unify-ev-list
  ((cons a b) (binary-+ a b))
  :namedp t)

(acl2::def-ev-pseudo-term-fty-support unify-ev unify-ev-list)



(define unify-ev-alist (x al)
  :verify-guards nil
  (if (atom x)
      nil
    (cons (cons (caar x) (unify-ev (cdar x) al))
          (unify-ev-alist (cdr x) al)))
  ///
  (defthm assoc-equal-unify-ev-alist
    (equal (cdr (assoc-equal k (unify-ev-alist x al)))
           (unify-ev (cdr (assoc-equal k x)) al)))

  (defthm assoc-equal-unify-ev-alist-iff
    (implies k
             (iff (assoc-equal k (unify-ev-alist x al))
                  (assoc-equal k x))))

  (defthm assoc-equal-unify-ev-alist-when-assoc
    (implies (assoc k x)
             (assoc k (unify-ev-alist x al))))

  (defthm unify-ev-alist-pairlis$
    (equal (unify-ev-alist (pairlis$ a b) al)
           (pairlis$ a
                     (unify-ev-list b al))))

  (defthm unify-ev-alist-of-cons
    (equal (unify-ev-alist (cons x y) a)
           (cons (cons (car x) (unify-ev (cdr x) a))
                 (unify-ev-alist y a)))))

(define term-unify-const ((pat pseudo-termp)
                          const
                          (alist pseudo-term-subst-p))
  :measure (pseudo-term-count pat)
  :returns (mv ok (new-alist pseudo-term-subst-p))
  :verify-guards nil
  (b* ((alist (pseudo-term-subst-fix alist)))
    (pseudo-term-case pat
      :const (mv (equal const pat.val) alist)
      :var (b* ((look (assoc pat.name alist)))
             (if look
                 (b* ((term (cdr look)))
                   (mv (pseudo-term-case term
                         :const (equal const term.val)
                         :otherwise nil)
                       alist))
               (mv t (cons (cons pat.name (pseudo-term-quote const))
                           alist))))
      :fncall
      (case pat.fn
        (cons
         (b* (((unless (and (consp const)
                            (eql (len pat.args) 2)))
               (mv nil alist))
              ((mv ok alist) (term-unify-const (first pat.args) (car const) alist))
              ((unless ok) (mv nil alist)))
           (term-unify-const (second pat.args) (cdr const) alist)))
        (binary-+
         (b* (((unless (and (acl2-numberp const)
                            (eql (len pat.args) 2)))
               (mv nil alist))
              ((when (pseudo-term-case (first pat.args) :const))
               (b* ((incr (pseudo-term-const->val (first pat.args)))
                    ((unless (acl2-numberp incr))
                     (mv nil alist)))
                 (term-unify-const (second pat.args) (- const incr) alist)))
              ((when (pseudo-term-case (second pat.args) :const))
               (b* ((incr (pseudo-term-const->val (second pat.args)))
                    ((unless (acl2-numberp incr))
                     (mv nil alist)))
                 (term-unify-const (first pat.args) (- const incr) alist))))
           (mv nil alist)))
        (t (mv nil alist)))
      :otherwise (mv nil alist)))
  ///
  (verify-guards term-unify-const)
  (fty::deffixequiv term-unify-const)

  (defund-nx term-unify-const-ok (pat x alist)
    (mv-nth 0 (term-unify-const pat x alist)))

  (local (in-theory (enable term-unify-const-ok)))

  (defthm term-unify-const-ok-when-ok
    (implies (term-unify-const-ok pat x alist)
             (mv-nth 0 (term-unify-const pat x alist)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defret <fn>-preserves-pairs
    (implies (and (hons-assoc-equal k (pseudo-term-subst-fix alist)) ok)
             (equal (hons-assoc-equal k new-alist)
                    (hons-assoc-equal k (pseudo-term-subst-fix alist))))
    :hints (("goal" :induct <call> :expand (<call>))))

  (local (defthm term-vars-when-const
           (implies (pseudo-term-case x :const)
                    (equal (term-vars x) nil))
           :hints (("goal" :expand ((term-vars x))))))

  (local (defthm equal-of-len
           (implies (syntaxp (quotep n))
                    (equal (equal (len x) n)
                           (if (zp n)
                               (and (atom x) (eql n 0))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- n))))))))

  (local (defthm len-of-cons
           (equal (len (cons x y))
                  (+ 1 (len y)))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (not (consp x)))))
  (local (defthm member-singleton
           (iff (member x (list y))
                (equal x y))))
  
  (local (in-theory (disable len acl2::member-of-cons member-equal)))
  
  
  (defret <fn>-binds-pat-vars
    (implies (and (member k (term-vars pat)) ok)
             (hons-assoc-equal k new-alist))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (term-vars pat)
                      (termlist-vars (pseudo-term-call->args pat))
                      (termlist-vars (cdr (pseudo-term-call->args pat)))))))

  (defret <fn>-lookup-under-iff
    (implies ok
             (iff (hons-assoc-equal k new-alist)
                  (or (hons-assoc-equal k (pseudo-term-subst-fix alist))
                      (member k (term-vars pat)))))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (term-vars pat)
                      (termlist-vars (pseudo-term-call->args pat))
                      (termlist-vars (cdr (pseudo-term-call->args pat)))))))

  (defret alist-keys-subsetp-of-<fn>
    (implies ok
             (subsetp (alist-keys (pseudo-term-subst-fix alist))
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw))))

  (defret term-vars-subsetp-of-<fn>
    (implies ok
             (subsetp (term-vars pat)
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw))))

  (defret <fn>-preserves-term-subst-strict
    (implies (subsetp (term-vars y) (alist-keys (pseudo-term-subst-fix alist)))
             (equal (term-subst-strict y new-alist)
                    (term-subst-strict y alist)))
    :hints (("goal" :induct <call>
             :in-theory (e/d (ACL2::HONS-ASSOC-EQUAL-IFF-MEMBER-ALIST-KEYS)
                             (acl2::alist-keys-member-hons-assoc-equal))                              
             :expand (<call>
                      (term-vars pat)
                      (termlist-vars (pseudo-term-call->args pat))
                      (termlist-vars (cdr (pseudo-term-call->args pat)))))))

  (defret <fn>-preserves-termlist-subst-strict
    (implies (subsetp (termlist-vars y) (alist-keys (pseudo-term-subst-fix alist)))
             (equal (termlist-subst-strict y new-alist)
                    (termlist-subst-strict y alist)))
    :hints (("goal" :induct <call>
             :in-theory (e/d (ACL2::HONS-ASSOC-EQUAL-IFF-MEMBER-ALIST-KEYS)
                             (acl2::alist-keys-member-hons-assoc-equal))                              
             :expand (<call>
                      (term-vars pat)
                      (termlist-vars (pseudo-term-call->args pat))
                      (termlist-vars (cdr (pseudo-term-call->args pat)))))))

  (local (defthm unify-ev-when-const
           (implies (pseudo-term-case x :const)
                    (equal (unify-ev x env)
                           (pseudo-term-const->val x)))
           :hints(("Goal" :in-theory (enable acl2::member-of-cons)))))

  (local (defthm term-subst-strict-when-const
           (implies (pseudo-term-case x :const)
                    (equal (term-subst-strict x a)
                           (pseudo-term-fix x)))
           :hints(("Goal" :expand ((term-subst-strict x a))))))
  
  (defret <fn>-reversible
    (implies ok
             (equal (unify-ev (term-subst-strict pat new-alist) env)
                    const))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (alist) (term-subst-strict pat alist))
                      (:free (alist) (termlist-subst-strict (pseudo-term-call->args pat) alist))
                      (:free (alist) (termlist-subst-strict (cdr (pseudo-term-call->args pat)) alist)))))))




(defines term-unify
  (define term-unify ((pat pseudo-termp)
                      (x pseudo-termp)
                      (alist pseudo-term-subst-p))
    :measure (pseudo-term-count pat)
    :hints ((and stable-under-simplificationp
                 '(:cases ((equal (pseudo-term-kind pat) :lambda)
                           (equal (pseudo-term-kind pat) :fncall)))))
    :returns (mv ok (new-alist pseudo-term-subst-p))
    :verify-guards nil
    (b* ((x (pseudo-term-fix x))
         (alist (pseudo-term-subst-fix alist))
         ((when (pseudo-term-case x :const))
          (term-unify-const pat (pseudo-term-const->val x) alist)))
      (pseudo-term-case pat
        :var (b* ((look (assoc pat.name alist)))
               (if look
                   (if (equal (cdr look) x)
                       (mv t alist)
                     (mv nil alist))
                 (mv t (cons (cons pat.name x) alist))))
        :null (mv (pseudo-term-case x :null) alist)
        :quote (pseudo-term-case x
                 :quote
                 (if (equal x.val pat.val)
                     (mv t alist)
                   (mv nil alist))
                 :otherwise (mv nil alist))
        :call (pseudo-term-case x
                :call
                (if (equal x.fn pat.fn)
                    (termlist-unify pat.args x.args alist)
                  (mv nil alist))
                :otherwise (mv nil alist)))))
  (define termlist-unify ((pat pseudo-term-listp)
                          (x pseudo-term-listp)
                          (alist pseudo-term-subst-p))
    :measure (pseudo-term-list-count pat)
    :returns (mv ok (new-alist pseudo-term-subst-p))
    (b* ((alist (pseudo-term-subst-fix alist)))
      (if (atom pat)
          (if (atom x)
              (mv t alist)
            (mv nil alist))
        (if (atom x)
            (mv nil alist)
          (b* (((mv ok alist) (term-unify (car pat) (car x) alist))
               ((unless ok) (mv nil alist)))
            (termlist-unify (cdr pat) (cdr x) alist))))))

  ///
  (verify-guards term-unify)
  
  (fty::deffixequiv-mutual term-unify)

  (defund-nx term-unify-ok (pat x alist)
    (mv-nth 0 (term-unify pat x alist)))

  (local (in-theory (enable term-unify-ok)))

  (defthm term-unify-ok-when-ok
    (implies (term-unify-ok pat x alist)
             (mv-nth 0 (term-unify pat x alist)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defund-nx termlist-unify-ok (pat x alist)
    (mv-nth 0 (termlist-unify pat x alist)))

  (local (in-theory (enable termlist-unify-ok)))

  (defthm termlist-unify-ok-when-ok
    (implies (termlist-unify-ok pat x alist)
             (mv-nth 0 (termlist-unify pat x alist)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defret-mutual <fn>-preserves-pairs
    (defret <fn>-preserves-pairs
      (implies (and (hons-assoc-equal k (pseudo-term-subst-fix alist)) ok)
               (equal (hons-assoc-equal k new-alist)
                      (hons-assoc-equal k (pseudo-term-subst-fix alist))))
      :hints ('(:expand (<call>)))
      :fn term-unify)

    (defret <fn>-preserves-pairs
      (implies (and (hons-assoc-equal k (pseudo-term-subst-fix alist)) ok)
               (equal (hons-assoc-equal k new-alist)
                      (hons-assoc-equal k (pseudo-term-subst-fix alist))))
      :hints ('(:expand (<call>)))      
      :fn termlist-unify))
  
  ;; (local (defthm member-singleton
  ;;          (iff (member x (list y))
  ;;               (equal x y))))
  ;; (local (in-theory (disable len acl2::member-of-cons member-equal)))

  (defret-mutual <fn>-binds-pat-vars
    (defret <fn>-binds-pat-vars
      (implies (and (member k (term-vars pat)) ok)
               (hons-assoc-equal k new-alist))
      :hints ('(:expand (<call>
                         (term-vars pat))))
      :fn term-unify)

    (defret <fn>-binds-pat-vars
      (implies (and (member k (termlist-vars pat)) ok)
               (hons-assoc-equal k new-alist))
      :hints ('(:expand (<call>
                         (termlist-vars pat))))
      :fn termlist-unify))

  (defret-mutual <fn>-lookup-under-iff
    (defret <fn>-lookup-under-iff
      (implies ok
               (iff (hons-assoc-equal k new-alist)
                    (or (hons-assoc-equal k (pseudo-term-subst-fix alist))
                        (member k (term-vars pat)))))
      :hints ('(:expand (<call>
                         (term-vars pat))))
      :fn term-unify)

    (defret <fn>-lookup-under-iff
      (implies ok
               (iff (hons-assoc-equal k new-alist)
                    (or (hons-assoc-equal k (pseudo-term-subst-fix alist))
                        (member k (termlist-vars pat)))))
      :hints ('(:expand (<call>
                         (termlist-vars pat))))
      :fn termlist-unify))

  (local (defthm not-member-when-subsetp-and-hons-assoc
           (implies (and (not (hons-assoc-equal k a))
                         (subsetp x (alist-keys (pseudo-term-subst-fix a))))
                    (not (member k x)))))

  (defret alist-keys-subsetp-of-<fn>
    (implies ok
             (subsetp (alist-keys (pseudo-term-subst-fix alist))
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))
    :fn term-unify)

  (defret alist-keys-subsetp-of-<fn>
    (implies ok
             (subsetp (alist-keys (pseudo-term-subst-fix alist))
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))
    :fn termlist-unify)

  (defret term-vars-subsetp-of-<fn>
    (implies ok
             (subsetp (term-vars pat)
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))
    :fn term-unify)

  (defret termlist-vars-subsetp-of-<fn>
    (implies ok
             (subsetp (termlist-vars pat)
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))
    :fn termlist-unify)

  (defret-mutual <fn>-preserves-term-subst-strict
    (defret <fn>-preserves-term-subst-strict
      (implies (subsetp (term-vars y) (alist-keys (pseudo-term-subst-fix alist)))
               (equal (term-subst-strict y new-alist)
                      (term-subst-strict y alist)))
      :hints ('(:expand ((term-vars x)
                         <call>)))
      :fn term-unify)
    (defret <fn>-preserves-term-subst-strict
      (implies (subsetp (term-vars y) (alist-keys (pseudo-term-subst-fix alist)))
               (equal (term-subst-strict y new-alist)
                      (term-subst-strict y alist)))
      :hints ('(:expand ((termlist-vars x)
                         <call>)))
      :fn termlist-unify))


  (defret-mutual <fn>-preserves-termlist-subst-strict
    (defret <fn>-preserves-termlist-subst-strict
      (implies (subsetp (termlist-vars y) (alist-keys (pseudo-term-subst-fix alist)))
               (equal (termlist-subst-strict y new-alist)
                      (termlist-subst-strict y alist)))
      :hints ('(:expand ((term-vars x)
                         <call>)))
      :fn term-unify)
    (defret <fn>-preserves-termlist-subst-strict
      (implies (subsetp (termlist-vars y) (alist-keys (pseudo-term-subst-fix alist)))
               (equal (termlist-subst-strict y new-alist)
                      (termlist-subst-strict y alist)))
      :hints ('(:expand ((termlist-vars x)
                         <call>)))
      :fn termlist-unify))


  (local (defthm pseudo-term-fix-when-pseudo-term-quote
           (implies (pseudo-term-case x :quote)
                    (equal (pseudo-term-fix x)
                           (pseudo-term-quote (pseudo-term-quote->val x))))))
  (local (in-theory (disable acl2::pseudo-term-quote-of-accessors)))

  (defret-mutual <fn>-reversible
    (defret <fn>-reversible
      (implies ok
               (equal (unify-ev (term-subst-strict pat new-alist) env)
                      (unify-ev x env)))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((:free (alist) (term-subst-strict pat alist)))
                     :in-theory (enable unify-ev-of-fncall-args))))
      :fn term-unify)
    (defret <fn>-reversible
      (implies ok
               (equal (unify-ev-list (termlist-subst-strict pat new-alist) env)
                      (unify-ev-list x env)))
      :hints ('(:expand (<call>
                         (:free (alist) (termlist-subst-strict pat alist))))
              (and stable-under-simplificationp
                   '(:expand ((pseudo-term-list-fix x)))))
      :fn termlist-unify)))

