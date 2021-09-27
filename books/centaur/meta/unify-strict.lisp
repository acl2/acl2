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

(include-book "substitute")
(include-book "term-vars")

(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local
 (defthm assoc-is-hons-assoc
   (implies k
            (equal (assoc k x)
                   (hons-assoc-equal k x)))))

(local (in-theory (disable pseudo-termp)))

(local (include-book "std/lists/take" :dir :system))

(local (defthm take-of-pseudo-term-list-fix
         (equal (take n (pseudo-term-list-fix args))
                (pseudo-term-list-fix (take n args)))
         :hints(("Goal" :in-theory (enable pseudo-term-list-fix)))))



(local (defthm pseudo-term-lambda-of-replace-non-symbols
         (equal (pseudo-term-lambda (replace-non-symbols-with-nil formals)
                                    body
                                    (take (len formals) args))
                (pseudo-term-lambda formals body args))
         :hints(("Goal" :in-theory (enable pseudo-term-lambda
                                           pseudo-lambda)))))

(defthmd equal-of-pseudo-term-lambda
  (equal (equal (pseudo-term-lambda formals body args) x)
         (and (pseudo-termp x)
              (pseudo-term-case x :lambda)
              (equal (pseudo-term-lambda->formals x) (replace-non-symbols-with-nil formals))
              (equal (pseudo-term-call->args x) (take (len formals) (pseudo-term-list-fix args)))
              (equal (pseudo-term-lambda->body x) (pseudo-term-fix body))))
  :hints (("goal" :use ((:instance ACL2::PSEUDO-TERM-LAMBDA-OF-ACCESSORS)
                        (:instance pseudo-term-lambda-of-replace-non-symbols))
           :in-theory (e/d ()
                           (ACL2::PSEUDO-TERM-LAMBDA-OF-ACCESSORS
                            pseudo-term-lambda-of-replace-non-symbols))))
  :otf-flg t)



(defthmd equal-of-pseudo-term-fncall
  (equal (equal (pseudo-term-fncall fn args) x)
         (and (pseudo-termp x)
              (pseudo-term-case x :fncall)
              (equal (pseudo-term-fncall->fn x) (pseudo-fnsym-fix fn))
              (equal (pseudo-term-call->args x) (pseudo-term-list-fix args))))
  :hints (("goal" :use ((:instance ACL2::PSEUDO-TERM-FNCALL-OF-ACCESSORS))
           :in-theory (disable ACL2::PSEUDO-TERM-FNCALL-OF-ACCESSORS))))

(defthmd equal-of-pseudo-term-call
  (equal (equal (pseudo-term-call fn args) x)
         (if (consp fn)
             (equal (pseudo-term-lambda
                     (acl2::pseudo-lambda->formals fn)
                     (acl2::pseudo-lambda->body fn)
                     args)
                    x)
           (equal (pseudo-term-fncall fn args) x)))
  :hints(("Goal" :in-theory (enable pseudo-term-call))))

(defthmd equal-of-pseudo-term-quote
  (equal (equal (pseudo-term-quote val) x)
         (and (pseudo-termp x)
              (pseudo-term-case x :quote)
              (equal (pseudo-term-quote->val x) val))))

(defthmd equal-of-pseudo-term-lambda->fn
  (implies (pseudo-term-case x :lambda)
           (equal (equal (pseudo-term-lambda->fn x) y)
                  (and (pseudo-lambda-p y)
                       (equal (pseudo-term-lambda->formals x)
                              (acl2::pseudo-lambda->formals y))
                       (equal (pseudo-term-lambda->body x)
                              (acl2::pseudo-lambda->body y)))))
  :hints (("goal" :use ((:instance acl2::pseudo-term-lambda->fn-of-pseudo-term-lambda
                         (formals (pseudo-term-lambda->formals x))
                         (body (pseudo-term-lambda->body x))
                         (args (pseudo-term-call->args x))))
           :in-theory (disable acl2::pseudo-term-lambda->fn-of-pseudo-term-lambda)))
  )

(local
 (defthm pseudo-term-fix-under-iff
   (iff (pseudo-term-fix x)
        (not (pseudo-term-case x :null)))
   :hints(("Goal" :in-theory (enable pseudo-term-fix
                                     pseudo-term-kind)))))


(defines term-unify-strict
  (define term-unify-strict ((pat pseudo-termp)
                             (x pseudo-termp)
                             (alist pseudo-term-subst-p))
    :measure (pseudo-term-count pat)
    :hints ((and stable-under-simplificationp
                 '(:cases ((equal (pseudo-term-kind pat) :lambda)
                           (equal (pseudo-term-kind pat) :fncall)))))
    :returns (mv ok (new-alist pseudo-term-subst-p))
    :verify-guards nil
    (b* ((x (pseudo-term-fix x))
         (alist (pseudo-term-subst-fix alist)))
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
                    (termlist-unify-strict pat.args x.args alist)
                  (mv nil alist))
                :otherwise (mv nil alist)))))
  (define termlist-unify-strict ((pat pseudo-term-listp)
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
          (b* (((mv ok alist) (term-unify-strict (car pat) (car x) alist))
               ((unless ok) (mv nil alist)))
            (termlist-unify-strict (cdr pat) (cdr x) alist))))))

  ///
  (verify-guards term-unify-strict)
  
  (fty::deffixequiv-mutual term-unify-strict)

  (defund-nx term-unify-strict-ok (pat x alist)
    (mv-nth 0 (term-unify-strict pat x alist)))

  (local (in-theory (enable term-unify-strict-ok)))

  (defthm term-unify-strict-ok-when-ok
    (implies (term-unify-strict-ok pat x alist)
             (mv-nth 0 (term-unify-strict pat x alist)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defund-nx termlist-unify-strict-ok (pat x alist)
    (mv-nth 0 (termlist-unify-strict pat x alist)))

  (local (in-theory (enable termlist-unify-strict-ok)))

  (defthm termlist-unify-strict-ok-when-ok
    (implies (termlist-unify-strict-ok pat x alist)
             (mv-nth 0 (termlist-unify-strict pat x alist)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defret-mutual <fn>-preserves-pairs
    (defret <fn>-preserves-pairs
      (implies (and (hons-assoc-equal k (pseudo-term-subst-fix alist)) ok)
               (equal (hons-assoc-equal k new-alist)
                      (hons-assoc-equal k (pseudo-term-subst-fix alist))))
      :hints ('(:expand (<call>)))
      :fn term-unify-strict)

    (defret <fn>-preserves-pairs
      (implies (and (hons-assoc-equal k (pseudo-term-subst-fix alist)) ok)
               (equal (hons-assoc-equal k new-alist)
                      (hons-assoc-equal k (pseudo-term-subst-fix alist))))
      :hints ('(:expand (<call>)))      
      :fn termlist-unify-strict))

  (defret-mutual <fn>-preserves-pairs
    (defret <fn>-binds-pat-vars
      (implies (and (member k (term-vars pat)) ok)
               (hons-assoc-equal k new-alist))
      :hints ('(:expand (<call>
                         (term-vars pat))))
      :fn term-unify-strict)

    (defret <fn>-binds-pat-vars
      (implies (and (member k (termlist-vars pat)) ok)
               (hons-assoc-equal k new-alist))
      :hints ('(:expand (<call>
                         (termlist-vars pat))))
      :fn termlist-unify-strict))

  (local (defthm not-member-when-subsetp-and-hons-assoc
           (implies (and (not (hons-assoc-equal k a))
                         (subsetp x (alist-keys (pseudo-term-subst-fix a))))
                    (not (member k x)))))

  (defret alist-keys-subsetp-of-<fn>
    (implies ok
             (subsetp (alist-keys (pseudo-term-subst-fix alist))
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))
    :fn term-unify-strict)

  (defret alist-keys-subsetp-of-<fn>
    (implies ok
             (subsetp (alist-keys (pseudo-term-subst-fix alist))
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))
    :fn termlist-unify-strict)

  (defret term-vars-subsetp-of-<fn>
    (implies ok
             (subsetp (term-vars pat)
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))
    :fn term-unify-strict)

  (defret termlist-vars-subsetp-of-<fn>
    (implies ok
             (subsetp (termlist-vars pat)
                      (alist-keys new-alist)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))
    :fn termlist-unify-strict)

  (defret-mutual <fn>-preserves-term-subst-strict
    (defret <fn>-preserves-term-subst-strict
      (implies (subsetp (term-vars y) (alist-keys (pseudo-term-subst-fix alist)))
               (equal (term-subst-strict y new-alist)
                      (term-subst-strict y alist)))
      :hints ('(:expand ((term-vars x)
                         <call>)))
      :fn term-unify-strict)
    (defret <fn>-preserves-term-subst-strict
      (implies (subsetp (term-vars y) (alist-keys (pseudo-term-subst-fix alist)))
               (equal (term-subst-strict y new-alist)
                      (term-subst-strict y alist)))
      :hints ('(:expand ((termlist-vars x)
                         <call>)))
      :fn termlist-unify-strict))


  (defret-mutual <fn>-preserves-termlist-subst-strict
    (defret <fn>-preserves-termlist-subst-strict
      (implies (subsetp (termlist-vars y) (alist-keys (pseudo-term-subst-fix alist)))
               (equal (termlist-subst-strict y new-alist)
                      (termlist-subst-strict y alist)))
      :hints ('(:expand ((term-vars x)
                         <call>)))
      :fn term-unify-strict)
    (defret <fn>-preserves-termlist-subst-strict
      (implies (subsetp (termlist-vars y) (alist-keys (pseudo-term-subst-fix alist)))
               (equal (termlist-subst-strict y new-alist)
                      (termlist-subst-strict y alist)))
      :hints ('(:expand ((termlist-vars x)
                         <call>)))
      :fn termlist-unify-strict))


  (local (defthm pseudo-term-fix-when-pseudo-term-quote
           (implies (pseudo-term-case x :quote)
                    (equal (pseudo-term-fix x)
                           (pseudo-term-quote (pseudo-term-quote->val x))))))
  (local (in-theory (disable acl2::pseudo-term-quote-of-accessors)))

  (defret-mutual <fn>-reversible
    (defret <fn>-reversible
      (implies ok
               (equal (term-subst-strict pat new-alist)
                      (pseudo-term-fix x)))
      :hints ('(:expand (<call>
                         (:free (alist) (term-subst-strict pat alist))))
              (and stable-under-simplificationp
                   '(:in-theory (enable acl2::pseudo-term-fix-when-pseudo-term-null))))
      :fn term-unify-strict)
    (defret <fn>-reversible
      (implies ok
               (equal (termlist-subst-strict pat new-alist)
                      (pseudo-term-list-fix x)))
      :hints ('(:expand (<call>
                         (:free (alist) (termlist-subst-strict pat alist))))
              (and stable-under-simplificationp
                   '(:expand ((pseudo-term-list-fix x)))))
      :fn termlist-unify-strict))

  (local (in-theory (enable equal-of-pseudo-term-call
                            equal-of-pseudo-term-fncall
                            equal-of-pseudo-term-lambda
                            equal-of-pseudo-term-quote
                            equal-of-pseudo-term-lambda->fn
                            acl2::pseudo-term-fix-when-pseudo-term-null)))

  (local (defthm not-equal-by-len
           (implies (not (equal (len x) (len y)))
                    (not (equal x y)))))

  (defret-mutual <fn>-reversible-iff
    (defret <fn>-reversible-iff
      (iff ok
           (equal (term-subst-strict pat new-alist)
                  (pseudo-term-fix x)))
      :hints ('(:expand (<call>
                         (:free (alist) (term-subst-strict pat alist))))
              (and stable-under-simplificationp
                   '(:cases ((pseudo-term-case pat :fncall))))
              (and stable-under-simplificationp
                   '(:cases ((equal (len (pseudo-term-call->args x))
                                    (len (pseudo-term-call->args pat)))))))
      :fn term-unify-strict)
    (defret <fn>-reversible-iff
      (iff ok
           (equal (termlist-subst-strict pat new-alist)
                  (pseudo-term-list-fix x)))
      :hints ('(:expand (<call>
                         (:free (alist) (termlist-subst-strict pat alist))))
              (and stable-under-simplificationp
                   '(:expand ((pseudo-term-list-fix x)))))
      :fn termlist-unify-strict))

  (in-theory (disable term-unify-strict-reversible
                      termlist-unify-strict-reversible))

  (defret <fn>-reversible-iff-rw
    (implies (acl2::rewriting-negative-literal
              `(mv-nth '0 (term-unify-strict ,pat ,x ,alist)))
             (iff ok
                  (and (term-unify-strict-ok pat x alist)
                       (equal (term-subst-strict pat new-alist)
                              (pseudo-term-fix x)))))
    :fn term-unify-strict)

  (defret <fn>-reversible-iff-rw
    (implies (acl2::rewriting-negative-literal
              `(mv-nth '0 (termlist-unify-strict ,pat ,x ,alist)))
             (iff ok
                  (and (termlist-unify-strict-ok pat x alist)
                       (equal (termlist-subst-strict pat new-alist)
                              (pseudo-term-list-fix x)))))
    :fn termlist-unify-strict)

  (in-theory (disable term-unify-strict-reversible-iff
                      termlist-unify-strict-reversible-iff))


  (fty::deffixequiv-mutual term-unify-strict))
