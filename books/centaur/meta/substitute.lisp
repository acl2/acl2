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
(include-book "term-vars")
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(defines term-subst
  :flag-local nil
  (define term-subst ((x pseudo-termp)
                      (a pseudo-term-subst-p))
    :returns (new-x pseudo-termp)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :const (pseudo-term-fix x)
      :var (let ((look (assoc-eq x.name (pseudo-term-subst-fix a))))
             (if look (cdr look) (pseudo-term-fix x)))
      :call (pseudo-term-call x.fn (termlist-subst x.args a))))
  (define termlist-subst ((x pseudo-term-listp)
                          (a pseudo-term-subst-p))
    :returns (new-x pseudo-term-listp)
    :measure (pseudo-term-list-count x)
    (if (Atom x)
        nil
      (cons (term-subst (car x) a)
            (termlist-subst (cdr x) a))))
  ///
  (defthm len-of-termlist-subst
    (equal (len (termlist-subst x a))
           (len x)))

  (verify-guards term-subst)

  (local (defthm assoc-of-append
           (implies k
                    (equal (assoc k (append a b))
                           (or (assoc k a) (assoc k b))))))

  (defret-mutual base-ev-of-term-subst
    (defret base-ev-of-term-subst
      (equal (base-ev (term-subst x a) env)
             (base-ev x (append (base-ev-alist a env) env)))
      :hints ('(:expand (<call>)
                :in-theory (enable acl2::base-ev-when-pseudo-term-call
                                   acl2::base-ev-of-pseudo-term-call)))
      :fn term-subst)
    (defret base-ev-list-of-termlist-subst
      (equal (base-ev-list (termlist-subst x a) env)
             (base-ev-list x (append (base-ev-alist a env) env)))
      :hints ('(:expand (<call>)))
      :fn termlist-subst))

  
  (defret-mutual acons-non-var-preserves-<fn>
    (defret acons-non-var-preserves-<fn>
      (implies (not (member k (term-vars x)))
               (equal (term-subst x (cons (cons k v) a))
                      new-x))
      :hints ('(:expand ((term-vars x)
                         (:free (a) <call>))))
      :fn term-subst)
    (defret acons-non-var-preserves-<fn>
      (implies (not (member k (termlist-vars x)))
               (equal (termlist-subst x (cons (cons k v) a))
                      new-x))
      :hints ('(:expand ((termlist-vars x)
                         (:free (a) <call>))))
      :fn termlist-subst))

  (fty::deffixequiv-mutual term-subst))



(defines term-subst-strict
  :flag-local nil
  (define term-subst-strict ((x pseudo-termp)
                             (a pseudo-term-subst-p))
    :returns (new-x pseudo-termp)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :const (pseudo-term-fix x)
      :var (cdr (assoc-eq x.name (pseudo-term-subst-fix a)))
      :call (pseudo-term-call x.fn (termlist-subst-strict x.args a))))
  (define termlist-subst-strict ((x pseudo-term-listp)
                          (a pseudo-term-subst-p))
    :returns (new-x pseudo-term-listp)
    :measure (pseudo-term-list-count x)
    (if (Atom x)
        nil
      (cons (term-subst-strict (car x) a)
            (termlist-subst-strict (cdr x) a))))
  ///
  (defthm len-of-termlist-subst-strict
    (equal (len (termlist-subst-strict x a))
           (len x)))

  (verify-guards term-subst-strict)

  (defret-mutual base-ev-of-term-subst-strict
    (defret base-ev-of-term-subst-strict
      (equal (base-ev (term-subst-strict x a) env)
             (base-ev x (base-ev-alist a env)))
      :hints ('(:expand (<call>)
                :in-theory (enable acl2::base-ev-when-pseudo-term-call
                                   acl2::base-ev-of-pseudo-term-call)))
      :fn term-subst-strict)
    (defret base-ev-list-of-termlist-subst-strict
      (equal (base-ev-list (termlist-subst-strict x a) env)
             (base-ev-list x (base-ev-alist a env)))
      :hints ('(:expand (<call>)))
      :fn termlist-subst-strict))

  (defret-mutual acons-non-var-preserves-<fn>
    (defret acons-non-var-preserves-<fn>
      (implies (not (member k (term-vars x)))
               (equal (term-subst-strict x (cons (cons k v) a))
                      new-x))
      :hints ('(:expand ((term-vars x)
                         (:free (a) <call>))))
      :fn term-subst-strict)
    (defret acons-non-var-preserves-<fn>
      (implies (not (member k (termlist-vars x)))
               (equal (termlist-subst-strict x (cons (cons k v) a))
                      new-x))
      :hints ('(:expand ((termlist-vars x)
                         (:free (a) <call>))))
      :fn termlist-subst-strict))

  (fty::deffixequiv-mutual term-subst-strict))

