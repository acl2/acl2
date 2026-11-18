; FGL - A Symbolic Simulation Framework for ACL2
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

; Object-level execution and analysis for branch merging.

(in-package "FGL")

(include-book "contexts")
(local (std::add-default-post-define-hook :fix))
(std::make-returnspec-config :hints-sub-returnnames t)
(local (in-theory (e/d (acl2::kwote-lst-redef) (kwote-lst))))

(fty::deflist pseudo-fnsymlist :elt-type pseudo-fnsym :true-listp t :elementp-of-nil t)

(define fncall-try-concrete-eval ((fn pseudo-fnsym-p)
                                  (args fgl-arglist-p)
                                  (dont-concrete-exec)
                                  unequiv
                                  state)
  :returns (mv ok (ans fgl-object-p))
  (b* (((when (or dont-concrete-exec
                  (not (fgl-arglist-all-boundp args))
                  (not (g-concretelist-p (fgl-arglist->objects args)))))
        (mv nil nil))
       (args (fgl-arglist->objects args))
       ((mv err ans)
        (if unequiv
            ;; allow attachments and program mode when unequiv
            (acl2::magic-ev-fncall (pseudo-fnsym-fix fn) (g-concretelist-vals args) state t t)
          (acl2::magic-ev-fncall-logic (pseudo-fnsym-fix fn) (g-concretelist-vals args) state))))
    (mv (not err) (g-concrete ans)))
  ///
  (defret fgl-object-bfrlist-of-<fn>
    (equal (fgl-object-bfrlist ans) nil))

  (local (defthm fgl-objectlist-eval-when-concretelist-p
           (implies (g-concretelist-p x)
                    (equal (fgl-objectlist-eval x env)
                           (g-concretelist-vals x)))
           :hints(("Goal" :in-theory (enable fgl-objectlist-eval fgl-object-eval g-concretelist-p
                                             g-concretelist-vals)))))

  (defret eval-of-<fn>
    (implies (and ok
                  (fgl-ev-meta-extract-global-facts :state st)
                  (equal (w st) (w state))
                  (not unequiv))
             (equal (fgl-object-eval ans env)
                    (fgl-ev (cons (pseudo-fnsym-fix fn) (kwote-lst (fgl-objectlist-eval
                                                                    (fgl-arglist->objects args)
                                                                    env)))
                            nil))))

  (defret fgl-arglist-unbound-when-<fn>
    (implies ok
             (not (fgl-arglist-unbounds args))))

  (defret fgl-ev-context-fix-of-eval-<fn>
    :pre-bind ((unequiv (member-equal 'unequiv contexts)))
    (implies (and ok
                  (fgl-ev-meta-extract-global-facts :state st)
                  (equal (w st) (w state))
                  (equiv-contextsp contexts))
             (equal (fgl-ev-context-fix contexts
                                        (fgl-object-eval ans env))
                    (fgl-ev-context-fix contexts
                                        (fgl-ev (cons (pseudo-fnsym-fix fn)
                                                      (kwote-lst (fgl-objectlist-eval
                                                                  (fgl-arglist->objects args)
                                                                  env)))
                                                nil))))))

(define fgl-apply-match-not ((x fgl-object-p))
  :guard (fgl-object-case x :g-apply)
  :returns (mv ok
               (negated-arg fgl-object-p))
  (b* (((unless (mbt (fgl-object-case x :g-apply))) (mv nil nil))
       ((g-apply x))
       (fn x.fn)
       (args x.args)
       ((when (eq fn 'not))
        (cond ((eql (len args) 1)
               (mv t (fgl-object-fix (car args))))
              (t (mv nil nil))))
       ((when (eq fn 'equal))
        (b* (((unless (eql (len args) 2))
              (mv nil nil))
             ((list arg1 arg2) args)
             ((when (fgl-object-case arg1
                      :g-concrete (eq arg1.val nil)
                      :otherwise nil))
              (mv t (fgl-object-fix arg2)))
             ((when (fgl-object-case arg2
                      :g-concrete (eq arg2.val nil)
                      :otherwise nil))
              (mv t (fgl-object-fix arg1))))
          (mv nil nil))))
    (mv nil nil))
  ///


  (defret fgl-apply-match-not-correct
    (implies ok
             (iff (fgl-object-eval negated-arg env logicman)
                  (not (fgl-object-eval x env logicman))))
    :hints(("Goal" :expand ((fgl-objectlist-eval (g-apply->args x) env)
                            (fgl-objectlist-eval (cdr (g-apply->args x)) env)
                            (fgl-objectlist-eval (cddr (g-apply->args x)) env))
            :in-theory (enable fgl-apply))))

  (defret fgl-object-count-of-g-apply-match-not
    (implies ok
             (< (fgl-object-count negated-arg) (fgl-object-count x)))
    :hints(("Goal" :expand ((fgl-object-count x)
                            (fgl-objectlist-count (g-apply->args x))
                            (fgl-objectlist-count (cdr (g-apply->args x)))
                            (fgl-objectlist-count (cddr (g-apply->args x))))))
    :rule-classes :linear)

  (defret bfrlist-of-fgl-apply-match-not
    (implies (not (member v (fgl-object-bfrlist x)))
             (not (member v (fgl-object-bfrlist negated-arg))))))

(define fgl-fncall-object->fns ((x fgl-object-p))
  :returns (fn pseudo-fnsymlist-p) ;; nil if didn't match
  (fgl-object-case x
    :g-boolean '(bool)
    :g-integer '(int)
    :g-concrete (cond ((consp x.val) '(cons concrete))
                      ((booleanp x.val) '(bool concrete))
                      ((integerp x.val) '(int concrete))
                      (t '(concrete)))
    :g-apply (list x.fn)
    :g-cons '(cons)
    :g-ite '(if)
    :otherwise nil))

(defthm fgl-ev-list-of-kwote-lst
  (equal (fgl-ev-list (kwote-lst x) a)
         (true-list-fix x))
  :hints (("goal" :induct (len x))))

(defthm not-quote-when-pseudo-fnsym-p
  (implies (pseudo-fnsym-p x)
           (not (equal x 'quote))))

(define fgl-object-recognize-merge-fncall ((x fgl-object-p))
  ;; Note: This is used when we want to merge two calls of the same function,
  ;; e.g.  (if test (foo x y) (foo w z)).  We don't want to match a g-boolean
  ;; to (bool x), for example, because that would lead to an infinite loop where we
  ;; match (if test (g-boolean b) (g-boolean c)) as
  ;; (if test (bool (g-boolean b)) (bool (g-boolean c)))
  ;; then merge the args, i.e. (list (g-boolean b)) (list (g-boolean c))
  ;; in which when we merge the first arg we get back to
  ;; (if test (g-boolean b) (g-boolean c)) and get stuck in an infinite loop.
  :returns (mv (fn pseudo-fnsym-p :rule-classes (:rewrite (:type-prescription :typed-term fn)))
               (args fgl-objectlist-p))
  (fgl-object-case x
    ;; :g-boolean (mv 'bool (list (fgl-object-fix x)))
    ;; :g-integer (mv 'int (list (fgl-object-fix x)))
    ;; :g-concrete (mv 'concrete (list (fgl-object-fix x)))
    :g-apply (mv x.fn x.args)
    :g-cons (mv 'cons (list x.car x.cdr))
    :g-concrete (if (consp x.val)
                    (mv 'cons (list (g-concrete (car x.val))
                                    (g-concrete (cdr x.val))))
                  (mv nil nil))
    :otherwise (mv nil nil))
  ///

  (defret eval-when-fgl-object-recognize-merge-fncall2
    (implies (and fn
                  (equal fn1 fn))
             (equal (fgl-ev (cons fn1
                                  (kwote-lst (fgl-objectlist-eval args env)))
                            a)
                    (fgl-object-eval x env)))
    :hints(("Goal" :in-theory (enable fgl-apply fgl-objectlist-eval
                                      fgl-ev-of-fncall-args))))

  (defret bfr-listp-fgl-objectlist-bfrlist-of-<fn>
    (implies (bfr-listp (fgl-object-bfrlist x))
             (bfr-listp (fgl-objectlist-bfrlist args)))
    :hints (("goal" :Expand ((fgl-object-bfrlist x))))))

(define fgl-objectlist-find-ite ((x fgl-objectlist-p))
  :returns (ite fgl-object-p)
  (if (atom x)
      nil
    (if (fgl-object-case (car x) :g-ite)
        (fgl-object-fix (car x))
      (fgl-objectlist-find-ite (cdr x))))
  ///
  (defret fgl-object-kind-of-<fn>
    (iff (equal (fgl-object-kind ite) :g-ite)
         ite))

  (defret bfr-listp-of-fgl-objectlist-find-ite
    (implies (bfr-listp (fgl-objectlist-bfrlist x))
             (bfr-listp (fgl-object-bfrlist ite)))))

(define fgl-objectlist-split ((test fgl-object-p)
                              (x fgl-objectlist-p))
  :returns (mv (then fgl-objectlist-p)
               (else fgl-objectlist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv rest-then rest-else) (fgl-objectlist-split test (cdr x)))
       (x1 (fgl-object-fix (car x)))
       ((when (and (fgl-object-case x1 :g-ite)
                   (equal (g-ite->test x1) (fgl-object-fix test))))
        (mv (cons (g-ite->then x1) rest-then)
            (cons (g-ite->else x1) rest-else))))
    (mv (cons x1 rest-then)
        (cons x1 rest-else)))
  ///
  (local (defthm fgl-objectlist-eval-of-atom
           (implies (not (Consp x))
                    (equal (fgl-objectlist-eval x env logicman) nil))
           :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (defret fgl-objectlist-split-correct-true
    (implies (fgl-object-eval test env)
             (equal (fgl-objectlist-eval then env)
                    (fgl-objectlist-eval x env))))

  (defret fgl-objectlist-split-correct-false
    (implies (not (fgl-object-eval test env))
             (equal (fgl-objectlist-eval else env)
                    (fgl-objectlist-eval x env))))

  (defret fgl-objectlist-count-of-fgl-objectlist-split-weak
    (and (<= (fgl-objectlist-count then) (fgl-objectlist-count x))
         (<= (fgl-objectlist-count else) (fgl-objectlist-count x)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-count)))
    :rule-classes :linear)

  (defret fgl-objectlist-count-of-fgl-objectlist-split-strong
    :pre-bind ((ite (fgl-objectlist-find-ite x))
               (test (g-ite->test ite)))
    (implies ite
             (and (< (fgl-objectlist-count then) (fgl-objectlist-count x))
                  (< (fgl-objectlist-count else) (fgl-objectlist-count x))))
    :hints(("Goal" :in-theory (enable fgl-objectlist-find-ite
                                      fgl-objectlist-count)))
    :rule-classes :linear)

  (defret bfr-listp-of-fgl-objectlist-split
    (implies (bfr-listp (fgl-objectlist-bfrlist x))
             (and (bfr-listp (fgl-objectlist-bfrlist then))
                  (bfr-listp (fgl-objectlist-bfrlist else))))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))
