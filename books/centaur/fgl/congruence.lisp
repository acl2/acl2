; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "FGL")

(include-book "contexts")
(include-book "congruence-rules")

(local (std::add-default-post-define-hook :fix))

(std::deflist fgl-ev-congruence-rulelist-correct-p (x)
  :guard (congruence-rulelist-p x)
  (fgl-ev-congruence-rule-correct-p x)
  ///
  (fty::deffixcong congruence-rulelist-equiv equal (fgl-ev-congruence-rulelist-correct-p x) x))

(local (in-theory (disable w)))

(defret fgl-ev-congruence-rule-correct-p-of-<fn>
  (implies (and (fgl-ev-meta-extract-global-facts)
                (equal w (w state))
                (not errmsg))
           (fgl-ev-congruence-rule-correct-p rule))
  :hints(("Goal" :in-theory (enable <fn>
                                    fgl-ev-meta-extract-formula-theoremp)))
  :fn congruence-rule-from-rune)

(defret fgl-ev-congruence-rulelist-correct-p-of-<fn>
  (implies (and (fgl-ev-meta-extract-global-facts)
                (equal w (w state)))
           (fgl-ev-congruence-rulelist-correct-p rules))
  :hints(("Goal" :in-theory (enable <fn>)))
  :fn congruence-rules-from-runes)

(local (defthm equiv-argcontexts-p-when-equiv-contextslist-p
         (implies (equiv-contextslist-p x)
                  (equiv-argcontexts-p x))
         :hints(("Goal" :in-theory (enable equiv-argcontexts-p)))))


(local (defthm len-of-join-equiv-contextslists
         (equal (len (cmr::join-equiv-contextslists ctx1 ctx2))
                (max (len ctx1) (len ctx2)))
         :hints(("Goal" :in-theory (enable cmr::join-equiv-contextslists)))))

(define apply-congruence-rule ((rule cmr::congruence-rule-p)
                               (fn pseudo-fnsym-p)
                               (ctx equiv-contextsp)
                               (arity natp)
                               (arg-ctxs equiv-contextslist-p))
  :returns (new-arg-ctxs equiv-contextslist-p)
  (b* (((cmr::congruence-rule rule))
       (arg-ctxs (equiv-contextslist-fix arg-ctxs))
       ((unless (or (eq rule.equiv-req 'equal)
                    (member rule.equiv-req (equiv-contexts-fix ctx))))
        arg-ctxs)
       ((unless (eq rule.fn (pseudo-fnsym-fix fn))) arg-ctxs)
       ((unless (eql rule.arity (lnfix arity))) arg-ctxs))
    
    (cmr::join-equiv-contextslists rule.arg-contexts arg-ctxs))
  ///
  (local (defthm equal-of-pseudo-fnsym-fix
           (implies (equal x (pseudo-fnsym-fix y))
                    (pseudo-fnsym-equiv x y))
           :rule-classes :forward-chaining))

  (local (defthm fgl-ev-congruence-correct-p-of-singleton
           (implies (and (fgl-ev-congruence-correct-p (list equiv) fn arg-ctxs arity)
                         (member (pseudo-fnsym-fix equiv) (equiv-contexts-fix ctx)))
                    (fgl-ev-congruence-correct-p ctx fn arg-ctxs arity))
           :hints((and stable-under-simplificationp
                       `(:expand (,(car (last clause)))
                         :use ((:instance fgl-ev-congruence-correct-p-necc
                                (ctx (list equiv))
                                (args1 (mv-nth 0 (fgl-ev-congruence-correct-p-witness . ,(cdar (last clause)))))
                                (args2 (mv-nth 1 (fgl-ev-congruence-correct-p-witness . ,(cdar (last clause)))))))
                         :in-theory (e/d (fgl-ev-context-equiv-by-singleton)
                                         (fgl-ev-of-pseudo-term-fncall
                                          fgl-ev-when-pseudo-term-fncall
                                          fgl-ev-congruence-correct-p-necc)))))))

  (local (defthm fgl-ev-congruence-correct-p-of-equal
           (implies (fgl-ev-congruence-correct-p '(equal) fn arg-ctxs arity)
                    (fgl-ev-congruence-correct-p ctx fn arg-ctxs arity))
           :hints((and stable-under-simplificationp
                       `(:expand (,(car (last clause)))
                         :use ((:instance fgl-ev-congruence-correct-p-necc
                                (ctx '(equal))
                                (args1 (mv-nth 0 (fgl-ev-congruence-correct-p-witness . ,(cdar (last clause)))))
                                (args2 (mv-nth 1 (fgl-ev-congruence-correct-p-witness . ,(cdar (last clause)))))))
                         :in-theory (e/d (fgl-ev-context-equiv-by-singleton)
                                         (fgl-ev-of-pseudo-term-fncall
                                          fgl-ev-when-pseudo-term-fncall
                                          fgl-ev-congruence-correct-p-necc)))))))

  (defret fgl-ev-congruence-correct-p-of-<fn>
    (implies (and (fgl-ev-congruence-rule-correct-p rule)
                  (fgl-ev-congruence-correct-p ctx fn arg-ctxs arity)
                  (<= (len arg-ctxs) (nfix arity)))
             (fgl-ev-congruence-correct-p ctx fn new-arg-ctxs arity))
    :hints(("Goal" :in-theory (enable fgl-ev-congruence-rule-correct-p))
           (and stable-under-simplificationp
                '(:cases ((< (len arg-ctxs) (len (cmr::congruence-rule->arg-contexts rule))))))))

  (defret len-contexts-of-<fn>
    (implies (and (<= (len arg-ctxs) (nfix arity))
                  (fgl-ev-congruence-rule-correct-p rule))
             (<= (len new-arg-ctxs) (nfix arity)))
    :hints(("Goal" :in-theory (enable fgl-ev-congruence-rule-correct-p)))
    :rule-classes :linear))

(define apply-congruence-rules ((rules congruence-rulelist-p)
                                (fn pseudo-fnsym-p)
                                (ctx equiv-contextsp)
                                (arity natp)
                                (arg-ctxs equiv-contextslist-p))
  :returns (new-arg-ctxs equiv-contextslist-p)
  (if (atom rules)
      (equiv-contextslist-fix arg-ctxs)
    (apply-congruence-rules
     (cdr rules) fn ctx arity
     (apply-congruence-rule (car rules) fn ctx arity arg-ctxs)))
  ///
  (defret len-contexts-of-<fn>
    (implies (and (fgl-ev-congruence-rulelist-correct-p rules)
                  (<= (len arg-ctxs) (nfix arity)))
             (<= (len new-arg-ctxs) (nfix arity)))
    :hints(("Goal" :in-theory (enable fgl-ev-congruence-rulelist-correct-p
                                      fgl-ev-congruence-rule-correct-p)))
    :rule-classes :linear)

  (defret fgl-ev-congruence-correct-p-of-<fn>
    (implies (and (fgl-ev-congruence-rulelist-correct-p rules)
                  (fgl-ev-congruence-correct-p ctx fn arg-ctxs arity)
                  (<= (len arg-ctxs) (nfix arity)))
             (fgl-ev-congruence-correct-p ctx fn new-arg-ctxs arity))
    :hints(("Goal" :in-theory (enable fgl-ev-congruence-rulelist-correct-p)))))

(local (defthm cdr-last-when-true-listp
         (implies (true-listp x)
                  (equal (cdr (last x)) nil))))


(define fgl-ev-congruence-rule-table-correct-p ((x congruence-rule-table-p))
  (if (atom x)
      t
    (and (if (mbt (and (consp (car x))
                       (pseudo-fnsym-p (caar x))))
             (fgl-ev-congruence-rulelist-correct-p (cdar x))
           t)
         (fgl-ev-congruence-rule-table-correct-p (cdr x))))
  ///
  (defthm fgl-ev-congruence-rulelist-correct-p-of-lookup
    (implies (and (fgl-ev-congruence-rule-table-correct-p x)
                  (pseudo-fnsym-p k))
             (fgl-ev-congruence-rulelist-correct-p (cdr (hons-assoc-equal k x)))))

  (defthm fgl-ev-congruence-rule-table-correct-p-of-fast-alist-fork
    (implies (and (fgl-ev-congruence-rule-table-correct-p a)
                  (fgl-ev-congruence-rule-table-correct-p b))
             (fgl-ev-congruence-rule-table-correct-p (fast-alist-fork a b))))

  (local (in-theory (enable congruence-rule-table-fix))))

(define congruence-rulelist-to-table ((x congruence-rulelist-p)
                                      (acc congruence-rule-table-p))
  :returns (table congruence-rule-table-p)
  (b* (((when (atom x)) (fast-alist-clean (congruence-rule-table-fix acc)))
       ((cmr::congruence-rule x1) (car x))
       (acc (congruence-rule-table-fix acc))
       (acc (hons-acons x1.fn (cons (cmr::congruence-rule-fix x1)
                                    (cdr (hons-get x1.fn acc)))
                        acc)))
    (congruence-rulelist-to-table (cdr x) acc))
  ///
  (defret fgl-ev-congruence-rule-table-correct-p-of-<fn>
    (implies (and (fgl-ev-congruence-rulelist-correct-p x)
                  (fgl-ev-congruence-rule-table-correct-p acc))
             (fgl-ev-congruence-rule-table-correct-p table))
    :hints (("goal" :induct <call>
             :expand ((:free (a b) (fgl-ev-congruence-rule-table-correct-p (cons a b)))
                      <call>))))

  (local (in-theory (enable congruence-rulelist-fix))))




(define fgl-congruence-rules (runes (w plist-worldp))
  :returns (table congruence-rule-table-p)
  (b* (((unless (fgl-congruence-runelist-p runes))
        (er hard? 'fgl-congruence-rules
            "Rune list did not satisfy fgl-congruence-runelist-p"))
       ((mv errmsg rules) (congruence-rules-from-runes runes w))
       (- (and errmsg
               (er hard? 'fgl-congruence-rules
                   "Not all congruence runes could be parsed into valid rules: ~@0" errmsg))))
    (congruence-rulelist-to-table rules nil))
  ///
  (defret fgl-ev-congruence-rule-table-correct-p-of-<fn>
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (fgl-ev-congruence-rule-table-correct-p table)))

  (memoize 'fgl-congruence-rules))


(defsection fgl-id-congruence-rule-correct
  (defun-sk fgl-id-congruence-rule-correct (rule)
    (forall (args alt)
            (b* (((fgl-id-congruence-rule rule))
                 (val (fgl-ev (cons rule.fn (kwote-lst args)) nil))
                 (alt-val (fgl-ev (cons rule.fn (kwote-lst (update-nth rule.id-index alt args))) nil)))
              (implies (and (equal (len args) rule.arity)
                            (not (equal val (nth rule.id-index args))))
                       (equal (equal val alt-val) t))))
    :rewrite :direct)

  (in-theory (disable fgl-id-congruence-rule-correct
                      fgl-id-congruence-rule-correct-necc))

  (fty::deffixcong fgl-id-congruence-rule-equiv equal (fgl-id-congruence-rule-correct rule) rule
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'fgl-id-congruence-rule-correct clause))
                        (arg (cadr lit))
                        (other (if (eq arg 'rule) '(fgl-id-congruence-rule-fix rule) 'rule)))
                   `(:expand (,lit)
                     :use ((:instance fgl-id-congruence-rule-correct-necc
                            (rule ,other)
                            (args (mv-nth 0 (fgl-id-congruence-rule-correct-witness ,arg)))
                            (alt (mv-nth 1 (fgl-id-congruence-rule-correct-witness ,arg)))))))))))

(defsection parse-id-congruence-rule-correct
  (local (in-theory (disable cmr::pseudo-term-var-list->names-when-pseudo-term-listp)))

  (local (defthm nonnil-when-pseudo-term-var
           (implies (pseudo-term-case x :var)
                    x)
           :rule-classes :forward-chaining))
  
  (local (defun lookup-keys (x a)
           (if (atom x)
               nil
             (cons (cdr (assoc (car x) a))
                   (lookup-keys (cdr x) a)))))

  (local (defthm lookup-keys-in-pairlis$
           (implies (no-duplicatesp keys)
                    (equal (lookup-keys keys (pairlis$ keys vals))
                           (take (len keys) vals)))
           :hints(("Goal" :in-theory (enable no-duplicatesp pairlis$ take)))))
  
  (local (defthm fgl-ev-list-of-pseudo-term-var-list
           (implies (cmr::pseudo-term-var-listp x)
                    (equal (fgl-ev-list x a)
                           (lookup-keys (cmr::pseudo-term-var-list->names x) a)))
           :hints(("Goal" :in-theory (enable lookup-keys
                                             cmr::pseudo-term-var-list->names
                                             cmr::pseudo-term-var-listp)))))

  (local (defthm assoc-member-in-pairlis$
           (implies (member-equal k keys)
                    (equal (cdr (assoc-equal k (pairlis$ keys vals)))
                           (nth (acl2::index-of k keys) vals)))
           :hints(("Goal" :in-theory (enable acl2::index-of pairlis$ assoc-equal)))))

  (local (defthm kwote-lst-of-true-list-fix
           (equal (kwote-lst (true-list-fix x)) (kwote-lst x))
           :hints(("Goal" :in-theory (enable kwote-lst)))))

  (local (defthm assoc-pairlis$-when-not-member
           (implies (case-split (not (member-equal k keys)))
                    (equal (assoc-equal k (pairlis$ keys vals)) nil))
           :hints(("Goal" :in-theory (enable pairlis$ assoc-equal)))))

  (local (defthm nth-of-fgl-ev-list
           (equal (nth n (fgl-ev-list x a))
                  (fgl-ev (nth n x) a))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (in-theory (disable len nth)))

  (local (defthm len-of-pseudo-term-var-list->names
           (equal (len (cmr::pseudo-term-var-list->names x))
                  (len x))
           :hints(("Goal" :in-theory (enable len cmr::pseudo-term-var-list->names)))))

  (local (defthm member-name-of-nth
           (implies (< (nfix n) (len x))
                    (member-equal (pseudo-term-var->name (nth n x))
                                  (cmr::pseudo-term-var-list->names x)))
           :hints(("Goal" :in-theory (enable cmr::pseudo-term-var-list->names nth len)))))

  (local
   (defret parse-simple-id-congruence-arity
     (implies rule
              (equal (len vars)
                     (fgl-id-congruence-rule->arity rule)))
     :hints(("Goal" :in-theory (enable <fn>)))
     :fn parse-simple-id-congruence))

  (local
   (defret parse-simple-id-congruence-arity-greater
     (implies rule
              (b* (((fgl-id-congruence-rule rule)))
                (< rule.id-index rule.arity)))
     :hints(("Goal" :in-theory (enable <fn>)))
     :rule-classes :linear
     :fn parse-simple-id-congruence))

  (local
   (defret parse-simple-id-congruence-no-dups
     (implies rule
              (no-duplicatesp-equal (cmr::pseudo-term-var-list->names vars)))
     :hints(("Goal" :in-theory (enable <fn>)))
     :fn parse-simple-id-congruence))

  (local (defthm equal-of-pseudo-term-var
           (equal (equal (pseudo-term-var x) y)
                  (and (pseudo-termp y)
                       (pseudo-term-case y :var)
                       (Equal (pseudo-term-var->name y) (pseudo-var-fix x))))
           :hints(("Goal" :in-theory (enable pseudo-term-var
                                             pseudo-term-kind
                                             pseudo-term-var->name)))))
  
  (local (defthm nth-of-pseudo-term-var-list->names
           (implies (< (nfix n) (len x))
                    (equal (nth n (cmr::pseudo-term-var-list->names x))
                           (pseudo-term-var->name (nth n x))))
           :hints(("Goal" :in-theory (enable nth len
                                             cmr::pseudo-term-var-list->names)))))

  (local (defthm pseudo-termp-nth
           (implies (pseudo-term-listp x)
                    (pseudo-termp (nth n x)))
           :hints(("Goal" :in-theory (enable pseudo-term-listp nth)))))

  (local (defthm pseudo-term-kind-of-nth-when-pseudo-term-var-listp
           (implies (and (cmr::pseudo-term-var-listp x)
                         (< (nfix n) (len x)))
                    (equal (pseudo-term-kind (nth n x)) :var))
           :hints(("Goal" :in-theory (enable cmr::pseudo-term-var-listp nth len)))))
  
  (local (defthm nth-index-of-pseudo-term-var-list->names
           (implies (and (member-equal k (cmr::pseudo-term-var-list->names x))
                         (pseudo-term-listp x)
                         (cmr::pseudo-term-var-listp x))
                    (equal (nth (acl2::index-of k (cmr::pseudo-term-var-list->names x)) x)
                           (pseudo-term-var k)))
           :hints(("Goal" :use ((:instance acl2::nth-of-index-when-member
                                 (x (cmr::pseudo-term-var-list->names x))))
                   :in-theory (disable acl2::nth-of-index-when-member)))))

  (local (defthm index-of-when-not-member
           (implies (not (member n x))
                    (not (acl2::index-of n x)))))
  (local (defthm index-of-nth-name
           (implies (and (no-duplicatesp-equal (cmr::pseudo-term-var-list->names x))
                         (< (nfix n) (len x)))
                    (equal (acl2::index-of (pseudo-term-var->name (nth n x))
                                           (cmr::pseudo-term-var-list->names x))
                           (nfix n)))
           :hints(("Goal" :in-theory (enable cmr::pseudo-term-var-list->names
                                             acl2::index-of
                                             nth len)))))
                    
  (local
   (defret parse-simple-id-congruence-correct
     (implies (and (fgl-ev x a)
                   rule)
              (b* (((fgl-id-congruence-rule rule)))
                (equal (fgl-ev (cons rule.fn vars) a)
                       (cdr (assoc (pseudo-term-var->name (nth rule.id-index vars)) a)))))
     :hints(("Goal" :in-theory (e/d (<fn>))))
     :fn parse-simple-id-congruence))

  (local
   (defretd parse-simple-disjunction-correct
     (implies ok
              (iff (fgl-ev x a)
                   (or (fgl-ev left a)
                       (fgl-ev right a))))
     :hints(("Goal" :in-theory (enable <fn>)))
     :fn parse-simple-disjunction))

  (local
   (defret parse-id-congruence-equivalence-correct
     (implies (and diff-var
                   (cmr::pseudo-term-var-listp vars)
                   (pseudo-term-listp vars)
                   (fgl-ev x a))
              (b* (((fgl-id-congruence-rule rule)))
                (equal (fgl-ev (cons rule.fn (update-nth rule.id-index diff-var vars)) a)
                       (fgl-ev (cons rule.fn vars) a))))
     :hints(("Goal" :in-theory (e/d (<fn>))))
     :fn parse-id-congruence-equivalence))

  (local (defthmd pseudo-term-var->name-equal
           (implies (and (pseudo-termp x)
                         (pseudo-term-case x :var)
                         (pseudo-termp y)
                         (pseudo-term-case y :var))
                    (iff (equal (pseudo-term-var->name x)
                                (pseudo-term-var->name y))
                         (equal x y)))
           :hints (("goal" :use ((:instance acl2::pseudo-term-var-of-accessors (x x))
                                 (:instance acl2::pseudo-term-var-of-accessors (x y)))
                    :in-theory (disable acl2::pseudo-term-var-of-accessors
                                        equal-of-pseudo-term-var)))))

  (local (defthmd pseudo-term-var->name-member
           (implies (and (pseudo-termp x)
                         (pseudo-term-case x :var)
                         (pseudo-term-listp y)
                         (cmr::pseudo-term-var-listp y))
                    (iff (member-equal (pseudo-term-var->name x)
                                       (cmr::pseudo-term-var-list->names y))
                         (member-equal x y)))
           :hints(("Goal" :in-theory (enable pseudo-term-var->name-equal
                                             cmr::pseudo-term-var-list->names
                                             cmr::pseudo-term-var-listp
                                             pseudo-term-listp)))))
  
  (local (defthm len-of-update-nth
           (equal (len (update-nth n v y))
                  (max (len y) (+ 1 (nfix n))))
           :hints(("Goal" :in-theory (enable len update-nth)))))
  (local (defthm len-of-update-nth-free
           (implies (equal x (update-nth n v y))
                    (equal (len x)
                           (max (len y) (+ 1 (nfix n)))))))
  (local (defthm max-when-less
           (implies (and (< x y)
                         (integerp x) (integerp y))
                    (equal (max y (+ 1 x)) y))))
  (local (in-theory (disable max)))

  (local (defthm member-nth
           (implies (< (nfix n) (len x))
                    (member (nth n x) x))
           :hints(("Goal" :in-theory (enable nth len)))))

  (local
   (defret parse-id-congruence-equivalence-not-same
     (implies (and diff-var
                   (cmr::pseudo-term-var-listp vars)
                   (pseudo-term-listp vars))
              (b* (((fgl-id-congruence-rule rule)))
                (implies (< rule.id-index (len vars))
                         (not (equal (pseudo-term-var->name diff-var)
                                     (pseudo-term-var->name (nth rule.id-index vars)))))))
     :hints(("Goal" :in-theory (e/d (<fn>
                                     pseudo-term-var->name-equal))))
     :fn parse-id-congruence-equivalence))

  (local
   (defret parse-id-congruence-equivalence-not-nenber
     (implies (and diff-var
                   (cmr::pseudo-term-var-listp vars)
                   (pseudo-term-listp vars))
              (b* (((fgl-id-congruence-rule rule)))
                (implies (< rule.id-index (len vars))
                         (not (member-equal (pseudo-term-var->name diff-var)
                                            (cmr::pseudo-term-var-list->names vars))))))
     :hints(("Goal" :in-theory (e/d (<fn>
                                     pseudo-term-var->name-member))))
     :fn parse-id-congruence-equivalence))

  (local (defthm quote-when-pseudo-fnsym-p
           (implies (pseudo-fnsym-p x)
                    (not (equal x 'quote)))))

  (local (defthm lookup-keys-when-cons-non-member
           (implies (not (member-equal k keys))
                    (equal (lookup-keys keys (cons (cons k v) a))
                           (lookup-keys keys a)))
           :hints(("Goal" :in-theory (enable lookup-keys)))))

  (local (defthm pseudo-term-var-listp-of-update-nth
           (implies (and (cmr::pseudo-term-var-listp x)
                         (pseudo-term-case v :var)
                         (< (nfix n) (len x)))
                    (cmr::pseudo-term-var-listp (update-nth n v x)))
           :hints(("Goal" :in-theory (enable update-nth len cmr::pseudo-term-var-listp)))))

  (local (defthm pseudo-term-var-list->names-of-update-nth
           (implies (< (nfix n) (len x))
                    (equal (cmr::pseudo-term-var-list->names (update-nth n v x))
                           (update-nth n (pseudo-term-var->name v) (cmr::pseudo-term-var-list->names x))))
           :hints(("Goal" :in-theory (enable update-nth len cmr::pseudo-term-var-list->names)))))

  (local (defthm lookup-keys-of-update-nth
           (implies (< (nfix n) (len keys))
                    (equal (lookup-keys (update-nth n v keys) a)
                           (update-nth n (cdr (assoc v a)) (lookup-keys keys a))))
           :hints(("Goal" :in-theory (enable update-nth lookup-keys len)))))

  (local (defthm update-nth-of-true-list-fix
           (equal (update-nth n v (true-list-fix x))
                  (true-list-fix (update-nth n v x)))
           :hints(("Goal" :in-theory (enable update-nth)))))
  
  (local (in-theory (disable kwote-lst
                             fgl-ev-list-of-cons)))
  (local
   (defret parse-id-congruence-rule-correct-lemma
     (implies (and rule
                   (fgl-ev-theoremp x))
              (b* (((fgl-id-congruence-rule rule))
                   (val (fgl-ev (cons rule.fn (kwote-lst args)) nil))
                   (alt-val (fgl-ev (cons rule.fn (kwote-lst (update-nth rule.id-index alt args))) nil)))
                (implies (and (equal (len args) rule.arity)
                              (not (equal val (nth rule.id-index args))))
                         (equal alt-val val))))
     :hints((acl2::use-termhint
             (b* (((mv rule ?vars) (parse-simple-id-congruence x))
                  (var-vars (cmr::pseudo-term-var-list->names vars))
                  ((when rule)
                   `(:use ((:instance acl2::mark-clause-is-true (x 'simple))
                           ;; (:instance fgl-ev-theoremp-implies
                           ;;  (a ,(acl2::hq (pairlis$ vars args))))
                           (:instance parse-simple-id-congruence-correct
                            (a ,(acl2::hq (pairlis$ var-vars args)))))
                     :in-theory (e/d (fgl-ev-of-fncall-args)
                                     (parse-simple-id-congruence-correct))))
                  ((mv ?ok left right) (parse-simple-disjunction x))
                  ((mv rule vars simple-term other-term)
                   (b* (((mv rule vars) (parse-simple-id-congruence left))
                        ((when rule) (mv rule vars left right))
                        ((mv rule vars) (parse-simple-id-congruence right)))
                     (mv rule vars right left)))
                  (var-vars (cmr::pseudo-term-var-list->names vars))
                  ;; ((unless rule) nil)
                  (diff-var
                   (parse-id-congruence-equivalence rule vars other-term))
                  (alist (cons (cons (pseudo-term-var->name diff-var) alt)
                               (pairlis$ var-vars args)))
                  (simple-true (fgl-ev simple-term alist)))
               (if simple-true
                   `(:use ((:instance acl2::mark-clause-is-true (x 'nonsimple-simple))
                           (:instance parse-simple-id-congruence-correct
                            (x ,(acl2::hq simple-term))
                            (a ,(acl2::hq alist)))
                           ;; (:instance fgl-ev-theoremp-implies
                           ;;  (x ,(acl2::hq simple-term))
                           ;;  (a ,(acl2::hq alist)))
                           )
                     :in-theory (e/d (parse-simple-disjunction-correct
                                      fgl-ev-of-fncall-args)
                                     (parse-simple-id-congruence-correct
                                      ;; fgl-ev-theoremp-implies
                                      )))
                 `(:use ((:instance acl2::mark-clause-is-true (x 'nonsimple-other))
                         (:instance parse-id-congruence-equivalence-correct
                          (rule ,(acl2::hq rule))
                          (vars ,(acl2::hq vars))
                          (x ,(acl2::hq other-term))
                          (a ,(acl2::hq alist)))
                         (:instance fgl-ev-theoremp-implies
                          (a ,(acl2::hq alist))))
                   :in-theory (e/d (parse-simple-disjunction-correct
                                    fgl-ev-of-fncall-args)
                                   (parse-id-congruence-equivalence-correct
                                    fgl-ev-theoremp-implies)))))
             :immediate-hints ('(:in-theory (enable <fn>)))
             ))
                                
               
     :fn parse-id-congruence-rule))
  
  (defret parse-id-congruence-rule-correct
    (implies (and (fgl-ev-theoremp x)
                  rule)
             (fgl-id-congruence-rule-correct rule))
    :hints (("goal" :in-theory (enable fgl-id-congruence-rule-correct)))
    :fn parse-id-congruence-rule))

(defret check-id-congruence-rune-correct
  (implies (and (fgl-ev-meta-extract-global-facts)
                (equal w (w state))
                (not errmsg))
           (fgl-id-congruence-rule-correct rule))
  :hints(("Goal" :in-theory (enable parse-id-congruence-rule-correct
                                    check-id-congruence-rune
                                    fgl-ev-meta-extract-formula-theoremp)))
  :fn check-id-congruence-rune)
           

(defsection fgl-id-congruence-rule-correct
  (defun-sk fgl-id-congruence-rule-correct (rule)
    (forall (args alt)
            (b* (((fgl-id-congruence-rule rule))
                 (val (fgl-ev (cons rule.fn (kwote-lst args)) nil))
                 (alt-val (fgl-ev (cons rule.fn (kwote-lst (update-nth rule.id-index alt args))) nil)))
              (implies (and (equal (len args) rule.arity)
                            (not (equal val (nth rule.id-index args))))
                       (equal (equal val alt-val) t))))
    :rewrite :direct)

  (in-theory (disable fgl-id-congruence-rule-correct
                      fgl-id-congruence-rule-correct-necc))

  (fty::deffixcong fgl-id-congruence-rule-equiv equal (fgl-id-congruence-rule-correct rule) rule
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'fgl-id-congruence-rule-correct clause))
                        (arg (cadr lit))
                        (other (if (eq arg 'rule) '(fgl-id-congruence-rule-fix rule) 'rule)))
                   `(:expand (,lit)
                     :use ((:instance fgl-id-congruence-rule-correct-necc
                            (rule ,other)
                            (args (mv-nth 0 (fgl-id-congruence-rule-correct-witness ,arg)))
                            (alt (mv-nth 1 (fgl-id-congruence-rule-correct-witness ,arg)))))))))))

(define fgl-id-congruence-rules-correct (rules)
  :verify-guards nil
  (if (atom rules)
      t
    (and (fgl-id-congruence-rule-correct (car rules))
         (fgl-id-congruence-rules-correct (cdr rules)))))

;; (defret id-congruence-table-from-runes-correct-fnsym
;;   (implies (hons-assoc-equal fnname table)
;;            (equal (fgl-id-congruence-rule->fn (cdr (hons-assoc-equal fnname table)))
;;                   fnname))
;;   :hints(("Goal" :induct <call>
;;           :in-theory (enable <fn>
;;                              (:i <fn>))))
;;   :fn id-congruence-table-from-runes)

(defretd id-congruence-table-from-runes-correct
  (implies (and (fgl-ev-meta-extract-global-facts)
                (equal w (w state)))
           (fgl-id-congruence-rules-correct (cdr (hons-assoc-equal fnname table))))
  :hints(("Goal" :induct <call>
          :in-theory (enable <fn>
                             fgl-id-congruence-rules-correct
                             check-id-congruence-rune-correct
                             (:i <fn>))))
  :fn id-congruence-table-from-runes)
           

(define fgl-id-congruence-rules (runes (w plist-worldp))
  :returns (table id-congruence-rule-table-p)
  (b* (((unless (fgl-id-congruence-runelist-p runes))
        (raise "Rune list did not satisfy fgl-id-congruence-runelist-p"))
       ((mv errmsg table) (id-congruence-table-from-runes runes w))
       (- (and errmsg
               (raise "Not all id-congruence runes could be parsed into valid rules: ~@0" errmsg))))
    table)
  ///
  (defretd <fn>-is-correct
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (fgl-id-congruence-rules-correct (cdr (hons-assoc-equal fnname table))))
    :hints(("Goal" :in-theory (enable id-congruence-table-from-runes-correct))))
  
  (memoize 'fgl-id-congruence-rules))




(local
 (encapsulate nil
  (local (defun list-equiv-ind (x y)
           (if (or (atom x) (atom y))
               (list x y)
             (list-equiv-ind (cdr x) (cdr y)))))
  
  (defthm nth-equiv-when-len-equal
    (implies (equal (len x) (len y))
             (iff (acl2::nth-equiv x y)
                  (acl2::list-equiv x y)))
    :hints(("Goal" :in-theory (enable acl2::nth-equiv-recursive)
            :induct (list-equiv-ind x y))))))



(local (fty::deffixcong acl2::list-equiv equal (kwote-lst x) x))

(local (defthm fgl-ev-congruence-correct-of-nil
         (fgl-ev-congruence-correct-p contexts fn nil arity)
         :hints(("Goal" :in-theory (enable fgl-ev-congruence-correct-p)))))

(define fgl-id-congruence-rule-equiv-contexts ((contexts equiv-contextsp)
                                               (fn pseudo-fnsym-p)
                                               (arity natp)
                                               (rule fgl-id-congruence-rule-p))
  :returns (arg-ctxs equiv-contextslist-p)
  :prepwork ((local (defthm equiv-contextslist-p-of-update-nth
                      (implies (and (equiv-contextsp v)
                                    (equiv-contextslist-p x))
                               (equiv-contextslist-p (update-nth n v x)))
                      :hints(("Goal" :in-theory (enable update-nth))))))
  (b* (((fgl-id-congruence-rule rule)))
    (and (eql (lnfix arity) rule.arity)
         (eq (pseudo-fnsym-fix fn) rule.fn)
         (< rule.id-index rule.arity)
         (update-nth rule.id-index (equiv-contexts-fix contexts) nil)))
  ///

  (defret len-of-<fn>
    (<= (len arg-ctxs) (nfix arity))
    :rule-classes :linear)
  
  (local (defthm fgl-ev-context-equiv-list-of-update-nth-implies-context-equiv-nth
           (implies (fgl-ev-context-equiv-list
                     (update-nth n (equiv-contexts-fix contexts) nil) a b)
                    (fgl-ev-context-equiv contexts (nth n a) (nth n b)))
           :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-list)))))


  (local (defthm update-nth-other-when-context-equiv-list
           (implies (and (fgl-ev-context-equiv-list (update-nth n contexts nil) args1 args2)
                         (equal (len args1) (len args2))
                         (< (nfix n) (len args1)))
                    (acl2::list-equiv (update-nth n (nth n args1) args2)
                                      args1))
           :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-list update-nth
                                             acl2::list-equiv true-list-fix)))))

  (local (defthm update-nth-other-when-context-equiv-list2
           (implies (and (fgl-ev-context-equiv-list (update-nth n contexts nil) args1 args2)
                         (equal (len args1) (len args2))
                         (< (nfix n) (len args1)))
                    (acl2::list-equiv (update-nth n (nth n args2) args1)
                                      args2))
           :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-list update-nth
                                             acl2::list-equiv true-list-fix)))))
  
  (defret fgl-ev-congruence-correct-of-<fn>
    (b* (((fgl-id-congruence-rule rule)))
      (implies (fgl-id-congruence-rule-correct rule)
               (fgl-ev-congruence-correct-p
                contexts fn arg-ctxs arity)))
    :hints((and stable-under-simplificationp
                '(:in-theory (e/d (fgl-ev-congruence-correct-p)
                                  (fgl-id-congruence-rule-correct-necc))
                  :use ((:instance fgl-id-congruence-rule-correct-necc
                         (args (b* (((fgl-id-congruence-rule rule)))
                                 (mv-nth 0 (fgl-ev-congruence-correct-p-witness
                                            contexts fn
                                            (fgl-id-congruence-rule-equiv-contexts contexts fn rule.arity rule)
                                            rule.arity))))
                         (alt (b* (((fgl-id-congruence-rule rule)))
                                (nth rule.id-index
                                     (mv-nth 1 (fgl-ev-congruence-correct-p-witness
                                                contexts fn
                                                (fgl-id-congruence-rule-equiv-contexts contexts fn rule.arity rule)
                                                rule.arity))))))
                        (:instance fgl-id-congruence-rule-correct-necc
                         (args (b* (((fgl-id-congruence-rule rule)))
                                 (mv-nth 1 (fgl-ev-congruence-correct-p-witness
                                            contexts fn
                                            (fgl-id-congruence-rule-equiv-contexts contexts fn rule.arity rule)
                                            rule.arity))))
                         (alt (b* (((fgl-id-congruence-rule rule)))
                                (nth rule.id-index
                                     (mv-nth 0 (fgl-ev-congruence-correct-p-witness
                                                contexts fn
                                                (fgl-id-congruence-rule-equiv-contexts contexts fn rule.arity rule)
                                                rule.arity))))))))))))


(define fgl-id-congruence-rules-equiv-contexts ((contexts equiv-contextsp)
                                                (fn pseudo-fnsym-p)
                                                (arity natp)
                                                (rules fgl-id-congruence-rulelist-p))
  :returns (arg-ctxs equiv-contextslist-p)
  (if (atom rules)
      nil
    (cmr::join-equiv-contextslists (fgl-id-congruence-rule-equiv-contexts contexts fn arity (car rules))
                                   (fgl-id-congruence-rules-equiv-contexts contexts fn arity (cdr rules))))
  ///
  (defret len-of-<fn>
    (<= (len arg-ctxs) (nfix arity))
    :rule-classes :linear)

  (local (defthm max-lte
           (implies (and (<= a x)
                         (<= b x))
                    (<= (max a b) x))))
  (local (in-theory (disable max)))
  
  (defret fgl-ev-congruence-correct-of-<fn>
    (implies (fgl-id-congruence-rules-correct rules)
             (fgl-ev-congruence-correct-p
              contexts fn arg-ctxs arity))
    :hints(("Goal" :in-theory (enable fgl-id-congruence-rules-correct)))))


(define fgl-interp-arglist-equiv-contexts ((contexts equiv-contextsp)
                                           (fn pseudo-fnsym-p)
                                           (arity natp)
                                           (runes)
                                           (id-runes)
                                           (w plist-worldp))
  :returns (new-contexts equiv-argcontexts-p)
  (b* (((when (member-eq 'unequiv (equiv-contexts-fix contexts))) t)
       (id-lookup (cdr (hons-get (pseudo-fnsym-fix fn) (fgl-id-congruence-rules id-runes w))))
       (rules (cdr (hons-get (pseudo-fnsym-fix fn) (fgl-congruence-rules runes w))))
       (id-contexts (fgl-id-congruence-rules-equiv-contexts contexts fn arity id-lookup)))
    (apply-congruence-rules rules fn contexts arity id-contexts))
  ///
  (local (defthm nth-equiv-when-equal-length
           (implies (equal (len x) (len y))
                    (equal (acl2::nth-equiv x y)
                           (acl2::list-equiv x y)))
           :hints(("Goal" :in-theory (enable acl2::list-equiv acl2::nth-equiv-recursive true-list-fix
                                             acl2::nth-equiv-ind len)
                   :induct (acl2::nth-equiv x y)))))

  (local (fty::deffixcong acl2::list-equiv equal (kwote-lst x) x
           :hints(("Goal" :in-theory (enable true-list-fix)))))

  (local (defthm fgl-ev-context-equiv-reflexive
           (fgl-ev-context-equiv ctx x x)
           :hints (`(:use ((:instance
                            (:functional-instance
                             cmr::equiv-ev-context-equiv-reflexive
                             . ,(let ((a (table-alist 'equiv-ev-fgl-ev-functional-subst world)))
                                  (pairlis$ (strip-cars a) (pairlis$ (strip-cdrs a) nil))))))
                     :in-theory (enable fgl-ev-context-equiv
                                        fgl-ev-context-equiv1
                                        fgl-ev-context-equiv1-suff
                                        fgl-ev-context-equiv-witness
                                        fgl-ev-context-equiv-trace
                                        fgl-ev-context-equiv-symm
                                        fgl-ev-context-equiv-base
                                        fgl-ev-of-fncall-args)))))

  (defret <fn>-correct
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (fgl-ev-argcontext-congruence-correct-p contexts fn new-contexts arity))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable fgl-ev-argcontext-congruence-correct-p
                                      fgl-id-congruence-rules-is-correct
                                      ))))))

