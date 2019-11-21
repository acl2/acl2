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

(in-package "FGL")

(include-book "contexts")

(local (std::add-default-post-define-hook :fix))

(defprod fgl-congruence-rune
  ((name pseudo-fnsym-p))
  :tag :congruence
  :layout :list)

(fty::deflist fgl-congruence-runelist :elt-type fgl-congruence-rune :true-listp t)

(local (in-theory (disable w)))

(fty::deflist congruence-rulelist :elt-type cmr::congruence-rule :true-listp t)

(std::deflist fgl-ev-congruence-rulelist-correct-p (x)
  :guard (congruence-rulelist-p x)
  (fgl-ev-congruence-rule-correct-p x)
  ///
  (fty::deffixcong congruence-rulelist-equiv equal (fgl-ev-congruence-rulelist-correct-p x) x))

;; (define fgl-ev-congruence-rulelist-correct-p ((x congruence-rulelist-p))
;;   (if (atom x)
;;       t
;;     (and (fgl-ev-congruence-rule-correct-p (car x))
;;          (fgl-ev-congruence-rulelist-correct-p (cdr x))))
;;   ///
;;   (defthm fgl-ev-congruence-rulelist-correct-p-of-cons
;;     (equal (fgl-ev-congruence-rulelist-correct-p (cons a b))
;;            (and (fgl-ev-congruence-rule-correct-p a)
;;                 (fgl-ev-congruence-rulelist-correct-p b))

(define congruence-rule-from-rune ((rune fgl-congruence-rune-p)
                                   (w plist-worldp))
  :returns (mv errmsg (rule (implies (not errmsg) (cmr::congruence-rule-p rule))))
  (b* ((name (fgl-congruence-rune->name rune))
       (formula (acl2::meta-extract-formula-w name w))
       ((unless (pseudo-termp formula))
        (mv (msg "Bad formula: ~x0" name) nil)))
    (cmr::parse-congruence-rule formula w))
  ///
  (defret fgl-ev-congruence-rule-correct-p-of-<fn>
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal w (w state))
                  (not errmsg))
             (fgl-ev-congruence-rule-correct-p rule))))

(define congruence-rules-from-runes ((runes fgl-congruence-runelist-p)
                                     (w plist-worldp))
  :returns (mv errmsg (rules congruence-rulelist-p))
  (b* (((when (atom runes)) (mv nil nil))
       ((mv errmsg1 rule) (congruence-rule-from-rune (car runes) w))
       ((mv errmsg2 rules) (congruence-rules-from-runes (cdr runes) w)))
    (if errmsg1
        (mv errmsg1 rules)
      (mv errmsg2 (cons rule rules))))
  ///
  (defret fgl-ev-congruence-rulelist-correct-p-of-<fn>
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (fgl-ev-congruence-rulelist-correct-p rules))))


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



(fty::defmap congruence-rule-table :key-type pseudo-fnsym :val-type congruence-rulelist
  :true-listp t)

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
             :expand ((:free (a b) (fgl-ev-congruence-rule-table-correct-p (cons a b)))))))

  (local (in-theory (enable congruence-rulelist-fix))))

(define fgl-congruence-runes ((w plist-worldp))
  (cdr (hons-assoc-equal 'fgl-congruence-rules (table-alist 'fgl-congruence-rules w))))

(defmacro add-fgl-congruence (name)
  (let ((rune (fgl-congruence-rune name)))
    `(progn (local (make-event
                    (b* ((rune ',rune)
                         ((mv errmsg &) (congruence-rule-from-rune rune (w state)))
                         ((when errmsg) (er soft 'add-fgl-congruence
                                            "Couldn't extract a congruence rule from ~x0: ~@1"
                                            rune errmsg)))
                      (value '(value-triple :congruence-rule-ok)))))
            (table fgl-congruence-rules 'fgl-congruence-rules
                   (cons ',rune (fgl-congruence-runes world))))))


(define congruence-rule-table-from-runes (runes (w plist-worldp))
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

  (memoize 'congruence-rule-table-from-runes))

(define fgl-congruence-rules ((w plist-worldp))
  :returns (table congruence-rule-table-p)
  (b* ((runes (fgl-congruence-runes w)))
    (congruence-rule-table-from-runes runes w))
  ///
  (defret fgl-ev-congruence-rule-table-correct-p-of-<fn>
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (fgl-ev-congruence-rule-table-correct-p table)))

  (memoize 'fgl-congruence-rules))
    



(define fgl-interp-arglist-equiv-contexts ((contexts equiv-contextsp)
                                           (fn pseudo-fnsym-p)
                                           (arity natp)
                                           (w plist-worldp))
  :returns (new-contexts equiv-argcontexts-p)
  (b* (((when (member-eq 'unequiv (equiv-contexts-fix contexts))) t)
       (rules (cdr (hons-get (pseudo-fnsym-fix fn) (fgl-congruence-rules w)))))
    (apply-congruence-rules rules fn contexts arity nil))
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

  (local (defthm fgl-ev-congruence-correct-p-of-empty-argcontexts
           (fgl-ev-congruence-correct-p contexts fn nil arity)
           :hints(("Goal" :in-theory (enable fgl-ev-congruence-correct-p)))))

  (defret <fn>-correct
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (fgl-ev-argcontext-congruence-correct-p contexts fn new-contexts arity))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable fgl-ev-argcontext-congruence-correct-p))))))


       
