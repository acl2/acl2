; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(include-book "centaur/meta/parse-rewrite" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "centaur/meta/pseudo-rewrite-rule" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "syntax-bind") ;; for unequiv
(include-book "rule-types")
(local (include-book "std/lists/append" :dir :system))
(local (std::add-default-post-define-hook :fix))
;; (include-book "def-fgl-rewrite")


(local (in-theory (disable pseudo-termp
                           pseudo-term-listp
                           acl2::pseudo-termp-opener)))

;; get theorem about append of rulelists
(local (fty::deflist fgl-rulelist :elt-type fgl-rule :true-listp t))

(defevaluator rules-ev rules-ev-list
  ((equal x y) (iff x y) (if x y z) (implies x y) (not x) (typespec-check ts x)
   (unequiv x y))
  :namedp t)

(acl2::def-meta-extract rules-ev rules-ev-list)
(acl2::def-ev-pseudo-term-fty-support rules-ev rules-ev-list)


(define fgl-rule-term ((x fgl-rule-p))
  :returns (term pseudo-termp)
  :prepwork ((local (in-theory (enable pseudo-termp))))
  (fgl-rule-case x
    :rewrite `(implies ,(conjoin x.hyps)
                       (,x.equiv ,x.lhs ,x.rhs))
    :otherwise ''t))

(define fgl-rulelist-terms ((x fgl-rulelist-p))
  :returns (terms pseudo-term-listp)
  (if (atom x)
      nil
    (cons (fgl-rule-term (car x))
          (fgl-rulelist-terms (cdr x)))))

(define rules-ev-good-fgl-rule-p ((x fgl-rule-p))
  (rules-ev-theoremp (fgl-rule-term x)))

(local
 (defthmd rules-ev-ev-when-theoremp
   (implies (rules-ev-theoremp x)
            (rules-ev x a))
   :hints (("goal" :use rules-ev-falsify))))

(define rules-ev-good-fgl-rules-p ((x fgl-rulelist-p))
  (if (atom x)
      t
    (and (rules-ev-good-fgl-rule-p (car x))
         (rules-ev-good-fgl-rules-p (cdr x))))
  ///
  (defthm rules-ev-good-fgl-rules-p-implies-conjoin-fgl-rulelist-terms
    (implies (rules-ev-good-fgl-rules-p x)
             (rules-ev (conjoin (fgl-rulelist-terms x)) env))
    :hints(("Goal" :in-theory (enable fgl-rulelist-terms
                                      rules-ev-good-fgl-rule-p
                                      rules-ev-ev-when-theoremp))))

  (defthm rules-ev-good-fgl-rules-p-when-theoremp-conjoin
    (implies (rules-ev-theoremp (conjoin (fgl-rulelist-terms x)))
             (rules-ev-good-fgl-rules-p x))
    :hints(("Goal" :in-theory (enable fgl-rulelist-terms
                                      rules-ev-good-fgl-rule-p
                                      rules-ev-ev-when-theoremp))))

  (defthm rules-ev-good-fgl-rules-p-of-append
    (implies (and (rules-ev-good-fgl-rules-p x)
                  (rules-ev-good-fgl-rules-p y))
             (rules-ev-good-fgl-rules-p (append x y)))))

(local (in-theory (disable acl2::rewrite-rule-term)))

(define rules-ev-good-rewrite-rulesp (rules)
  (if (atom rules)
      t
    (and (rules-ev-theoremp (acl2::rewrite-rule-term (car rules)))
         (rules-ev-good-rewrite-rulesp (cdr rules))))
  ///
  (defthm rules-ev-good-rewrite-rulesp-of-cons
    (equal (rules-ev-good-rewrite-rulesp (cons a b))
           (and (rules-ev-theoremp (acl2::rewrite-rule-term a))
                (rules-ev-good-rewrite-rulesp b))))

  (defthm rules-ev-good-rewrite-rulesp-of-cdr
    (implies (rules-ev-good-rewrite-rulesp x)
             (rules-ev-good-rewrite-rulesp (cdr x))))

  (defthm rules-ev-of-car-when-good-rewrite-rulesp
    (implies (and (rules-ev-good-rewrite-rulesp x) (consp x))
             (rules-ev (acl2::rewrite-rule-term (car x)) a))
    :hints(("Goal" :in-theory (disable acl2::rewrite-rule-term)
            :expand ((rules-ev-good-rewrite-rulesp x))
            :use ((:instance rules-ev-falsify
                   (x (acl2::rewrite-rule-term (car x))) (a a))))))

  (local (defun rules-ev-good-rewrite-rulesp-badguy (rules)
           (if (atom rules)
               nil
             (if (rules-ev-theoremp (acl2::rewrite-rule-term (car rules)))
                 (rules-ev-good-rewrite-rulesp-badguy (cdr rules))
               (car rules)))))

  (local (defthmd rules-ev-good-rewrite-rulesp-by-badguy
           (iff (rules-ev-good-rewrite-rulesp rules)
                (b* ((badguy (rules-ev-good-rewrite-rulesp-badguy rules)))
                  (or (not (member badguy rules))
                      (rules-ev-theoremp (acl2::rewrite-rule-term badguy)))))))


  (defthm rules-ev-good-rewrite-rulesp-of-lemmas
    (implies (and (rules-ev-meta-extract-global-facts)
                  (equal wrld (w state)))
             (rules-ev-good-rewrite-rulesp (fgetprop fn 'acl2::lemmas nil wrld)))
    :hints(("Goal" :in-theory (e/d (rules-ev-good-rewrite-rulesp-by-badguy)
                                   (rules-ev-good-rewrite-rulesp
                                    rules-ev-good-rewrite-rulesp-badguy
                                    acl2::rewrite-rule-term
                                    w))
            :do-not-induct t))))

(define rules-ev-good-rewrite-rule-alistp (x)
  (if (atom x)
      t
    (and (or (atom (car x))
             (rules-ev-good-rewrite-rulesp (cdar x)))
         (rules-ev-good-rewrite-rule-alistp (cdr x))))
  ///
  (defthm lookup-when-rules-ev-good-rewrite-rule-alistp
    (implies (rules-ev-good-rewrite-rule-alistp x)
             (rules-ev-good-rewrite-rulesp (cdr (hons-assoc-equal k x))))))

(define map-rewrite-rules (lemmas map-acc)
  (b* (((when (atom lemmas)) map-acc)
       (lemma (car lemmas))
       ((unless (and (consp lemma)
                     (consp (cdr lemma))))
        (map-rewrite-rules (cdr lemmas) map-acc))
       (rest (cdr (hons-get (cadr lemma) map-acc)))
       (map-acc (hons-acons (cadr lemma) (cons lemma rest) map-acc)))
    (map-rewrite-rules (cdr lemmas) map-acc))
  ///
  (defthm rules-ev-good-rewrite-rulesp-of-map-rewrite-rules
    (implies (and (rules-ev-good-rewrite-rulesp lemmas)
                  (rules-ev-good-rewrite-rule-alistp map-acc))
             (rules-ev-good-rewrite-rule-alistp (map-rewrite-rules lemmas map-acc)))
    :hints(("Goal" :in-theory (enable rules-ev-good-rewrite-rulesp rules-ev-good-rewrite-rule-alistp)))))

(local (defthm pseudo-fnsym-p-by-symbolp
         (implies (and (symbolp x)
                       (not (equal x 'quote)))
                  (pseudo-fnsym-p x))
         :hints(("Goal" :in-theory (enable pseudo-fnsym-p)))))

(define fgl-rule-from-lemma ((fgl-rune fgl-rune-p) x)
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rule (implies (not errmsg) (fgl-rule-p rule))))
  (b* (((unless (pseudo-rewrite-rule-p x)) (mv (msg "Bad rewrite rule: ~x0" x) nil))
       ((acl2::rewrite-rule x))
       ((when (eq x.subclass 'acl2::meta))
        (mv (msg "Rule ~x0 is a :meta rule~%" x.rune) nil)))
    (mv nil (make-fgl-rule-rewrite :rune fgl-rune
                                   :rule (cmr::make-rewrite
                                          :hyps x.hyps
                                          :equiv x.equiv
                                          :lhs x.lhs
                                          :rhs x.rhs))))
  ///
  (defret rules-ev-good-fgl-rule-p-of-<fn>
    (implies (not errmsg)
             (equal (rules-ev (fgl-rule-term rule) env)
                    (rules-ev (acl2::rewrite-rule-term x) env)))
    :hints(("Goal" :in-theory (enable fgl-rule-term
                                      cmr::rewrite-rule-term-alt-def)))))

(define fgl-rules-from-lemmas ((fgl-rune fgl-rune-p) lemmas)
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-rulelist-p))
  (b* (((when (atom lemmas)) (mv nil nil))
       ((mv err rule) (fgl-rule-from-lemma fgl-rune (car lemmas)))
       ((mv err2 rest) (fgl-rules-from-lemmas fgl-rune (cdr lemmas))))
    (mv (or err err2)
        (if err rest (cons rule rest))))
  ///
  (defret rules-ev-good-fgl-rules-p-of-<fn>
    (implies (rules-ev-good-rewrite-rulesp lemmas)
             (rules-ev-good-fgl-rules-p rules))
    :hints(("Goal" :in-theory (enable rules-ev-good-fgl-rules-p
                                      rules-ev-good-fgl-rule-p
                                      rules-ev-good-rewrite-rulesp)))))

(define fgl-rules-from-rewrite (rune (fgl-rune fgl-rune-p) fn-lemma-map)
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-rulelist-p))
  :guard-hints (("goal" :in-theory (enable pseudo-fnsym-p)))
  (b* ((rw (cdr (hons-get rune fn-lemma-map))))
    (fgl-rules-from-lemmas fgl-rune rw))
  ///
  (defret rules-ev-good-fgl-rule-p-of-<fn>
    (implies (rules-ev-good-rewrite-rule-alistp fn-lemma-map)
             (rules-ev-good-fgl-rules-p rules))))

#!cmr
(defret rules-ev-of-parse-rewrites-from-term
  (implies (fgl::rules-ev x env)
           (fgl::rules-ev (conjoin (cmr::rewritelist-terms rewrites)) env))
  :hints (("goal" :use ((:functional-instance parse-rw-ev-of-parse-rewrites-from-term
                         (parse-rw-ev fgl::rules-ev)
                         (parse-rw-ev-list fgl::rules-ev-list)))
           :in-theory (enable fgl::rules-ev-of-fncall-args)))
  :fn parse-rewrites-from-term)



(define fgl-rule-from-cmr-rewrite ((rune fgl-rune-p) (x cmr::rewrite-p))
  :returns (rule fgl-rule-p)
  (b* (((cmr::rewrite x)))
    (make-fgl-rule-rewrite :rule (cmr::make-rewrite :hyps x.hyps
                                                    :lhs x.lhs
                                                    :rhs x.rhs
                                                    :equiv x.equiv)
                           :rune rune))
  ///
  (defret rules-ev-ev-of-<fn>
    (equal (rules-ev (fgl-rule-term rule) env)
           (rules-ev (cmr::rewrite-term x) env))
    :hints(("Goal" :in-theory (enable fgl-rule-term cmr::rewrite-term)))))

(define fgl-rules-from-cmr-rewrites ((rune fgl-rune-p) (x cmr::rewritelist-p))
  :returns (rules fgl-rulelist-p)
  (if (atom x)
      nil
    (cons (fgl-rule-from-cmr-rewrite rune (car x))
          (fgl-rules-from-cmr-rewrites rune (cdr x))))
  ///
  (defret rules-ev-ev-of-<fn>
    (iff (rules-ev (conjoin (fgl-rulelist-terms rules)) env)
         (rules-ev (conjoin (cmr::rewritelist-terms x)) env))
    :hints(("Goal" :in-theory (enable cmr::rewritelist-terms fgl-rulelist-terms)))))

(local
 (defthmd rules-ev-when-theoremp
   (implies (rules-ev-theoremp x)
            (rules-ev x a))
   :hints (("goal" :use rules-ev-falsify))))

(define fgl-rules-from-formula ((form pseudo-termp)
                                (fgl-rune fgl-rune-p)
                                (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-rulelist-p))
  (b* (((mv err rewrites) (cmr::parse-rewrites-from-term form world)))
    (mv err (fgl-rules-from-cmr-rewrites fgl-rune rewrites)))
  ///

  (defret rules-ev-good-fgl-rule-p-of-<fn>
    (implies (rules-ev-theoremp form)
             (rules-ev-good-fgl-rules-p rules))
    :hints(("Goal" :in-theory (enable rules-ev-when-theoremp)))))


(local (in-theory (disable w)))

(define fgl-rules-from-rune ((rune fgl-rune-p) (fn-lemma-map) (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-rulelist-p))
  :prepwork ((local (defthm fgl-rule-p-of-rune
                      (implies (and (fgl-rune-p x)
                                    (not (fgl-rune-case x :rewrite))
                                    (not (fgl-rune-case x :definition))
                                    (not (fgl-rune-case x :formula)))
                               (and (fgl-rule-p x)
                                    (equal (fgl-rule-kind x)
                                           (fgl-rune-kind x))))
                      :hints(("Goal" :in-theory (enable fgl-rune-p fgl-rule-p fgl-rune-kind fgl-rule-kind))))))
  (fgl-rune-case rune
    :rewrite (fgl-rules-from-rewrite `(:rewrite ,rune.name) rune fn-lemma-map)
    :definition (fgl-rules-from-rewrite `(:definition ,rune.name) rune fn-lemma-map)
    :formula (b* ((form (acl2::meta-extract-formula-w rune.name world))
                  ((unless (pseudo-termp form))
                   (mv (msg "Formula for ~x0 was not pseudo-termp: ~x1~%" rune.name form) nil)))
               (fgl-rules-from-formula form rune world))
    :otherwise (mv nil (list (fgl-rune-fix rune))))
  ///
  (local (defthm fgl-rule-term-when-not-rewrite
           (implies (not (fgl-rule-case x :rewrite))
                    (equal (fgl-rule-term x) ''t))
           :hints(("Goal" :in-theory (enable fgl-rule-term)))))

  (local (defthm fgl-rule-p-of-rune-fix
           (implies (and (not (fgl-rune-case x :rewrite))
                         (not (fgl-rune-case x :definition))
                         (not (fgl-rune-case x :formula)))
                    (and (fgl-rule-p (fgl-rune-fix x))
                         (equal (fgl-rule-kind (fgl-rune-fix x))
                                (fgl-rune-kind x))))
           :hints(("Goal" :use ((:instance fgl-rule-p-of-rune (x (fgl-rune-fix x))))
                   :in-theory (disable fgl-rule-p-of-rune)))))

  (defret rules-ev-good-fgl-rules-p-of-<fn>
    (implies (and (rules-ev-good-rewrite-rule-alistp fn-lemma-map)
                  (rules-ev-meta-extract-global-facts)
                  (equal world (w state)))
             (rules-ev-good-fgl-rules-p rules))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable rules-ev-good-fgl-rules-p)))
            (and stable-under-simplificationp
                 '(:in-theory (enable rules-ev-good-fgl-rule-p))))))

(define fgl-rules-from-runes ((runes fgl-runelist-p) (fn-lemma-map) (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-rulelist-p))
  (b* (((when (atom runes)) (mv nil nil))
       ((mv errmsg1 rules1) (fgl-rules-from-rune (car runes) fn-lemma-map world))
       ((mv errmsg2 rest) (fgl-rules-from-runes (cdr runes) fn-lemma-map world)))
    (mv (or errmsg1 errmsg2) (append rules1 rest)))
  ///
  (defret rules-ev-good-fgl-rules-p-of-<fn>
    (implies (and (rules-ev-good-rewrite-rule-alistp fn-lemma-map)
                  (rules-ev-meta-extract-global-facts)
                  (equal world (w state)))
             (rules-ev-good-fgl-rules-p rules))
    :hints(("Goal" :in-theory (enable rules-ev-good-fgl-rules-p)))))

(define fgl-rules-filter-leading-fnsym ((fn pseudo-fnsym-p) (x fgl-rulelist-p))
  :returns (new-x fgl-rulelist-p)
  (b* (((When (atom x)) nil)
       (x1 (car x))
       ((unless (fgl-rule-case x1 :rewrite))
        (cons (fgl-rule-fix x1)
              (fgl-rules-filter-leading-fnsym fn (cdr x))))
       ((fgl-rule-rewrite x1))
       ((cmr::rewrite x1.rule))
       ((when (pseudo-term-case x1.rule.lhs
                :fncall (eq x1.rule.lhs.fn (pseudo-fnsym-fix fn))
                :otherwise nil))
        (cons (fgl-rule-fix x1)
              (fgl-rules-filter-leading-fnsym fn (cdr x)))))
    (fgl-rules-filter-leading-fnsym fn (cdr x)))
  ///
  (defret rules-ev-good-fgl-rules-p-of-<fn>
    (implies (rules-ev-good-fgl-rules-p x)
             (rules-ev-good-fgl-rules-p new-x))
    :hints(("Goal" :in-theory (enable rules-ev-good-fgl-rules-p)))))

(define fgl-rewrite-rules-lookup ((fn pseudo-fnsym-p) (alist) (world plist-worldp))
  (b* ((look (hons-get (pseudo-fnsym-fix fn) alist)))
    (if look
        (cdr look)
      (if (eq (fgetprop (pseudo-fnsym-fix fn) 'acl2::unnormalized-body :none world) :none)
          nil
        (list (fgl-rune-formula fn))))))
       


(define fgl-function-rules ((fn pseudo-fnsym-p) (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-rulelist-p))
  (b* ((table (make-fast-alist (table-alist 'fgl-rewrite-rules world)))
       (fn (pseudo-fnsym-fix fn))
       (runes (fgl-rewrite-rules-lookup fn table world))
       ((unless (fgl-runelist-p runes))
        (mv (msg "Error: entry for ~x0 in the ~x1 table did not satisfy ~x2~%"
                 fn 'fgl-rewrite-rules 'fgl-runelist-p)
            nil))
       (lemmas (fgetprop fn 'acl2::lemmas nil world))
       (map (map-rewrite-rules lemmas nil))
       ((mv err rules1)
        (fgl-rules-from-runes runes map world)))
    (mv err (fgl-rules-filter-leading-fnsym fn rules1)))
  ///
  (defret rules-ev-good-fgl-rules-p-of-<fn>
    (implies (and (rules-ev-meta-extract-global-facts)
                  (equal world (w state)))
             (rules-ev-good-fgl-rules-p rules)))

  (memoize 'fgl-function-rules))


(define map-rewrite-rules-memo (lemmas)
  :enabled t
  (map-rewrite-rules lemmas nil)
  ///
  (memoize 'map-rewrite-rules-memo))

(define fgl-rule-match-branch-fnsym ((fn pseudo-fnsym-p) (x fgl-rule-p))
  (fgl-rule-case x
    :rewrite
    (b* (((cmr::rewrite x.rule)))
      (pseudo-term-case x.rule.lhs
        :fncall (and (eq x.rule.lhs.fn 'if)
                     (eql (len x.rule.lhs.args) 3)
                     (b* ((arg2 (second x.rule.lhs.args)))
                       (pseudo-term-case arg2
                         :fncall (eq arg2.fn (pseudo-fnsym-fix fn))
                         :otherwise nil)))
        :otherwise nil))
    :otherwise t)) ;; might match

(define fgl-rules-filter-branch-fnsym ((fn pseudo-fnsym-p) (x fgl-rulelist-p))
  :returns (new-x fgl-rulelist-p)
  (cond ((atom x) nil)
        ((fgl-rule-match-branch-fnsym fn (car x))
         (cons (fgl-rule-fix (car x)) (fgl-rules-filter-branch-fnsym fn (cdr x))))
        (t (fgl-rules-filter-branch-fnsym fn (cdr x))))
  ///
  (defret rules-ev-good-fgl-rules-p-of-<fn>
    (implies (rules-ev-good-fgl-rules-p x)
             (rules-ev-good-fgl-rules-p new-x))
    :hints(("Goal" :in-theory (enable rules-ev-good-fgl-rules-p)))))

(define fgl-branch-merge-rules-lookup ((fn pseudo-fnsym-p) (alist))
  (cdr (hons-get (pseudo-fnsym-fix fn) alist)))


(define fgl-branch-merge-rules ((fn pseudo-fnsym-p) (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-rulelist-p))
  (b* ((table (make-fast-alist (table-alist 'fgl-branch-merge-rules world)))
       (fn (pseudo-fnsym-fix fn))
       (runes (fgl-branch-merge-rules-lookup fn table))
       ((unless (fgl-runelist-p runes))
        (mv (msg "Error: entry for ~x0 in the ~x1 table did not satisfy ~x2~%"
                 fn 'fgl-rewrite-rules 'fgl-runelist-p)
            nil))
       (lemmas (fgetprop 'if 'acl2::lemmas nil world))
       (map (map-rewrite-rules-memo lemmas))
       ((mv errmsg rules1) (fgl-rules-from-runes runes map world)))
    (mv errmsg (fgl-rules-filter-branch-fnsym fn rules1)))
  ///
  (defret rules-ev-good-fgl-rules-p-of-<fn>
    (implies (and (rules-ev-meta-extract-global-facts)
                  (equal world (w state)))
             (rules-ev-good-fgl-rules-p rules)))

  (memoize 'fgl-branch-merge-rules))







