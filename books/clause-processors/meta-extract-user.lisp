; Copyright (C) 2012-2014 Centaur Technology
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

(in-package "ACL2")

;; This book defines theorems and tools to enable
;; the user to more easily use the supported system functions in their meta
;; rules (and, not yet implemented, clause processors).

;(include-book "meta-extract-ttag")
(include-book "ev-theoremp")
(include-book "tools/def-functional-instance" :dir :system)
(include-book "tools/match-tree" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "magic-ev")
(include-book "xdoc/top" :dir :system)

; The following are necessary for developer builds, in which sublis-var and
; other supporting functions for meta-extract are not in :logic mode.
(include-book "system/sublis-var" :dir :system)
(include-book "system/meta-extract" :dir :system)

(in-theory (disable mv-nth))

;; The functions listed in this evaluator are the ones necessary to use all
;; meta-extract facilities, i.e. to prove the theorems that follow.  We provide a
;; macro def-meta-extract below which proves these theorems for an extension of
;; this evaluator.
(defevaluator mextract-ev mextract-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b))
  :namedp t)

;; This introduces a bad-guy function MEXTRACT-EV-FALSIFY and a macro
;; (MEXTRACT-EV-THEOREMP x) --> (mextract-ev x (mextract-ev-falsify x))
;; along with theorems for reasoning about falsify and
;; disjoin/conjoin/conjoin-clauses.
(def-ev-theoremp mextract-ev)

;; Badguy for contextual terms.
(defchoose mextract-contextual-badguy (obj) (a mfc state)
  (not (mextract-ev (meta-extract-contextual-fact obj mfc state) a)))

;; (mextract-ev-contextual-facts a) can be used as a hyp in a :meta rule, and
;; allows us to assume the correctness of any result (correctly) derived from
;; the supported contextual prover facilities with respect to mextract-ev.
(defmacro mextract-ev-contextual-facts (a &key (mfc 'mfc) (state 'state))
  `(mextract-ev
    (meta-extract-contextual-fact
     (mextract-contextual-badguy ,a ,mfc ,state)
     ,mfc ,state)
    ,a))


(defthmd mextract-contextual-badguy-sufficient
  (implies (mextract-ev-contextual-facts a)
           (mextract-ev (meta-extract-contextual-fact obj mfc state) a))
  :hints (("goal" :use mextract-contextual-badguy
           :in-theory (disable meta-extract-contextual-fact))))

;; Badguy for global terms.
(defchoose mextract-global-badguy (obj st) (state)
  (not (mextract-ev-theoremp (meta-extract-global-fact+ obj st state))))

;; (mextract-ev-global-facts) can be used as a hyp in a :meta rule, and
;; allows us to assume the correctness of any result (correctly) derived from
;; the supported global prover facilities with respect to mextract-ev.
(defmacro mextract-ev-global-facts (&key (state 'state))
  `(mextract-ev
    (meta-extract-global-fact+
     (mv-nth 0 (mextract-global-badguy ,state))
     (mv-nth 1 (mextract-global-badguy ,state))
     ,state)
    (mextract-ev-falsify
     (meta-extract-global-fact+
      (mv-nth 0 (mextract-global-badguy ,state))
      (mv-nth 1 (mextract-global-badguy ,state))
      ,state))))

(defthmd mextract-global-badguy-sufficient
  (implies (mextract-ev-global-facts)
           (mextract-ev (meta-extract-global-fact+ obj st state) a))
  :hints (("goal" :use ((:instance mextract-global-badguy)
                        (:instance mextract-ev-falsify
                         (x (meta-extract-global-fact+ obj st state))))
           :in-theory (disable meta-extract-global-fact+))))


(local (in-theory (disable w sublis-var)))

;; Assuming (mextract-ev-contextual-facts a), we know mfc-ts works as expected.
(defthm mextract-typeset
  (implies (mextract-ev-contextual-facts a)
           (typespec-check (mfc-ts term mfc state :forcep nil)
                           (mextract-ev term a)))
  :hints (("goal" :use ((:instance mextract-contextual-badguy
                         (obj `(:typeset ,term))))
           :in-theory (disable typespec-check))))

;; Assuming (mextract-ev-contextual-facts a), mfc-rw+ works as expected
;; for equal, iff, and equiv-relation calls (note: no geneqvs yet).
(defthm mextract-rw+-equal
  (implies (mextract-ev-contextual-facts a)
           (equal (mextract-ev
                   (mfc-rw+ term alist obj nil mfc state
                            :forcep nil)
                   a)
                  (mextract-ev (sublis-var alist term) a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw+ term alist obj nil)))))))

(defthm mextract-rw+-iff
  (implies (mextract-ev-contextual-facts a)
           (iff (mextract-ev
                 (mfc-rw+ term alist obj t mfc state
                          :forcep nil)
                 a)
                (mextract-ev (sublis-var alist term) a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw+ term alist obj t)))))))

(defthm mextract-rw+-equiv
  (implies (and (mextract-ev-contextual-facts a)
                equiv
                (not (equal equiv t))
                (symbolp equiv)
                (getprop equiv 'coarsenings nil 'current-acl2-world (w state)))
           (mextract-ev
            `(,equiv ,(sublis-var alist term)
                    ,(mfc-rw+ term alist obj equiv mfc state
                              :forcep nil))
            a))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw+ term alist obj equiv)))))))

;; Assuming (mextract-ev-contextual-facts a), mfc-rw works as expected
;; for equal, iff, and equiv-relation calls (note: no geneqvs yet).
(defthm mextract-rw-equal
  (implies (mextract-ev-contextual-facts a)
           (equal (mextract-ev
                   (mfc-rw term obj nil mfc state
                           :forcep nil)
                   a)
                  (mextract-ev (sublis-var nil term) a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw term obj nil)))))))

(defthm mextract-rw-iff
  (implies (mextract-ev-contextual-facts a)
           (iff (mextract-ev
                 (mfc-rw term obj t mfc state
                         :forcep nil)
                 a)
                (mextract-ev (sublis-var nil term) a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw term obj t)))))))

(defthm mextract-rw-equiv
  (implies (and (mextract-ev-contextual-facts a)
                equiv
                (not (equal equiv t))
                (symbolp equiv)
                (getprop equiv 'coarsenings nil 'current-acl2-world (w state)))
           (mextract-ev
            `(,equiv ,(sublis-var nil term)
                    ,(mfc-rw term obj equiv mfc state
                             :forcep nil))
            a))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw term obj equiv)))))))

;; Assuming (mextract-ev-contextual-facts a), mfc-ap works as expected.
(defthm mextract-mfc-ap
  (implies (and (mextract-ev-contextual-facts a)
                (mextract-ev term a))
           (not (mfc-ap term mfc state :forcep nil)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :ap term)))))))

;; Assuming (mextract-ev-contextual-facts a), mfc-relieve-hyp works as expected.
(defthm mextract-relieve-hyp
  (implies (and (mextract-ev-contextual-facts a)
                (not (mextract-ev (sublis-var alist hyp) a)))
           (not (mfc-relieve-hyp hyp alist rune target bkptr mfc state
                                 :forcep nil)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :relieve-hyp hyp alist rune target bkptr)))))))

;; Assuming (mextract-ev-global-facts), meta-extract-formula produces a theorem
(defthm mextract-formula
  (implies (and (mextract-ev-global-facts)
                (equal (w st) (w state)))
           (mextract-ev (meta-extract-formula name st) a))
  :hints(("Goal" :use ((:instance mextract-global-badguy-sufficient
                        (obj (list :formula name)))))))

;; The following is used to show that any member of a list may be accessed by
;; nth, which is needed for mextract-lemma below
(local
 (encapsulate nil
   (local (defthm minus-over-plus
            (equal (- (+ a b))
                   (+ (- a) (- b)))))
   (local (defthm plus-move-constant
            (implies (syntaxp (quotep b))
                     (equal (+ a b c)
                            (+ b a c)))))
   (local (defthm nth-plus-1
            (implies (natp b)
                     (equal (nth (+ 1 b) x)
                            (nth b (cdr x))))))

   (defthm len-member-equal
     (<= (len (member-equal x y)) (len y))
     :rule-classes :linear)

   (defthm len-member-equal-pos
     (implies (member-equal x y)
              (< 0 (len (member-equal x y))))
     :rule-classes :linear)

   (defthm nth-by-member-equal
     (implies (member x y)
              (equal (nth (+ (len y) (- (len (member x y)))) y)
                     x)))))

(defthm mextract-lemma-term
  (implies (and (mextract-ev-global-facts)
                (member rule (fgetprop fn 'lemmas nil (w st)))
                (equal (w st) (w state)))
           (mextract-ev (rewrite-rule-term rule)
                      a))
  :hints(("Goal"
          :use ((:instance mextract-global-badguy-sufficient
                 (obj (list :lemma fn
                            (let ((lemmas
                                   (getprop fn 'lemmas nil
                                            'current-acl2-world (w state))))
                              (- (len lemmas)
                                 (len (member rule lemmas)))))))))))

;; Assuming (mextract-ev-global-facts), each element of the lemmas property of a
;; symbol in the world is a correct rewrite rule.
(defthm mextract-lemma
  (implies (and (mextract-ev-global-facts)
                (member rule (fgetprop fn 'lemmas nil (w st)))
                (not (eq (access rewrite-rule rule :subclass) 'meta))
                (mextract-ev (conjoin (access rewrite-rule rule :hyps)) a)
                (equal (w st) (w state)))
           (mextract-ev `(,(access rewrite-rule rule :equiv)
                        ,(access rewrite-rule rule :lhs)
                        ,(access rewrite-rule rule :rhs))
                      a))
  :hints(("Goal"
          :use ((:instance mextract-global-badguy-sufficient
                 (obj (list :lemma fn
                            (let ((lemmas
                                   (getprop fn 'lemmas nil
                                            'current-acl2-world (w state))))
                              (- (len lemmas)
                                 (len (member rule lemmas)))))))))))


(defthm plist-worldp-w-state
  (implies (state-p1 state)
           (plist-worldp (w state)))
  :hints(("Goal" :in-theory (enable w))))

(defun magic-ev-fncall-logic (fn arglist state)
  (declare (xargs :guard (symbolp fn)
                  :stobjs state))
  (if (logicp fn (w state))
      (magic-ev-fncall fn arglist state t nil)
    (mv (msg "Not logic mode: ~x0" fn) nil)))

(defthm mextract-fncall-logic
  (mv-let (erp val)
    (magic-ev-fncall-logic fn arglist st)
    (implies (and (mextract-ev-global-facts)
                  (equal (w st) (w state))
                  (not erp))
             (equal val
                    (mextract-ev (cons fn (kwote-lst arglist)) nil))))
  :hints(("Goal"
          :use ((:instance mextract-global-badguy-sufficient
                 (obj (list :fncall fn arglist))
                 (a nil))))))

(local (in-theory (disable magic-ev-fncall-logic)))


(defthm mextract-fncall
  (mv-let (erp val)
    (magic-ev-fncall fn arglist st t nil)
    (implies (and (mextract-ev-global-facts)
                  (equal (w st) (w state))
                  (not erp)
                  (logicp fn (w st)))
             (equal val
                    (mextract-ev (cons fn (kwote-lst arglist)) nil))))
  :hints(("Goal"
          :use ((:instance mextract-global-badguy-sufficient
                 (obj (list :fncall fn arglist))
                 (a nil))))))

(set-state-ok t)
(flag::make-flag magic-ev-flg magic-ev)

(defthm-magic-ev-flg
  (defthm mextract-ev-magic-ev
    (mv-let (erp val)
      (magic-ev x alist st hard-errp aokp)
      (implies (and (mextract-ev-global-facts)
                    (equal (w st) (w state))
                    (not erp)
                    (equal hard-errp t)
                    (equal aokp nil)
                    ;; need pseudo-termp so that we know we don't look up
                    ;; non-symbol atoms
                    (pseudo-termp x)
                    (logic-fnsp x (w st)))
               (equal val
                      (mextract-ev x alist))))
    :flag magic-ev)
  (defthm mextract-ev-magic-ev-lst
    (mv-let (erp val)
      (magic-ev-lst x alist st hard-errp aokp)
      (implies (and (mextract-ev-global-facts)
                    (equal (w st) (w state))
                    (not erp)
                    (equal hard-errp t)
                    (equal aokp nil)
                    (pseudo-term-listp x)
                    (logic-fns-listp x (w st)))
               (equal val
                      (mextract-ev-lst x alist))))
    :flag magic-ev-lst)

    :hints(("goal" :in-theory (e/d (mextract-ev-of-fncall-args)
                                   (meta-extract-global-fact+))
            :induct (magic-ev-flg flag x alist st hard-errp aokp))))




;; Get a function's definition via meta-extract-formula.
(defun fn-get-def (fn state)
  (declare (xargs :guard (symbolp fn)
                  :stobjs state))
  (b* (((when (eq fn 'quote))
        (mv nil nil nil))
       (formula (meta-extract-formula fn state))
       ((unless-match formula (equal ((:! fn) . (:? formals)) (:? body)))
        (mv nil nil nil))
       ((unless (and (symbol-listp formals)
                     (not (member-eq nil formals))
                     (no-duplicatesp-eq formals)))
        (mv nil nil nil)))
    (mv t formals body)))

(defthm fn-get-def-formals
  (b* (((mv ok formals ?body) (fn-get-def fn st)))
    (implies ok
             (and (symbol-listp formals)
                  (not (member nil formals))
                  (no-duplicatesp formals)))))


(encapsulate nil
  (local (defun ev-pair-ind (head keys vals)
           (if (atom keys)
               head
             (ev-pair-ind (append head (list (cons (car keys) (car vals))))
                          (cdr keys) (cdr vals)))))
  (local (defthm intersectp-commutes
           (equal (intersectp x y)
                  (intersectp y x))))

  (local (defthm intersectp-of-append
           (equal (intersectp (append y z) x)
                  (or (intersectp y x)
                      (intersectp z x)))
           :hints (("goal" :induct (append y z)
                    :in-theory (disable intersectp-commutes)))))

  (local (defthm intersectp-of-append2
           (equal (intersectp x (append y z))
                  (or (intersectp x y)
                      (intersectp x z)))
           :hints (("goal" :use intersectp-of-append
                    :in-theory (disable intersectp-of-append)
                    :do-not-induct t))))

  (local (defthm intersectp-list
           (iff (intersectp x (list y))
                (member y x))))

  (local (defthm append-append
           (equal (append (append a b) c)
                  (append a b c))))

  (local (defthm alistp-append
           (implies (and (alistp a)
                         (alistp b))
                    (alistp (append a b)))))
  ;; (local (include-book "std/lists/take" :dir :system))
  (local (defthm commutativity-2-of-+
           (equal (+ x (+ y z))
                  (+ y (+ x z)))))

  (local (defthm fold-consts-in-+
           (implies (and (syntaxp (quotep x))
                         (syntaxp (quotep y)))
                    (equal (+ x (+ y z)) (+ (+ x y) z)))))

  (local (defthm distributivity-of-minus-over-+
           (equal (- (+ x y)) (+ (- x) (- y)))))
  ;; (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (defthm assoc-when-not-member-strip-cars
           (implies (and (not (member k (strip-cars x)))
                         (alistp x))
                    (not (assoc k x)))))
  (local (defthm assoc-of-append-alist
           (implies (alistp head)
                    (equal (assoc k (append head rest))
                           (or (assoc k head) (assoc k rest))))))
  (local (defthm strip-cars-append
           (equal (strip-cars (Append a b))
                  (append (Strip-cars a) (strip-cars b)))))

  (defthm ev-lst-of-pairlis-append-head-rest
    (implies (and (no-duplicatesp keys)
                  (alistp head)
                  (not (intersectp keys (strip-cars head)))
; (true-listp vals)
; (equal (len keys) (len vals))
                  (symbol-listp keys)
                  (not (member nil keys)))
             (equal (mextract-ev-lst keys
                                     (append head
                                             (pairlis$ keys vals)
                                             rest))
                    (take (len keys) vals)))
    :hints (("goal" :induct (ev-pair-ind head keys vals)
             :do-not-induct t)))

  (defthm ev-lst-of-pairlis-append-rest
    (implies (and (no-duplicatesp keys)
; (true-listp vals)
; (equal (len keys) (len vals))
                  (symbol-listp keys)
                  (not (member nil keys)))
             (equal (mextract-ev-lst keys
                                     (append (pairlis$ keys vals)
                                             rest))
                    (take (len keys) vals)))
    :hints (("goal" :use ((:instance ev-lst-of-pairlis-append-head-rest
                           (head nil))))))


  (defthm ev-lst-of-pairlis
    (implies (and (no-duplicatesp keys)
; (true-listp vals)
; (equal (len keys) (len vals))
                  (symbol-listp keys)
                  (not (member nil keys)))
             (equal (mextract-ev-lst keys (pairlis$ keys vals))
                    (take (len keys) vals)))
    :hints (("goal" :use ((:instance ev-lst-of-pairlis-append-head-rest
                           (head nil) (rest nil))))))

  (defthm kwote-lst-of-take
    (implies (equal n (len args))
             (equal (kwote-lst (take n args))
                    (kwote-lst args)))))

(defthm len-of-mextract-ev-lst
  (equal (len (mextract-ev-lst x a))
         (len x)))

(local (defthm mextract-ev-match-tree
         (b* (((mv ok alist)
               (match-tree pat x alist)))
           (implies ok
                    (equal (mextract-ev x a)
                           (mextract-ev (subst-tree pat alist) a))))
         :hints(("Goal" :in-theory (enable match-tree-is-subst-tree)))))

(defthm mextract-ev-fn-get-def
  (b* (((mv ok formals body) (fn-get-def fn st)))
    (implies (and ok
                  (mextract-ev-global-facts)
                  (equal (w st) (w state))
                  (equal (len args) (len formals)))
             (equal (mextract-ev (cons fn args) a)
                    (mextract-ev body (pairlis$ formals
                                           (mextract-ev-lst args a))))))
  :hints(("Goal" :in-theory (e/d (mextract-ev-of-fncall-args)
                                 (mextract-formula
                                  meta-extract-global-fact+
                                  meta-extract-formula
                                  take))
          :use ((:instance mextract-formula
                 (name fn)
                 (acl2::st st)
                 (a (pairlis$ (mv-nth 1 (fn-get-def fn st))
                              (mextract-ev-lst args a))))))))

(in-theory (disable fn-get-def))

;; Checks that the function has the specified formals and body according to
;; fn-get-def.
(defun fn-check-def (fn state formals body)
  (declare (xargs :guard (symbolp fn)
                  :stobjs state))
  (b* (((mv ok fformals fbody) (fn-get-def fn state)))
    (and ok
         (equal fformals formals)
         (equal fbody body))))


(defthm fn-check-def-formals
  (implies (fn-check-def fn st formals body)
           (and (symbol-listp formals)
                (not (member nil formals))
                (no-duplicatesp formals))))

(defthm fn-check-def-not-quote
  (implies (fn-check-def fn st formals body)
           (not (equal fn 'quote)))
  :hints(("Goal" :in-theory (enable fn-get-def))))

(defthm mextract-ev-fn-check-def
  (implies (and (fn-check-def fn st formals body)
                (mextract-ev-global-facts)
                (equal (w st) (w state))
                (equal (len args) (len formals)))
           (equal (mextract-ev (cons fn args) a)
                  (mextract-ev body (pairlis$ formals
                                              (mextract-ev-lst args a)))))
  :hints(("Goal" :in-theory (disable meta-extract-global-fact+))))

(defthm fn-check-def-is-fn-get-def
  (b* (((mv ok formals body) (fn-get-def fn state)))
    (equal ok
           (fn-check-def fn state formals body)))
  :hints(("Goal" :in-theory (enable fn-get-def))))


(in-theory (disable fn-check-def))




;; Macro def-meta-extract proves the above theorems for any evaluator that
;; extends mextract-ev.
(defconst *def-meta-extract-events*
  '(encapsulate nil
     (local (in-theory nil))
     (def-ev-theoremp evfn)

     (defchoose evfn-meta-extract-contextual-badguy (obj) (a mfc state)
       (not (evfn (meta-extract-contextual-fact obj mfc state) a)))

     (defchoose evfn-meta-extract-global-badguy (obj st) (state)
       (not (evfn (meta-extract-global-fact+ obj st state)
                  (evfn-falsify (meta-extract-global-fact+ obj st state)))))

     (defthmd evfn-falsify-sufficient
       (implies (evfn x (evfn-falsify x))
                (evfn x a))
       :hints (("goal" :use evfn-falsify)))

     (defmacro evfn-meta-extract-contextual-facts (a &key (mfc 'mfc) (state 'state))
       `(evfn
         (meta-extract-contextual-fact
          (evfn-meta-extract-contextual-badguy ,a ,mfc ,state)
          ,mfc ,state)
         ,a))

     (defthmd evfn-meta-extract-contextual-badguy-sufficient
       (implies (evfn-meta-extract-contextual-facts a)
                (evfn (meta-extract-contextual-fact obj mfc state) a))
       :hints (("goal" :use evfn-meta-extract-contextual-badguy
                :in-theory (disable meta-extract-contextual-fact))))

     (defmacro evfn-meta-extract-global-facts (&key (state 'state))
       `(evfn
         (meta-extract-global-fact+
          (mv-nth 0 (evfn-meta-extract-global-badguy ,state))
          (mv-nth 1 (evfn-meta-extract-global-badguy ,state))
          ,state)
         (evfn-falsify
          (meta-extract-global-fact+
           (mv-nth 0 (evfn-meta-extract-global-badguy ,state))
           (mv-nth 1 (evfn-meta-extract-global-badguy ,state))
           ,state))))

     (defthmd evfn-meta-extract-global-badguy-sufficient
       (implies (evfn-meta-extract-global-facts)
                (evfn (meta-extract-global-fact+ obj st state) a))
       :hints (("goal" :use ((:instance evfn-meta-extract-global-badguy)
                             (:instance evfn-falsify
                              (x (meta-extract-global-fact+ obj st state))))
                :in-theory (disable meta-extract-global-fact))))

     (defthm evfn-meta-extract-global-badguy-true-listp
       (true-listp (evfn-meta-extract-global-badguy state))
       :hints (("goal" :use evfn-meta-extract-global-badguy))
       :rule-classes (:rewrite :type-prescription))

     (local (in-theory (enable evfn-meta-extract-global-badguy-sufficient
                               evfn-meta-extract-contextual-badguy-sufficient)))

     (local (in-theory (disable meta-extract-global-fact
                                meta-extract-contextual-fact)))

     (local
      (make-event
       (let ((rule (find-matching-rule
                    :dont-care :dont-care :dont-care
                    '(evfn (CONS (CAR X)
                                 (KWOTE-LST (evlst-fn (CDR X) A)))
                           'NIL)
                    (getprop 'evfn 'lemmas nil 'current-acl2-world (w state)))))
         (prog2$
          (or rule
              (er hard? 'def-meta-extract
                  "Couldn't find fncall on args rule for ~x0~%" 'evfn))
          `(add-default-hints
            '((and stable-under-simplificationp
                   '(:in-theory (enable ,rule
                                        evfn-falsify-sufficient)))))))))

     (local
      (make-event
       `(in-theory (enable
                    ,(ev-find-fncall-rule 'evfn 'typespec-check (w state))
                    ,(ev-find-fncall-rule 'evfn 'if (w state))
                    ,(ev-find-fncall-rule 'evfn 'equal (w state))
                    ,(ev-find-fncall-rule 'evfn 'not (w state))
                    ,(ev-find-fncall-rule 'evfn 'iff (w state))
                    ,(ev-find-fncall-rule 'evfn 'implies (w state))
                    ,(ev-lst-find-cons-rule 'evlst-fn (w state))
                    ,(ev-lst-find-atom-rule 'evlst-fn (w state))
                    ,(ev-find-quote-rule 'evfn (w state))
                    ,(ev-find-variable-rule 'evfn (w state))
                    ,(ev-find-lambda-rule 'evfn (w state))
                    ,(ev-find-nonsymbol-atom-rule 'evfn (w state))
                    ,(ev-find-bad-fncall-rule 'evfn (w state))))))

     (def-functional-instance
       evfn-meta-extract-typeset
       mextract-typeset
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-rw+-equal
       mextract-rw+-equal
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-rw+-iff
       mextract-rw+-iff
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-rw+-equiv
       mextract-rw+-equiv
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-rw-equal
       mextract-rw-equal
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-rw-iff
       mextract-rw-iff
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-rw-equiv
       mextract-rw-equiv
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-mfc-ap
       mextract-mfc-ap
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-relieve-hyp
       mextract-relieve-hyp
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-formula
       mextract-formula
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-lemma-term
       mextract-lemma-term
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-lemma
       mextract-lemma
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-fncall-logic
       mextract-fncall-logic
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-fncall
       mextract-fncall
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-magic-ev
       mextract-ev-magic-ev
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-meta-extract-magic-ev-lst
       mextract-ev-magic-ev-lst
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     ;; rewrite to fn-check-def now
     ;; (def-functional-instance
     ;;   evfn-fn-get-def
     ;;   mextract-ev-fn-get-def
     ;;   ((mextract-ev evfn)
     ;;    (mextract-ev-lst evlst-fn)
     ;;    (mextract-ev-falsify evfn-falsify)
     ;;    (mextract-global-badguy evfn-meta-extract-global-badguy)))

     (def-functional-instance
       evfn-meta-extract-fn-check-def
       mextract-ev-fn-check-def
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     ;; why not...
     (def-functional-instance
       evfn-lst-of-pairlis
       ev-lst-of-pairlis
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-lst-of-pairlis-append-rest
       ev-lst-of-pairlis-append-rest
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))

     (def-functional-instance
       evfn-lst-of-pairlis-append-head-rest
       ev-lst-of-pairlis-append-head-rest
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy))
       :translate nil
       :macro-subst ((mextract-ev-global-facts evfn-meta-extract-global-facts)
                     (mextract-ev-contextual-facts evfn-meta-extract-contextual-facts)))))

(defun meta-extract-replace-sym (from to x)
  (let* ((name (symbol-name x))
         (pos (search from name)))
    (if pos
        (let* ((pre (subseq name 0 pos))
               (post (subseq name (+ pos (length from)) nil)))
          (intern-in-package-of-symbol
           (concatenate 'string pre (symbol-name to) post)
           to))
      x)))

(mutual-recursion
 (defun meta-extract-replace-evfn (evfn evlst-fn x)
   (declare (xargs :mode :program))
   (if (atom x)
       (if (symbolp x)
           (meta-extract-replace-sym
            "EVLST-FN" evlst-fn
            (meta-extract-replace-sym
             "EVFN" evfn x))
         x)
     (meta-extract-replace-evfn-list evfn evlst-fn x)))
 (defun meta-extract-replace-evfn-list (evfn evlst-fn x)
   (if (atom x)
       nil
     (cons (meta-extract-replace-evfn evfn evlst-fn (car x))
           (meta-extract-replace-evfn-list evfn evlst-fn (cdr x))))))


(defmacro def-meta-extract (evfn evlst-fn)
  (meta-extract-replace-evfn evfn evlst-fn *def-meta-extract-events*))


(in-theory (disable meta-extract-contextual-fact
                    meta-extract-global-fact))



;; Now a couple of examples.


(local
 ;; This just localizes all the events in events and allows a name to be given
 (defmacro localize-example (name &rest events)
   `(encapsulate nil
      (value-triple ',name)
      (local
       (progn . ,events))
      (value-triple ',name))))




(local
 (localize-example
  using-typeset-and-type-alist

  (defthm nth-when-symbolp
    (implies (symbolp n)
             (equal (nth n x)
                    (car x)))
    :rule-classes nil)

  (defevaluator nthmeta-ev nthmeta-ev-lst
    ((typespec-check ts x)
     (if a b c)
     (equal a b)
     (not a)
     (iff a b)
     (implies a b)
     (nth n x)
     (car x))
    :namedp t)

  (def-meta-extract nthmeta-ev nthmeta-ev-lst)

  (defun nth-symbolp-metafn (term mfc state)
    (declare (xargs :stobjs state))
    (case-match term
      (('nth n x)
       (if (equal (mfc-ts n mfc state :forcep nil) *ts-symbol*)
           `(car ,x)
         (prog2$ (cw "Oops, the typeset of n is ~x0~%"
                     (mfc-ts n mfc state :forcep nil))
                 term)))
      (& term)))



  (defthm nth-symbolp-meta
    (implies (nthmeta-ev-meta-extract-contextual-facts a)
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (nth-symbolp-metafn term mfc state) a)))
    :hints (("goal" :use ((:instance nthmeta-ev-meta-extract-typeset
                           (term (cadr term))))
             :in-theory (disable nthmeta-ev-meta-extract-typeset)))
    :rule-classes ((:meta :trigger-fns (nth))))

  (defmacro nth-symbolp-test (n)
    `(encapsulate nil
       (local (progn

                (encapsulate
                  (((foo *) => *)
                   ((bar *) => *)
                   ((baz *) => *))


                  (local (defun foo (x) (declare (ignore x)) t))
                  (local (defun bar (x) (symbolp x)))
                  (local (defun baz (x) (symbolp x)))

                  (defthm foo-type
                    (symbolp (foo x))
                    :rule-classes :type-prescription)

                  (defthm bar-booleanp
                    (booleanp (bar x))
                    :rule-classes :type-prescription)

                  (defthm bar-implies-symbolp
                    (implies (bar x)
                             (symbolp x))
                    :rule-classes :compound-recognizer)

                  (defthm baz-implies-symbolp
                    (implies (baz x)
                             (symbolp x))
                    :rule-classes :forward-chaining))

                (make-event
                 (mv-let (erp val state)
                   (defthm nth-foo
                     (equal (nth (foo x) y)
                            (car y)))
                   (declare (ignore val))
                   (if erp
                       (prog2$ (cw "FOO failed~%")
                               (value '(value-triple ':foo-failed)))
                     (prog2$ (cw "FOO passed~%")
                             (value '(value-triple ':foo-passed))))))

                (make-event
                 (mv-let (erp val state)
                   (defthm nth-when-bar
                     (implies (Bar x)
                              (equal (nth x y)
                                     (car y))))
                   (declare (ignore val))
                   (if erp
                       (prog2$ (cw "BAR failed~%")
                               (value '(value-triple ':bar-failed)))
                     (prog2$ (cw "BAR passed~%")
                             (value '(value-triple ':bar-passed))))))


                (make-event
                 (mv-let (erp val state)
                   (defthm nth-when-baz
                     (implies (Baz x)
                              (equal (nth x y)
                                     (car y))))
                   (declare (ignore val))
                   (if erp
                       (prog2$ (cw "BAZ failed~%")
                               (value '(value-triple ':baz-failed)))
                     (prog2$ (cw "BAZ passed~%")
                             (value '(value-triple ':baz-passed))))))))
       (value-triple '(nth-symbol-test ,n))))

  (nth-symbolp-test 1)



  (defthm type-alistp-of-mfc-type-alist
    (type-alistp (mfc-type-alist mfc)))

  (in-theory (disable mfc-type-alist))

  (encapsulate nil
    (local (defthm alistp-when-type-alistp
             (implies (type-alistp x)
                      (alistp x))))
    (defthm alistp-of-mfc-type-alist
      (alistp (mfc-type-alist mfc))))

  (local (defthm assoc-equal-when-alistp
           (implies (alistp x)
                    (iff (consp (Assoc-equal a x))
                         (assoc-equal a x)))))

  (defthm cdr-assoc-equal-when-type-alistp
    (implies (type-alistp x)
             (iff (consp (cdr (assoc-equal a x)))
                  (assoc-equal a x))))

  (in-theory (disable nth nth-symbolp-meta))

  (nth-symbolp-test 2)))


(local
 (localize-example
  using-mfc-rw+

  (encapsulate
    (((foo *) => *)
     ((bar *) => *)
     ((baz *) => *))

    (set-ignore-ok t)
    (set-irrelevant-formals-ok t)
    (local (defun foo (x) nil))
    (local (defun bar (x) nil))
    (local (defun baz (x) nil))

    ;; Under (bar ...) context, (foo x) is equivalent to x.
    (defthm bar-of-foo
      (equal (bar (foo x))
             (bar x)))

    ;; Under (foo ...) context, (baz x) is equivalent to x.
    (defthm foo-of-baz
      (equal (foo (baz x))
             (foo x))))

  ;; The above constraints imply that under BAR context, (baz x) is equivalent
  ;; to x, since:
  ;; (bar (baz x))       => (bar (foo (baz x))) by bar-of-foo (reversed)
  ;; (bar (foo (baz x))) => (bar (foo x))       by foo-of-baz
  ;; (bar (foo x))       => (bar x)             by bar-of-foo.
  ;; But because the top one uses bar-of-foo reversed, ACL2 can't prove this:
  (make-event
   (b* (((mv erp & state)
         (defthm bar-of-baz-fails
           (equal (bar (baz x))
                  (bar x)))))
     (if erp
         (value '(value-triple :failed))
       (er soft 'bar-of-baz-fails "Proof unexpectedly succeeded"))))

  (defevaluator foobar-ev foobar-ev-lst
    ((typespec-check ts x)
     (if a b c)
     (equal a b)
     (not a)
     (iff a b)
     (implies a b)
     (foo x)
     (bar x))
    :namedp t)

  (def-meta-extract foobar-ev foobar-ev-lst)

  ;; This meta rule only knows basically that a BAR context induces a FOO
  ;; context, because (bar (foo x)) = (bar x).  In particular it cares nothing
  ;; about baz.
  (defun reduce-bar-with-foo (x mfc state)
    (declare (xargs :stobjs state))
    (case-match x
      (('bar xx . &)
       (let* ((xxx (case-match xx
                     (('foo xxx . &)
                      (prog2$ (cw "note: reduce-bar-with-foo caught xx not in ~
                                 normal form: ~x0~%" xx)
                              xxx))
                     (& xx)))
              (foo-xxx-rw (mfc-rw+ '(foo xxx)
                                   `((xxx . ,xxx))
                                   '? nil mfc state :forcep nil))
              (y (case-match foo-xxx-rw
                   (('foo y . &) y)
                   (& foo-xxx-rw))))
         `(bar ,y)))
      (& x)))

  (encapsulate nil
    (local (defthm bar-of-foo-free
             (implies (equal x (foo y))
                      (equal (bar x)
                             (bar y)))))

    ;; Note: even with bar-of-foo-free, this isn't proved
    (make-event
     (b* (((mv erp & state)
           (defthm bar-of-baz-fails
             (equal (bar (baz x))
                    (bar x)))))
       (if erp
           (value '(value-triple :failed))
         (er soft 'bar-of-baz-fails "Proof unexpectedly succeeded"))))

    (defthm reduce-bar-with-foo-meta
      (implies (foobar-ev-meta-extract-contextual-facts a)
               (equal (foobar-ev x a)
                      (foobar-ev (reduce-bar-with-foo x mfc state) a)))
      :hints (("goal" :use ((:instance FOOBAR-EV-META-EXTRACT-RW+-EQUAL
                             (term '(foo xxx))
                             (alist (let ((xx (cadr x)))
                                      `((xxx . ,(case-match xx
                                                  (('foo xxx . &) xxx)
                                                  (& xx))))))
                             (obj '?))
                            (:instance bar-of-foo
                             (x (foobar-ev (let ((xx (cadr x)))
                                             (case-match xx
                                               (('foo xxx . &) xxx)
                                               (& xx)))
                                           a))))
               :in-theory (e/d (sublis-var)
                               (foobar-ev-meta-extract-rw+-equal
                                bar-of-foo))))
      :rule-classes ((:meta :trigger-fns (bar)))))

  (defthm bar-of-baz
    (equal (bar (baz x))
           (bar x)))))




;; Allows use of meta-extract-formula with just the world.  You still need
;; state in the theorems (and to know that wrld = (w state)).
(defund meta-extract-formula-w (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (or (getprop name 'theorem nil 'current-acl2-world wrld)
      (cond ((logicp name wrld)
             (mv-let (flg prop)
               (constraint-info name wrld)
               (cond ((unknown-constraints-p prop)
                      *t*)
                     (flg (ec-call (conjoin prop)))
                     (t prop))))
            (t *t*))))

(defthm meta-extract-formula-w-rewrite
  (equal (meta-extract-formula-w name (w state))
         (meta-extract-formula name state))
  :hints(("Goal" :in-theory (enable meta-extract-formula-w
                                    meta-extract-formula))))

(defund fn-get-def-w (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (b* (((when (eq fn 'quote))
        (mv nil nil nil))
       (formula (meta-extract-formula-w fn wrld))
       ((unless-match formula (equal ((:! fn) . (:? formals)) (:? body)))
        (mv nil nil nil))
       ((unless (and (symbol-listp formals)
                     (not (member-eq nil formals))
                     (no-duplicatesp-eq formals)))
        (mv nil nil nil)))
    (mv t formals body)))

(defthm fn-get-def-w-rewrite
  (equal (fn-get-def-w name (w state))
         (fn-get-def name state))
  :hints(("Goal" :in-theory (enable fn-get-def fn-get-def-w))))

(defund fn-check-def-w (fn wrld formals body)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (b* (((mv ok fformals fbody) (fn-get-def-w fn wrld)))
    (and ok
         (equal fformals formals)
         (equal fbody body))))

(defthm fn-check-def-w-rewrite
  (equal (fn-check-def-w name (w state) formals body)
         (fn-check-def name state formals body))
  :hints(("Goal" :in-theory (enable fn-check-def fn-check-def-w))))



(local
 (localize-example
  using-fncall

  (defevaluator fnc-ev fnc-ev-lst
    ((typespec-check ts x)
     (if a b c)
     (equal a b)
     (not a)
     (iff a b)
     (implies a b)))

  (defun unquote-lst (x)
    (declare (xargs :guard (and (pseudo-term-listp x)
                                (quote-listp x))))
    (if (atom x)
        nil
      (cons (unquote (car x))
            (unquote-lst (cdr x)))))

  (defthm kwote-lst-of-unquote-lst-when-quote-listp
    (implies (and (quote-listp x)
                  (pseudo-term-listp x))
             (equal (kwote-lst (unquote-lst x))
                    x)))

  (defthm fnc-ev-list-when-quote-listp
    (implies (quote-listp x)
             (equal (fnc-ev-lst x a)
                    (unquote-lst x))))

  ;; Dumb metafunction that evaluates a function call.
  (defun ev-call-metafn (x mfc state)
    (declare (xargs :guard (pseudo-termp x)
                    :stobjs state)
             (ignorable mfc))
    (if (and (consp x)
             (symbolp (car x))
             (not (eq (car x) 'quote))
             (quote-listp (cdr x))
             (mbt (pseudo-term-listp (cdr x))))
        (mv-let (erp val)
          (magic-ev-fncall-logic (car x) (unquote-lst (cdr x)) state)
          (if erp
              x
            (kwote val)))
      x))

  (def-meta-extract fnc-ev fnc-ev-lst)

  (defthm ev-call-metafn-correct
    (implies (fnc-ev-meta-extract-global-facts)
             (equal (fnc-ev (ev-call-metafn x mfc state) a)
                    (fnc-ev x a)))
    :hints(("Goal"
            ;; :use ((:instance fnc-ev-meta-extract-fncall-logic
            ;;        (fn (car x))
            ;;        (arglist (unquote-lst (cdr x)))
            ;;        (st state)))
            :in-theory (enable fnc-ev-constraint-0))))


  (defun fib (x)
    (if (or (zp x) (eql x 1))
        1
      (+ (fib (- x 1))
         (fib (- x 2)))))

  (in-theory (disable fib (fib)))

  (defun fib-hyp-metafn (x mfc state)
    (declare (xargs :guard (pseudo-termp x)
                    :stobjs state)
             (ignorable mfc state))
    (if (and (consp x)
             (eq (car x) 'fib)
             (quotep (cadr x))
             (< (nfix (cadr (cadr x))) 10))
        *t*
      *nil*))

  (defthm ev-call-metafn-for-fib
    (implies (and (fnc-ev-meta-extract-global-facts)
                  (fnc-ev (fib-hyp-metafn x mfc state) a))
             (equal (fnc-ev x a)
                    (fnc-ev (ev-call-metafn x mfc state) a)))
    :hints(("Goal" :in-theory (disable ev-call-metafn)))
    :rule-classes ((:meta :trigger-fns (fib))))

  ;; this fails:
  ;; (defthm fib-20
  ;;   (equal (fib 20) 10946))

  (defthm fib-9
    (equal (fib 9) 55))))

;; The following is for reference by the xdoc:
(defevaluator mx-ev mx-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)))

(defxdoc magic-ev
  :parents (meta)
  :short "Evaluate a term under a ground substitution using @(see magic-ev-fncall)."
  :long "<p>Invocation:</p>
@({
 (magic-ev term alist state hard-error-returns-nilp aokp)
 })

<p>evaluates the given term under the alist mapping variables to values.
Functions within the term are evaluated using @(see magic-ev-fncall) and the
values returned are the same as for @(see magic-ev-fncall), that is,</p>
@({
 (mv NIL value)
 })
<p>on success or</p>
@({
 (mv T error-msg)
 })
<p>on failure.</p>")

(defxdoc magic-ev-lst
  :parents (magic-ev)
  :short "Evaluate a list of terms using @(see magic-ev).")

(defxdoc fn-get-def
  :parents (meta-extract)
  :short "Look up a function's definition from the world."
  :long "<p>Invocation:</p>
@({
 (fn-get-def fnname state)
 })
<p>or equivalently,if @('world') is @('(w state)'),</p>
@({
 (fn-get-def-w fnname world)
 })

<p>produces @('(mv successp formals body)'), where if @('successp') is true,
then @('(fnname . formals)') is equal to @('body') under evaluation.</p>

<p>@('fn-get-def') can be assumed to work correctly in the context of
metafunctions and clause processors via @(see meta-extract).</p>

<p>The @(see def-meta-extract) macro supports @('fn-get-def') indirectly: we
rewrite the @('successp') return value to a call of @('fn-check-def'), and
@('def-meta-extract') provides a theorem that rewrites an evaluation of
@('(fnname . args)') to the evaluation of @('body') under the pairing of
@('formals') to @('args') when it can relieve the hypothesis</p>
@({
 (fn-check-def fnname state formals body).
 })")

(defpointer fn-check-def fn-get-def)




(local
 ;; Set up a custom untranslate so that the xdoc will show the
 ;; mx-ev-meta-extract macros rather than their expanded forms.
 (progn
   (make-event
    (let ((curr-preprocess (cdr (assoc 'untranslate-preprocess
                                       (table-alist 'user-defined-functions-table (w state))))))
      `(defun my-preprocess (term wrld)
         (declare (ignorable wrld)
                  (xargs :mode :program))
         (cond ((equal term '(MX-EV
                              (META-EXTRACT-GLOBAL-FACT+ (MV-NTH '0
                                                                 (MX-EV-META-EXTRACT-GLOBAL-BADGUY STATE))
                                                         (MV-NTH '1
                                                                 (MX-EV-META-EXTRACT-GLOBAL-BADGUY STATE))
                                                         STATE)
                              (MX-EV-FALSIFY (META-EXTRACT-GLOBAL-FACT+
                                              (MV-NTH '0
                                                      (MX-EV-META-EXTRACT-GLOBAL-BADGUY STATE))
                                              (MV-NTH '1
                                                      (MX-EV-META-EXTRACT-GLOBAL-BADGUY STATE))
                                              STATE))))
                '(mx-ev-meta-extract-global-facts))
               ((equal term '(MX-EV (META-EXTRACT-CONTEXTUAL-FACT
                                     (MX-EV-META-EXTRACT-CONTEXTUAL-BADGUY A MFC STATE)
                                     MFC STATE)
                                    A))
                '(mx-ev-meta-extract-contextual-facts a))
               ((and (consp term)
                     (equal (car term) '(LAMBDA (X L)
                                                (RETURN-LAST 'MBE1-RAW
                                                             (MEMBER-EQL-EXEC X L)
                                                             (RETURN-LAST 'PROGN
                                                                          (MEMBER-EQL-EXEC$GUARD-CHECK X L)
                                                                          (MEMBER-EQUAL X L))))))
                (cons 'member (cdr term)))
               ((and (consp term)
                     (equal (car term) '(LAMBDA (X)
                                                (RETURN-LAST 'MBE1-RAW
                                                             (NO-DUPLICATESP-EQL-EXEC X)
                                                             (RETURN-LAST 'PROGN
                                                                          (NO-DUPLICATESP-EQL-EXEC$GUARD-CHECK X)
                                                                          (NO-DUPLICATESP-EQUAL X))))))
                (cons 'no-duplicatesp (cdr term)))
               (t ,(if curr-preprocess
                       `(,curr-preprocess term wrld)
                     'term))))))
   (table user-defined-functions-table 'untranslate-preprocess 'my-preprocess)))

(def-meta-extract mx-ev mx-ev-lst)

(defxdoc def-meta-extract
  :parents (meta-extract)
  :short "Generate macros and theorems convenient for using @(see meta-extract) with a given evaluator."
  :long "<p>Using the @(see meta-extract) feature in proofs of meta rules and
clause processors is fairly inconvenient when starting from scratch.
Def-meta-extract generates a set of theorems for a given evaluator that are
a more convenient starting point for reasoning about meta-extract.</p>

<p>Usage:</p>

@({
 (defevaluator mx-ev mx-ev-lst
   ((typespec-check ts x)
    (if a b c)
    (equal a b)
    (not a)
    (iff a b)
    (implies a b)
    ...))   ;; other functions as needed for the application

 (def-meta-extract mx-ev mx-ev-lst)
 })

<p>We will use the above invocation on @('mx-ev') as an example;
@('def-meta-extract') should be applicable to any evaluator that supports the
six functions listed in the defevaluator form above.</p>

<p>The above invocation of @('def-meta-extract') produces two macros that
expand to well-formed meta-extract hypotheses:</p>
@({
 (mx-ev-meta-extract-contextual-facts a :mfc mfc :state state)
 (mx-ev-meta-extract-global-facts :state state)
 })
<p>(Note: The keyword arguments listed default to the variable names @('mfc')
and @('state'), which are usually the right arguments.)</p>

<p>The exact meta-extract hypotheses produced use a bad-guy function as the
@('obj') argument to the meta-extract function, and for the global macro, for
the @('st') argument to @('meta-extract-global-fact+'), so that they
effectively universally quantify them, as shown by the following two theorems:</p>
@(def mx-ev-meta-extract-contextual-badguy-sufficient)
@(def mx-ev-meta-extract-global-badguy-sufficient)

<p>However, @('def-meta-extract') proves several theorems for the given
evaluator so that the user doesn't need to reason directly about invocations of
@(see meta-extract-contextual-fact) and @(see meta-extract-global-fact+).  For
example, to show that an invocation of @('meta-extract-formula') is true under
@('mx-ev'), you could prove:</p>
@({
  (implies (and (mx-ev (meta-extract-global-fact+ (list :formula name) st state) a)
                (equal (w st) (w state)))
           (mx-ev (meta-extract-formula name st) a))
})
<p>But the following theorem proved by @('def-meta-extract') obviates the need
to reason directly about @(see meta-extract-global-fact+) and provide the correct
@('obj = (list :formula name)') in this manner:</p>
@({
  (implies (and (mx-ev-meta-extract-global-facts)
                (equal (w st) (w state)))
           (mx-ev (meta-extract-formula name st) a))
 })

<p>(Note: @('st'), the state from which the formula is extracted, and
@('state'), the original state on which the metafunction or clause processor
was invoked, may differ in the case of a clause processor because the clause
processor can update state.  As long as the @('w') field (holding the ACL2
logical world) of the state is not updated, global facts can still be extracted
from the state and assumed correct.)</p>

<h3>List of theorems proved by @('def-meta-extract')</h3>

<h4>Typset reasoning with @(see mfc-ts)</h4>
<p>The following theorem allows the user to conclude that a typeset returned by
@(see mfc-ts) correctly describes the type of a term:</p>
@(def mx-ev-meta-extract-typeset)

<h4>Rewriting with @(see mfc-rw) and under substitution with @(see mfc-rw+)</h4>
<p>The following six theorems allow the user to conclude that a call of @(see
mfc-rw) returns an equivalent term, or that a call of @(see mfc-rw+) returns a
term equivalent to the substitution of @('alist') into @('term'), with the
equivalence given by the @('equiv-info') argument provided (@('nil') for
equality, @('t') for @('iff'), or the name of an equivalence relation):</p>
@(def mx-ev-meta-extract-rw-equal)
@(def mx-ev-meta-extract-rw-iff)
@(def mx-ev-meta-extract-rw-equiv)
@(def mx-ev-meta-extract-rw+-equal)
@(def mx-ev-meta-extract-rw+-iff)
@(def mx-ev-meta-extract-rw+-equiv)

<h4>Detecting linear arithmetic contradictions with @(see mfc-ap)</h4>
<p>The following theorem allows the user to conclude that a term is false under
the given environment @('a') when @(see mfc-ap) returns @('t') indicating a
linear arithmetic contradiction:</p>
@(def mx-ev-meta-extract-mfc-ap)

<h4>Proving terms true with @(see mfc-relieve-hyp)</h4>
@(def mx-ev-meta-extract-relieve-hyp)

<h4>Looking up formulas by name using @(see meta-extract-formula)</h4>
<p>(Note: @('meta-extract-formula') can be used to look up a theorem,
definition of a defined function, or constraint of a constrained function.)</p>
@(def mx-ev-meta-extract-formula)

<h4>Looking up rewrite rules from a @('lemmas') property</h4>
<p>The following two theorems conclude that a rewrite rule extracted from a
function's @('lemmas') property is valid (the second somewhat more explicitly
than the first):</p>
@(def mx-ev-meta-extract-lemma-term)
@(def mx-ev-meta-extract-lemma)

<h4>Calling a function with @(see magic-ev-fncall)</h4>
@(def mx-ev-meta-extract-fncall)

<h4>Evaluating a term with @(see magic-ev) or termlist with @(see magic-ev-lst)</h4>
@(def mx-ev-meta-extract-magic-ev)
@(def mx-ev-meta-extract-magic-ev-lst)

<h4>Looking up a function definition with @(see fn-get-def)</h4>
<p>The following theorem allows a function call to be expaneded to its body
when the function definition is successfully looked up in the world with @(see
fn-get-def).  Note: The term @('(mv-nth 0 (fn-get-def ...))') indicating
success of the @(see fn-get-def) call is rewritten to the call of @(see
fn-check-def):</p>
@(def mx-ev-meta-extract-fn-check-def)

<h4>Technical lemmas about pairing formals with actuals</h4>
<p>The following three theorems may help in reasoning about expansions of
function calls and lambdas:</p>
@(def mx-ev-lst-of-pairlis)
@(def mx-ev-lst-of-pairlis-append-rest)
@(def mx-ev-lst-of-pairlis-append-head-rest)")
