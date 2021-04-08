; Clause processor that implements rewrite rules that have a variable as the LHS.

; Copyright (C) 2013 Centaur Technology
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

(include-book "std/util/bstar" :dir :system)
(include-book "meta-extract-user")
(include-book "unify-subst")

; (Matt K.) I've added the following verify-termination form so that
; dumb-negate-lit is in :logic mode (as required by the present book) when
; using an ACL2 image built with ACL2_DEVEL=d.  But Sol Swords asked if this is
; actually necessary, and indeed it seems not to be: All that is required is to
; be able to certify books under with ACL2_DEVEL=d that are keys of ACL2
; constant *system-verify-guards-alist*.  However, at this point it seems
; simplest to leave this form in place.
(verify-termination dumb-negate-lit) ; and guards

(local (in-theory (disable w)))

(defevaluator repl-ev repl-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)
   (cons a b)
   (binary-+ a b))
  :namedp t)

(def-meta-extract repl-ev repl-ev-lst)
(def-unify repl-ev repl-ev-alist)

;; REPL-EV-EQUALITY-ALIST-P: Alist that binds equal terms to each other.
(defun repl-ev-equality-alist-p (x a)
  (declare (xargs :guard (and (alistp x)
                              (alistp a))))
  (if (atom x)
      t
    (and (equal (repl-ev (caar x) a)
                (repl-ev (cdar x) a))
         (repl-ev-equality-alist-p (cdr x) a))))

(defthm assoc-in-repl-ev-equality-alist
  (implies (and (repl-ev-equality-alist-p x a)
                (assoc-equal term x))
           (equal (repl-ev term a)
                  (repl-ev (cdr (assoc-equal term x)) a))))



(defsection subst-subterms
  ;; SUBST-SUBTERMS: Substitute equal subterms within a term.

  (mutual-recursion
   (defun subst-subterms (x alist)
     (declare (xargs :guard (and (pseudo-termp x)
                                 (alistp alist))))
     (b* ((look (assoc-equal x alist))
          ((when look) (cdr look))
          ((when (or (variablep x) (fquotep x))) x))
       (cons (car x) (subst-subterms-list (cdr x) alist))))
   (defun subst-subterms-list (x alist)
     (declare (xargs :guard (and (pseudo-term-listp x)
                                 (alistp alist))))
     (if (atom x)
         nil
       (cons (subst-subterms (car x) alist)
             (subst-subterms-list (cdr x) alist)))))

  (in-theory (disable subst-subterms subst-subterms-list))
  (local (in-theory (enable subst-subterms subst-subterms-list)))

  (flag::make-flag subst-subterms-flag subst-subterms
                   :flag-mapping ((subst-subterms term)
                                  (subst-subterms-list list)))

  (defthm len-subst-subterms-list
    (equal (len (subst-subterms-list x alist))
           (len x)))

  (defthm-subst-subterms-flag
    (defthm pseudo-termp-subst-subterms
      (implies (and (pseudo-termp x)
                    (pseudo-term-val-alistp alist))
               (pseudo-termp (subst-subterms x alist)))
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (a b)
                               (pseudo-termp (cons a b)))))))
      :flag term)
    (defthm pseudo-term-listp-subst-subterms-list
      (implies (and (pseudo-term-listp x)
                    (pseudo-term-val-alistp alist))
               (pseudo-term-listp (subst-subterms-list x alist)))
      :flag list))

  (defthm-subst-subterms-flag
    (defthm subst-subterms-correct
      (implies (repl-ev-equality-alist-p alist a)
               (equal (repl-ev (subst-subterms x alist) a)
                      (repl-ev x a)))
      :hints('(:in-theory (enable repl-ev-of-fncall-args)))
      :flag term)
    (defthm subst-subterms-list-correct
      (implies (repl-ev-equality-alist-p alist a)
               (equal (repl-ev-lst (subst-subterms-list x alist) a)
                      (repl-ev-lst x a)))
      :flag list))

  (defthm disjoin-subst-subterms-list-correct
    (implies (repl-ev-equality-alist-p alist a)
             (iff (repl-ev (disjoin (subst-subterms-list x alist)) a)
                  (repl-ev (disjoin x) a)))
    :hints (("goal" :induct (len x)
             :in-theory (e/d (repl-ev-disjoin-when-consp))))))



(local (defthm match-tree-pseudo-termp
         (b* (((mv ok subst) (match-tree pat x alist)))
           (implies ok
                    (equal (pseudo-termp x)
                           (pseudo-termp (subst-tree pat subst)))))
         :hints(("Goal" :in-theory (enable match-tree-is-subst-tree)))))


(defsection unify-lit-with-equality-rule

  (local (def-match-tree-rewrites (implies (:? hyp-term)
                                           (equal (:? lhs)
                                                  (:? rhs)))))

  (defund unify-lit-with-equality-rule (lit rule)
    (declare (xargs :guard (and (pseudo-termp lit)
                                (pseudo-termp rule))))
    (b* (((unless-match rule (implies (:? hyp-term)
                                      (equal (:? lhs)
                                             (:? rhs))))
          (mv nil nil))
         ((when (or (atom hyp-term)
                    (eq (car hyp-term) 'if)))
          (mv nil nil))
         ((mv ok subst) (simple-one-way-unify hyp-term lit nil))
         ((unless ok)
          (mv nil nil)))
      (mv t (cons (substitute-into-term lhs subst)
                  (substitute-into-term rhs subst)))))

  (local (in-theory (enable unify-lit-with-equality-rule)))

  (defthm unify-lit-with-equality-rule-cdr-pseudo-termp
    (implies (and (pseudo-termp lit)
                  (pseudo-termp rule))
             (pseudo-termp (cdr (mv-nth 1 (unify-lit-with-equality-rule lit
                                                                        rule))))))

  (local (defthm match-tree-repl-ev
           (b* (((mv ok subst) (match-tree pat x alist)))
             (implies ok
                      (equal (repl-ev x a)
                             (repl-ev (subst-tree pat subst) a))))
           :hints(("Goal" :in-theory (enable match-tree-is-subst-tree)))))

  (defthm unify-lit-with-equality-rule-consp
    (b* (((mv ok pair) (unify-lit-with-equality-rule lit rule)))
      (implies ok (consp pair))))

  (defthm unify-lit-with-equality-rule-correct
    (b* (((mv ok (cons lhs rhs)) (unify-lit-with-equality-rule lit rule)))
      (implies (and ok
                    (repl-ev-theoremp rule)
                    (pseudo-termp lit)
                    (pseudo-termp rule)
                    (repl-ev lit a))
               (equal (repl-ev lhs a)
                      (repl-ev rhs a))))
    :hints (("goal" :use ((:instance repl-ev-falsify
                           (x rule)
                           (a (repl-ev-alist
                               (mv-nth 1 (simple-one-way-unify
                                          (hyp-term rule) lit nil))
                               a))))))))


(defsection lit-get-equality-rules

  (defund lit-get-equality-rules (lit rules w)
    (declare (xargs :guard (and (pseudo-termp lit)
                                (symbol-listp rules)
                                (plist-worldp w))))
    (b* (((when (atom rules)) nil)
         (rulename (car rules))
         (rule (meta-extract-formula-w rulename w))
         ((unless (pseudo-termp rule))
          (lit-get-equality-rules lit (cdr rules) w))
         ((mv ok pair) (unify-lit-with-equality-rule lit rule)))
      (if ok
          (cons pair (lit-get-equality-rules lit (cdr rules) w))
        (lit-get-equality-rules lit (cdr rules) w))))

  (local (in-theory (enable lit-get-equality-rules)))

  (defthm alistp-lit-get-equality-rules
    (alistp (lit-get-equality-rules lit rules w)))

  (defthm pseudo-term-val-alistp-lit-get-equality-rules
    (implies (pseudo-termp lit)
             (pseudo-term-val-alistp
              (lit-get-equality-rules lit rules w)))
    :hints(("Goal" :in-theory (enable pseudo-term-val-alistp))))

  (defthm repl-ev-equality-alist-p-lit-get-equality-rules
    (implies (and (repl-ev-meta-extract-global-facts)
                  (equal (w st) (w state))
                  (repl-ev lit a)
                  (pseudo-termp lit))
             (repl-ev-equality-alist-p
              (lit-get-equality-rules lit rules (w st)) a))))

(defthm repl-ev-of-disjoin-revappend
  (iff (repl-ev (disjoin (revappend x y)) a)
       (or (repl-ev (disjoin x) a)
           (repl-ev (disjoin y) a))))


(defsection dumb-negate-lit
  (in-theory (disable dumb-negate-lit))
  (local (in-theory (enable dumb-negate-lit)))

  (defthm repl-ev-dumb-negate-lit
    (implies (pseudo-termp x)
             (iff (repl-ev (dumb-negate-lit x) a)
                  (not (repl-ev x a)))))

  (defthm pseudo-termp-dumb-negate-lit
    (implies (pseudo-termp lit)
             (pseudo-termp (dumb-negate-lit lit)))
    :hints(("Goal" :in-theory (enable pseudo-termp
                                      pseudo-term-listp)))))

(defsection remove-non-symbols
  (defund remove-non-symbols (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (symbolp (car x))
          (cons (car x) (remove-non-symbols (cdr x)))
        (remove-non-symbols (cdr x)))))

  (local (in-theory (enable remove-non-symbols)))

  (defthm symbol-listp-remove-non-symbols
    (symbol-listp (remove-non-symbols x)))

  (defthm remove-non-symbols-when-symbol-listp
    (implies (symbol-listp x)
             (equal (remove-non-symbols x) x))))

(defsection remove-non-symbol-pairs
  (defund remove-non-symbol-pairs (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (and (consp (car x))
               (symbolp (caar x)))
          (cons (car x) (remove-non-symbol-pairs (cdr x)))
        (remove-non-symbol-pairs (cdr x)))))

  (local (in-theory (enable remove-non-symbol-pairs)))

  (defthm symbol-alistp-remove-non-symbol-pairs
    (symbol-alistp (remove-non-symbol-pairs x)))

  (defthm remove-non-symbol-pairs-when-symbol-alistp
    (implies (symbol-alistp x)
             (equal (remove-non-symbol-pairs x) x))))



(defsection replace-equalities-iter

  (defund replace-equalities-iter (tail head ruletable w)
    (declare (xargs :guard (and (pseudo-term-listp tail)
                                (pseudo-term-listp head)
                                (symbol-alistp ruletable)
                                (plist-worldp w))
                    :measure (len tail)))
    (b* (((when (atom tail))
          (revappend head nil))
         ((cons lit rest) tail)
         (nlit (dumb-negate-lit lit))
         ((unless (and (consp nlit)
                       (symbolp (car nlit))
                       (not (eq (car nlit) 'quote))))
          (replace-equalities-iter rest (cons lit head) ruletable w))
         (rules (cdr (assoc (car nlit) ruletable)))
         (rules (mbe :logic (remove-non-symbols rules)
                     :exec (if (symbol-listp rules)
                               rules
                             (remove-non-symbols rules))))
         (subst (lit-get-equality-rules nlit rules w))
         (rest (subst-subterms-list rest subst))
         (head (subst-subterms-list head subst)))
      (replace-equalities-iter rest (cons lit head) ruletable w)))

  (local (in-theory (enable replace-equalities-iter)))

  (defthm pseudo-term-listp-revappend
    (implies (and (pseudo-term-listp x)
                  (pseudo-term-listp y))
             (pseudo-term-listp (revappend x y))))

  (defthm pseudo-term-listp-replace-equalities-iter
    (implies (and (pseudo-term-listp tail)
                  (pseudo-term-listp head))
             (pseudo-term-listp (replace-equalities-iter tail head ruletable
                                                         w))))

  (defthm replace-equalities-iter-correct
    (implies (and (repl-ev-meta-extract-global-facts)
                  (equal (w st) (w state))
                  (not (repl-ev (disjoin tail) a))
                  (not (repl-ev (disjoin head) a))
                  (pseudo-term-listp tail))
             (not (repl-ev (disjoin (replace-equalities-iter
                                     tail head ruletable (w st)))
                           a)))
    :hints(("Goal" :in-theory (enable repl-ev-disjoin-when-consp)))))


(defsection replace-equalities-cp

  (defund replace-equalities-cp (clause hints state)
    (declare (xargs :stobjs state
                    :guard (pseudo-term-listp clause)
                    :guard-hints (("goal" :in-theory (enable w))))
             (ignorable hints))
    (b* ((w (w state))
         (ruletable (table-alist 'replace-equalities-rules w))
         (ruletable (mbe :logic (remove-non-symbol-pairs ruletable)
                         :exec (if (symbol-alistp ruletable)
                                   ruletable
                                 (remove-non-symbol-pairs ruletable)))))
      (mv nil (list (replace-equalities-iter clause nil ruletable w)))))

  (local (in-theory (enable replace-equalities-cp)))

  (defthm replace-equalities-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (repl-ev-meta-extract-global-facts)
                  (repl-ev (conjoin-clauses
                            (clauses-result
                             (replace-equalities-cp clause hints state)))
                           a))
             (repl-ev (disjoin clause) a))
    :rule-classes :clause-processor))



;; NOTE: We define this in match-tree.lisp instead of here for a dumb sort of
;; reason:  we want to use it in def-match-tree-rewrites.
;; (defun replace-equalities-thm-fnsym (thmname w)
;;   (declare (xargs :guard (and (symbolp thmname)
;;                               (plist-worldp w))))
;;   (b* (((unless-match (meta-extract-formula-w thmname w)
;;                       (implies ((:?f hyp-sym) . (:? hyp-args))
;;                                (equal (:? lhs)
;;                                       (:? rhs))))
;;         (er hard? 'add-replace-equalities-rule
;;             "Theorem ~x0 not of the right form") thmname))
;;     hyp-sym))

;; (defmacro add-replace-equalities-rule (thmname)
;;   `(table replace-equalities-rules
;;           (replace-equalities-thm-fnsym ',thmname world)
;;           (cons ',thmname
;;                 (cdr (assoc (replace-equalities-thm-fnsym ',thmname world)
;;                             (table-alist 'replace-equalities-rules world))))))


;; NOTE: This is mostly an example of usage, but is also pretty useful so we'll
;; leave it non-local.

;; This is the replacement we generally want to make...
(defthm match-tree-replace-equalities
  (implies (mv-nth 0 (match-tree pat x alist))
           (equal x
                  (subst-tree pat (mv-nth 1 (match-tree pat x alist)))))
  :hints(("Goal" :in-theory (enable match-tree-is-subst-tree)))
  :rule-classes nil)

;; But we don't want to replace occurrences of X inside the match-tree-term
;; itself!  This will block subst-subterms from doing so.
(defthm match-tree-block-self-subst
  (implies (mv-nth 0 (match-tree pat x alist))
           (equal (match-tree pat x alist)
                  (match-tree pat x alist)))
  :rule-classes nil)

(add-replace-equalities-rule match-tree-replace-equalities)
(add-replace-equalities-rule match-tree-block-self-subst)



(local
 (progn
   (in-theory (disable match-tree-pseudo-termp))

   (defthm foo
     (mv-let (ok alist)
       (match-tree '(implies ((:?f hyp-sym) . (:? hyp-args))
                             (equal (:? lhs)
                                    (:? rhs)))
                   rule nil)
       (implies ok
                (iff (pseudo-termp rule)
                     (and (pseudo-term-listp (cdr (assoc 'hyp-args alist)))
                          (pseudo-termp (cdr (assoc 'lhs alist)))
                          (pseudo-termp (cdr (assoc 'rhs alist)))))))
     :hints ((and stable-under-simplificationp
                  '(:clause-processor (replace-equalities-cp clause nil state)))))))

