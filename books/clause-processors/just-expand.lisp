; Copyright (C) 2012 Centaur Technology
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
(include-book "unify-subst")
(include-book "meta-extract-user")
(include-book "std/util/bstar" :dir :system)
(include-book "ev-theoremp")
(include-book "use-by-hint")
(include-book "std/lists/butlast" :dir :system)

(in-theory (disable butlast))


(defund expand-me (x)
  (declare (xargs :Guard t))
  x)
(in-theory (disable (expand-me) (:t expand-me)))

(defund expand-me-with (rule x)
  (declare (xargs :guard t)
           (ignore rule))
  x)
(in-theory (disable (expand-me-with) (:t expand-me-with)))

(defevaluator expev expev-lst
  ((if a b c) (equal a b) (not a) (use-by-hint a)
   (cons a b) (binary-+ a b)
   (typespec-check ts x)
   (iff a b)
   (implies a b)
   (expand-me x)
   (expand-me-with rule x))
  :namedp t)

(def-ev-theoremp expev)
(def-meta-extract expev expev-lst)
(def-unify expev expev-alist)

(local (in-theory (disable w)))

(local (defthm expev-alist-of-pairlis$
         (equal (expev-alist (pairlis$ x y) a)
                (pairlis$ x (expev-lst y a)))))

(defsection expand-this-term
  (defund expand-this-term (x explicit-rule w)
    "returns (mv successp x1)"
    (declare (xargs :guard (and (pseudo-termp x)
                                (symbolp explicit-rule)
                                (plist-worldp w))))
    (b* (((when (or (variablep x) (fquotep x))) x)
         (fn (ffn-symb x))
         ((when (flambdap fn))
          ;; expand the lambda; why not
          (b* ((formals (lambda-formals fn))
               (body (lambda-body fn))
               (args (fargs x)))
            (substitute-into-term body (pairlis$ formals args))))
         ;; x is a function call, fn is a symbol
         (rule (or explicit-rule fn))
         (formula (meta-extract-formula-w rule w))
         ((unless (pseudo-termp formula)) x)
         ((mv ok lhs rhs)
          (case-match formula
            (('equal lhs rhs)
             (mv t lhs rhs))
            (& (mv nil nil nil))))
         ((unless ok) x)
         ((mv match-ok subst) (simple-one-way-unify lhs x nil))
         ((unless match-ok) x))
      (substitute-into-term rhs subst)))

  (local (in-theory (enable expand-this-term)))

  (defthm expand-this-term-correct
    (implies (and (expev-meta-extract-global-facts)
                  (equal w (w state))
                  (pseudo-termp x))
             (equal (expev (expand-this-term x explicit-rule w) a)
                    (expev x a)))
    :hints (("goal" :use ((:instance expev-meta-extract-formula
                           (name (or explicit-rule (car x)))
                           (st state)
                           (a (expev-alist
                               (mv-nth 1 (simple-one-way-unify
                                          (cadr (meta-extract-formula
                                                 (or explicit-rule (car x)) state))
                                          x nil))
                               a))))
             :in-theory (disable expev-meta-extract-formula))))

  (defthm expand-this-term-pseudo-termp
    (implies (pseudo-termp x)
             (pseudo-termp (expand-this-term x explicit-rule w)))))


(defsection expand-if-marked


  (defund expand-if-marked (fn args w)
    (declare (xargs :guard (and (symbolp fn)
                                (not (eq fn 'quote))
                                (pseudo-term-listp args)
                                (plist-worldp w))))
    (b* (((when (eq fn 'expand-me))
          (b* ((term (first args)))
            (expand-this-term term nil w)))
         ((when (and (eq fn 'expand-me-with)
                     (quotep (first args))))
          (b* ((rule (unquote (first args)))
               (term (second args))
               ((unless (or (symbol-listp rule) ;; rune
                            (symbolp rule)))
                term)
               (rule (if (consp rule) (second rule) rule)))
            (expand-this-term term rule w))))
      (cons fn args)))

  (local (in-theory (enable expand-if-marked expand-me expand-me-with)))

  (defthm expand-if-marked-correct
    (implies (and (expev-meta-extract-global-facts)
                  (equal w (w state))
                  (symbolp fn)
                  (pseudo-term-listp args))
             (equal (expev (expand-if-marked fn args w) a)
                    (expev (cons fn args) a))))

  (defthm expand-if-marked-pseudo-termp
    (implies (and (symbolp fn)
                  (not (eq fn 'quote))
                  (pseudo-term-listp args))
             (pseudo-termp (expand-if-marked fn args w))))

  (defun expand-if-marked-meta (x mfc state)
    (declare (xargs :stobjs state
                    :guard (pseudo-termp x))
             (ignorable mfc))
    (b* (((when (variablep x)) x)
         (fn (ffn-symb x))
         ((when (eq fn 'quote)) x)
         ((when (consp fn)) x)
         (args (fargs x)))
      (expand-if-marked fn args (w state))))


  ;; don't enable this now or the rest of the book will go crazy
  (defthmd expand-marked-meta
    (implies (and (pseudo-termp x)
                  (expev-meta-extract-global-facts))
             (equal (expev x a)
                    (expev (expand-if-marked-meta x mfc state) a)))
    :rule-classes ((:meta :trigger-fns (expand-me expand-me-with)))))


(defsection term/alist-ind
  (mutual-recursion
   (defun expev-term/alist-ind (x al)
     (b* (((when (variablep x)) al)
          (fn (ffn-symb x))
          ((when (eq fn 'quote)) al)
          (?args (expev-termlist/alist-ind (fargs x) al))
          ((when (consp fn))
           (expev-term/alist-ind (lambda-body fn)
                                 (pairlis$ (lambda-formals fn)
                                           (expev-lst (fargs x) al)))))
       al))
   (defun expev-termlist/alist-ind (x al)
     (if (atom x)
         nil
       (cons (expev-term/alist-ind (car x) al)
             (expev-termlist/alist-ind (cdr x) al)))))

  (make-flag expev-term/alist-flag expev-term/alist-ind
             :flag-mapping ((expev-term/alist-ind . term)
                            (expev-termlist/alist-ind . list))))



(defsection expand-marked-term

  (mutual-recursion
   (defun expand-marked-term (x w)
     (declare (xargs :guard (and (pseudo-termp x)
                                 (plist-worldp w))
                     :verify-guards nil))
     (b* (((when (variablep x)) x)
          (fn (ffn-symb x))
          ((when (eq fn 'quote)) x)
          (args (expand-marked-list (fargs x) w))
          ((when (flambdap fn))
           `((lambda ,(lambda-formals fn)
               ,(expand-marked-term (lambda-body fn) w))
             . ,args)))
       (expand-if-marked fn args w)))

   (defun expand-marked-list (x w)
     (declare (xargs :guard (and (pseudo-term-listp x)
                                 (plist-worldp w))))
     (if (atom x)
         nil
       (cons (expand-marked-term (car x) w)
             (expand-marked-list (cdr x) w)))))



  (in-theory (disable expand-marked-term
                      expand-marked-list))

  (defthm len-of-expand-marked-list
    (equal (len (expand-marked-list x w))
           (len x))
    :hints(("Goal" :in-theory (enable expand-marked-list))))

  (defthm-expev-term/alist-flag
    (defthm expand-marked-term-pseudo-termp
      (implies (pseudo-termp x)
               (pseudo-termp (expand-marked-term x w)))
      :hints ('(:expand ((expand-marked-term x w))))
      :flag term)
    (defthm expand-marked-list-pseudo-term-listp
      (implies (pseudo-term-listp x)
               (pseudo-term-listp (expand-marked-list x w)))
      :hints ('(:expand ((expand-marked-list x w)
                         (expand-marked-list nil w))))
      :flag list))

  (local (defthm pseudo-termp-car-when-pseudo-term-listp
           (implies (pseudo-term-listp x)
                    (pseudo-termp (car x)))))

  (verify-guards expand-marked-term)

  (defthm-expev-term/alist-flag
    (defthm expand-marked-term-correct
      (implies (and (expev-meta-extract-global-facts)
                    (equal w (w state))
                    (pseudo-termp x))
               (equal (expev (expand-marked-term x w) al)
                      (expev x al)))
      :hints ('(:expand ((expand-marked-term x w))
                :in-theory (enable expev-of-fncall-args)))
      :flag term)
    (defthm expand-marked-list-correct
      (implies (and (expev-meta-extract-global-facts)
                    (equal w (w state))
                    (pseudo-term-listp x))
               (equal (expev-lst (expand-marked-list x w) al)
                      (expev-lst x al)))
      :hints ('(:expand ((expand-marked-list x w)
                         (expand-marked-list nil w))))
      :flag list)))


(defsection remove-expand-mes

  (mutual-recursion
   (defun remove-expand-mes (x)
     (declare (xargs :guard (and (pseudo-termp x))
                     :verify-guards nil))
     (b* (((when (variablep x)) x)
          (fn (ffn-symb x))
          ((when (eq fn 'quote)) x)
          (args (remove-expand-mes-list (fargs x)))
          ((when (flambdap fn))
           `((lambda ,(lambda-formals fn)
               ,(remove-expand-mes (lambda-body fn)))
             . ,args))
          ((when (and (eq fn 'expand-me) (equal (len args) 1)))
           (car args))
          ((when (and (eq fn 'expand-me-with) (equal (len args) 2)))
           (cadr args)))
       (cons fn args)))

   (defun remove-expand-mes-list (x)
     (declare (xargs :guard (and (pseudo-term-listp x))))
     (if (atom x)
         nil
       (cons (remove-expand-mes (car x))
             (remove-expand-mes-list (cdr x))))))



  (in-theory (disable remove-expand-mes
                      remove-expand-mes-list))

  (defthm len-of-remove-expand-mes-list
    (equal (len (remove-expand-mes-list x))
           (len x))
    :hints(("Goal" :in-theory (enable remove-expand-mes-list))))

  (defthm-expev-term/alist-flag
    (defthm remove-expand-mes-pseudo-termp
      (implies (pseudo-termp x)
               (pseudo-termp (remove-expand-mes x)))
      :hints ('(:expand ((remove-expand-mes x))))
      :flag term)
    (defthm remove-expand-mes-list-pseudo-term-listp
      (implies (pseudo-term-listp x)
               (pseudo-term-listp (remove-expand-mes-list x)))
      :hints ('(:expand ((remove-expand-mes-list x)
                         (remove-expand-mes-list nil))))
      :flag list))

  (local (defthm pseudo-termp-car-when-pseudo-term-listp
           (implies (pseudo-term-listp x)
                    (pseudo-termp (car x)))))

  (verify-guards remove-expand-mes)

  (defthm-expev-term/alist-flag
    (defthm remove-expand-mes-correct
      (implies (pseudo-termp x)
               (equal (expev (remove-expand-mes x) al)
                      (expev x al)))
      :hints ('(:expand ((remove-expand-mes x))
                :in-theory (enable expev-of-fncall-args
                                   expand-me expand-me-with)))
      :flag term)
    (defthm remove-expand-mes-list-correct
      (implies (pseudo-term-listp x)
               (equal (expev-lst (remove-expand-mes-list x) al)
                      (expev-lst x al)))
      :hints ('(:expand ((remove-expand-mes-list x)
                         (remove-expand-mes-list nil))))
      :flag list)))





;; This could be made much more sophisticated.  However, at the moment we just
;; expand term with an EQUAL-based definition.

;; (defun just-expand-cp-hint-get-rule (rule fn w)
;;   (declare (xargs :mode :program))
;;   (if (not rule)
;;       (b* ((def (def-body fn w))
;;            ((unless (and def (not (access def-body def :hyp))))
;; ; Matt K. note: With new :equiv field, maybe also need (eq 'equal (access def-body def :equiv)).
;;             (er hard? 'just-expand-cp "couldn't find a hyp-free definition for ~x0"
;;                 fn)
;;             nil))
;;         (list (cons fn (access def-body def :formals)) ;; lhs
;;               (access def-body def :concl)
;;               (access def-body def :rune)))
;;     (b* ((lemmas (getprop fn 'lemmas nil 'current-acl2-world w))
;;          (lemma (if (symbolp rule)
;;                     (find-named-lemma
;;                      (deref-macro-name rule (macro-aliases w))
;;                      lemmas t)
;;                   (find-runed-lemma rule lemmas)))
;;          ((unless (and lemma
;;                        (not (access rewrite-rule lemma :hyps))
;;                        (eq (access rewrite-rule lemma :equiv) 'equal)))
;;           (er hard? 'just-expand-cp "the definition has hyps or is not EQUAL-based")
;;           nil))
;;       (list (access rewrite-rule lemma :lhs)
;;             (access rewrite-rule lemma :rhs)
;;             (access rewrite-rule lemma :rune)))))

(defsection just-expand-cp-parse-hints

  (defun just-expand-cp-finish-hint (rule vars term w)
    (declare (xargs :mode :program))
    (b* (((when (atom term))
          (er hard? 'just-expand-cp "atom in term position in hints: ~x0~%" term)) ;; error
         ((mv erp trans-term)
          (translate-cmp term t nil nil 'just-expand-cp w
                         (default-state-vars nil)))
         ((when erp)
          (er hard? 'just-expand-cp "translate failed: ~@0~%" trans-term))
         ;; ((list lhs rhs rune) (just-expand-cp-hint-get-rule rule (car trans-term)
         ;;                                                    w))
         (trans-term-vars (simple-term-vars trans-term))
         (nonfree-vars (set-difference-eq trans-term-vars vars))
         ((when (not (or (symbolp rule)
                         (symbol-listp rule)))) ;; rune
          (er hard? 'just-expand-cp "invalid rule: ~x0~%" rule))
         (rule (if (consp rule) (cadr rule) rule)))
      (cons trans-term `(;; (lhs . ,lhs)
                         ;; (rhs . ,rhs)
                         (rule . ,rule)
                         (subst . ,(pairlis$ nonfree-vars nonfree-vars))))))

  (defun just-expand-cp-parse-hint (hint w)
    (declare (xargs :mode :program))
    (case-match hint
      ((':with rule (':free vars term))
       (just-expand-cp-finish-hint rule vars term w))
      ((':free vars (':with rule term))
       (just-expand-cp-finish-hint rule vars term w))
      ((':free vars term)
       (just-expand-cp-finish-hint nil vars term w))
      ((':with rule term)
       (just-expand-cp-finish-hint rule nil term w))
      (& (just-expand-cp-finish-hint nil nil hint w))))


  (defun just-expand-cp-parse-hints (hints w)
    (declare (Xargs :mode :program))
    (if (atom hints)
        nil
      (cons (just-expand-cp-parse-hint (car hints) w)
            (just-expand-cp-parse-hints (cdr hints) w)))))


(defsection just-exp-hints-okp

  (defund just-exp-hint-alist-okp (alist)
    (declare (xargs :guard t))
    (and (alistp alist)
         (symbolp (cdr (assoc 'rule alist)))
         (alistp (cdr (assoc 'subst alist)))))

  (defund just-exp-hints-okp (hints)
    (declare (xargs :guard t))
    (or (atom hints)
        (and (consp (car hints))
             (pseudo-termp (caar hints))
             (just-exp-hint-alist-okp (cdar hints))
             (just-exp-hints-okp (cdr hints))))))


(defsection mark-expansion

  (local (in-theory (enable just-exp-hint-alist-okp)))

  (defund mark-expansion (term pattern alist)
    (declare (xargs :guard (and (pseudo-termp term)
                                (pseudo-termp pattern)
                                (just-exp-hint-alist-okp alist))))
    (b* ((subst (cdr (assoc 'subst alist)))
         ((mv pat-ok &) (simple-one-way-unify pattern term subst))
         ((unless pat-ok) term)
         (rule (cdr (assoc 'rule alist))))
      (if rule
          `(expand-me-with ',rule ,term)
        `(expand-me ,term))))

  (local (in-theory (enable mark-expansion expand-me expand-me-with)))

  (defthm mark-expansion-correct
    (implies (and (pseudo-termp term)
                  (pseudo-termp pattern)
                  (just-exp-hint-alist-okp alist))
             (equal (expev (mark-expansion term pattern alist) a)
                    (expev term a)))
    :hints (("goal" :do-not-induct t)))

  (defthm pseudo-termp-mark-expansion
    (implies (pseudo-termp term)
             (pseudo-termp (mark-expansion term pattern alist)))))


(defsection mark-expansions
  (local (in-theory (enable just-exp-hints-okp)))

  (defund mark-expansions (term hints)
    (declare (xargs :guard (and (pseudo-termp term)
                                (just-exp-hints-okp hints))))
    (if (atom hints)
        term
      (mark-expansions
       (mark-expansion term (caar hints) (cdar hints))
       (cdr hints))))

  (local (in-theory (enable mark-expansions)))


  (defthm mark-expansions-correct
    (implies (and (just-exp-hints-okp hints)
                  (pseudo-termp term))
             (equal (expev (mark-expansions term hints) a)
                    (expev term a))))

  (defthm pseudo-termp-mark-expansions
    (implies (pseudo-termp term)
             (pseudo-termp (mark-expansions term hints)))))




(defsection mark-expands-with-hints

  (mutual-recursion
   (defun mark-expands-with-hints (x hints lambdasp)
     (declare (xargs :guard (and (pseudo-termp x)
                                 (just-exp-hints-okp hints))
                     :verify-guards nil))
     (b* (((when (variablep x)) x)
          (fn (ffn-symb x))
          ((when (eq fn 'quote)) x)
          (args (mark-expands-with-hints-list (fargs x) hints lambdasp))
          ((when (and lambdasp (flambdap fn)))
           `((lambda ,(lambda-formals fn)
               ;; NOTE: this is a little odd because it doesn't consider the lambda
               ;; substitution.  Sound, but arguably expands the wrong terms (for
               ;; some value of "wrong").
               ,(mark-expands-with-hints (lambda-body fn) hints lambdasp))
             . ,args)))
       (mark-expansions (cons fn args) hints)))

   (defun mark-expands-with-hints-list (x hints lambdasp)
     (declare (xargs :guard (and (pseudo-term-listp x)
                                 (just-exp-hints-okp hints))))
     (if (atom x)
         nil
       (cons (mark-expands-with-hints (car x) hints lambdasp)
             (mark-expands-with-hints-list (cdr x) hints lambdasp)))))

  (in-theory (disable mark-expands-with-hints
                      mark-expands-with-hints-list))

  (defthm len-of-mark-expands-with-hints-list
    (equal (len (mark-expands-with-hints-list x hints lambdasp))
           (len x))
    :hints(("Goal" :in-theory (enable mark-expands-with-hints-list))))

  (defthm-expev-term/alist-flag
    (defthm mark-expands-with-hints-pseudo-termp
      (implies (pseudo-termp x)
               (pseudo-termp (mark-expands-with-hints x hints lambdasp)))
      :hints ('(:expand ((mark-expands-with-hints x hints lambdasp))))
      :flag term)
    (defthm mark-expands-with-hints-list-pseudo-term-listp
      (implies (pseudo-term-listp x)
               (pseudo-term-listp (mark-expands-with-hints-list x hints lambdasp)))
      :hints ('(:expand ((mark-expands-with-hints-list x hints lambdasp)
                         (mark-expands-with-hints-list nil hints lambdasp))))
      :flag list))

  (verify-guards mark-expands-with-hints
    :hints (("goal" :expand ((:free (a b) (pseudo-termp (cons a b)))))))

  (defthm-expev-term/alist-flag
    (defthm mark-expands-with-hints-correct
      (implies (and (just-exp-hints-okp hints)
                    (pseudo-termp x))
               (equal (expev (mark-expands-with-hints x hints lambdasp) al)
                      (expev x al)))
      :hints ('(:expand ((mark-expands-with-hints x hints lambdasp))
                :in-theory (enable expev-of-fncall-args)))
      :flag term)
    (defthm mark-expands-with-hints-list-correct
      (implies (and (just-exp-hints-okp hints)
                    (pseudo-term-listp x))
               (equal (expev-lst (mark-expands-with-hints-list x hints lambdasp) al)
                      (expev-lst x al)))
      :hints ('(:expand ((mark-expands-with-hints-list x hints lambdasp)
                         (mark-expands-with-hints-list nil hints lambdasp))))
      :flag list)))



(defsection apply-expansion

  (local (in-theory (enable just-exp-hint-alist-okp)))

  (defund apply-expansion (term pattern alist w)
    (declare (xargs :guard (and (pseudo-termp term)
                                (pseudo-termp pattern)
                                (just-exp-hint-alist-okp alist)
                                (plist-worldp w))))
    (b* ((subst (cdr (assoc 'subst alist)))
         ((mv pat-ok &) (simple-one-way-unify pattern term subst))
         ((unless pat-ok) term)
         (rule (cdr (assoc 'rule alist))))
      (expand-this-term term rule w)))

  (local (in-theory (enable apply-expansion)))

  (defthm apply-expansion-correct
    (implies (and (expev-meta-extract-global-facts)
                  (equal w (w state))
                  (pseudo-termp term)
                  (pseudo-termp pattern)
                  (just-exp-hint-alist-okp alist))
             (equal (expev (apply-expansion term pattern alist w) a)
                    (expev term a)))
    :hints (("goal" :do-not-induct t)))

  (defthm pseudo-termp-apply-expansion
    (implies (pseudo-termp term)
             (pseudo-termp (apply-expansion term pattern alist w)))))

(defsection apply-expansions
  (local (in-theory (enable just-exp-hints-okp)))

  (defund apply-expansions (term hints w)
    (declare (xargs :guard (and (pseudo-termp term)
                                (just-exp-hints-okp hints)
                                (plist-worldp w))))
    (if (atom hints)
        term
      (apply-expansions
       (apply-expansion term (caar hints) (cdar hints) w)
       (cdr hints) w)))

  (local (in-theory (enable apply-expansions)))


  (defthm apply-expansions-correct
    (implies (and (expev-meta-extract-global-facts)
                  (equal w (w state))
                  (just-exp-hints-okp hints)
                  (pseudo-termp term))
             (equal (expev (apply-expansions term hints w) a)
                    (expev term a))))

  (defthm pseudo-termp-apply-expansions
    (implies (pseudo-termp term)
             (pseudo-termp (apply-expansions term hints w)))))


(defsection expand-with-hints

  (mutual-recursion
   (defun expand-with-hints (x hints lambdasp w)
     (declare (xargs :guard (and (pseudo-termp x)
                                 (plist-worldp w)
                                 (just-exp-hints-okp hints))
                     :verify-guards nil))
     (b* (((when (variablep x)) x)
          (fn (ffn-symb x))
          ((when (eq fn 'quote)) x)
          (args (expand-with-hints-list (fargs x) hints lambdasp w))
          ((when (and lambdasp (flambdap fn)))
           `((lambda ,(lambda-formals fn)
               ;; NOTE: this is a little odd because it doesn't consider the lambda
               ;; substitution.  Sound, but arguably expands the wrong terms (for
               ;; some value of "wrong").
               ,(expand-with-hints (lambda-body fn) hints lambdasp w))
             . ,args)))
       (apply-expansions (cons fn args) hints w)))

   (defun expand-with-hints-list (x hints lambdasp w)
     (declare (xargs :guard (and (pseudo-term-listp x)
                                 (just-exp-hints-okp hints)
                                 (plist-worldp w))))
     (if (atom x)
         nil
       (cons (expand-with-hints (car x) hints lambdasp w)
             (expand-with-hints-list (cdr x) hints lambdasp w)))))

  (in-theory (disable expand-with-hints
                      expand-with-hints-list))

  (defthm len-of-expand-with-hints-list
    (equal (len (expand-with-hints-list x hints lambdasp w))
           (len x))
    :hints(("Goal" :in-theory (enable expand-with-hints-list))))

  (defthm-expev-term/alist-flag
    (defthm expand-with-hints-pseudo-termp
      (implies (pseudo-termp x)
               (pseudo-termp (expand-with-hints x hints lambdasp w)))
      :hints ('(:expand ((expand-with-hints x hints lambdasp w))))
      :flag term)
    (defthm expand-with-hints-list-pseudo-term-listp
      (implies (pseudo-term-listp x)
               (pseudo-term-listp (expand-with-hints-list x hints lambdasp w)))
      :hints ('(:expand ((expand-with-hints-list x hints lambdasp w)
                         (expand-with-hints-list nil hints lambdasp w))))
      :flag list))

  (verify-guards expand-with-hints
    :hints (("goal" :expand ((:free (a b) (pseudo-termp (cons a b)))))))

  (defthm-expev-term/alist-flag
    (defthm expand-with-hints-correct
      (implies (and (expev-meta-extract-global-facts)
                    (equal w (w state))
                    (just-exp-hints-okp hints)
                    (pseudo-termp x))
               (equal (expev (expand-with-hints x hints lambdasp w) al)
                      (expev x al)))
      :hints ('(:expand ((expand-with-hints x hints lambdasp w))
                :in-theory (enable expev-of-fncall-args)))
      :flag term)
    (defthm expand-with-hints-list-correct
      (implies (and (expev-meta-extract-global-facts)
                    (equal w (w state))
                    (just-exp-hints-okp hints)
                    (pseudo-term-listp x))
               (equal (expev-lst (expand-with-hints-list x hints lambdasp w) al)
                      (expev-lst x al)))
      :hints ('(:expand ((expand-with-hints-list x hints lambdasp w)
                         (expand-with-hints-list nil hints lambdasp w))))
      :flag list)))






;; (mutual-recursion
;;  (defun term-apply-expansions (x hints lambdasp)
;;    (declare (xargs :guard (and (pseudo-termp x)
;;                                (just-exp-hints-okp hints))
;;                    :verify-guards nil))
;;    (if (or (variablep x)
;;            (fquotep x))
;;        x
;;      (let ((args (termlist-apply-expansions (fargs x) hints lambdasp))
;;            (fn (ffn-symb x)))
;;        (if (and lambdasp (flambdap fn))
;;            ;; NOTE: this is a little odd because it doesn't consider the lambda
;;            ;; substitution.  Sound, but arguably expands the wrong terms (for
;;            ;; some value of "wrong").
;;            (let* ((body (term-apply-expansions (lambda-body fn) hints lambdasp)))
;;              (cons (make-lambda (lambda-formals fn) body)
;;                    args))
;;          (apply-expansions (cons fn args) hints)))))
;;  (defun termlist-apply-expansions (x hints lambdasp)
;;    (declare (xargs :guard (and (pseudo-term-listp x)
;;                                (just-exp-hints-okp hints))))
;;    (if (atom x)
;;        nil
;;      (cons (term-apply-expansions (car x) hints lambdasp)
;;            (termlist-apply-expansions (cdr x) hints lambdasp)))))

;; (make-flag term-apply-expansions-flg term-apply-expansions
;;            :flag-mapping ((term-apply-expansions . term)
;;                           (termlist-apply-expansions . list)))

;; (defthm len-of-termlist-apply-expansions
;;   (equal (len (termlist-apply-expansions x hints lambdasp))
;;          (len x))
;;   :hints (("goal" :induct (len x)
;;            :expand (termlist-apply-expansions x hints lambdasp))))

;; (defthm-term-apply-expansions-flg
;;   (defthm pseudo-termp-term-apply-expansions
;;     (implies (and (pseudo-termp x)
;;                   (just-exp-hints-okp hints))
;;              (pseudo-termp (term-apply-expansions x hints lambdasp)))
;;     :hints ((and stable-under-simplificationp
;;                  '(:expand ((:free (a b) (pseudo-termp (cons a b)))))))
;;     :flag term)
;;   (defthm pseudo-term-listp-termlist-apply-expansions
;;     (implies (and (pseudo-term-listp x)
;;                   (just-exp-hints-okp hints))
;;              (pseudo-term-listp (termlist-apply-expansions x hints lambdasp)))
;;     :flag list))

;; (mutual-recursion
;;  (defun term-apply-expansions-correct-ind (x hints a lambdasp)
;;    (if (or (variablep x)
;;            (fquotep x))
;;        (list x a)
;;      (let ((args (termlist-apply-expansions (fargs x) hints lambdasp))
;;            (ign (termlist-apply-expansions-correct-ind
;;                  (fargs x) hints a lambdasp))
;;            (fn (ffn-symb x)))
;;        (declare (ignore ign))
;;        (if (and lambdasp (flambdap fn))
;;            (term-apply-expansions-correct-ind
;;             (lambda-body fn) hints
;;             (pairlis$ (lambda-formals fn)
;;                       (expev-lst args a)) lambdasp)
;;          (apply-expansions (cons fn args) hints)))))
;;  (defun termlist-apply-expansions-correct-ind (x hints a lambdasp)
;;    (if (atom x)
;;        nil
;;      (cons (term-apply-expansions-correct-ind (car x) hints a lambdasp)
;;            (termlist-apply-expansions-correct-ind (cdr x) hints a lambdasp)))))

;; (make-flag term-apply-expansions-correct-flg term-apply-expansions-correct-ind
;;            :flag-mapping ((term-apply-expansions-correct-ind . term)
;;                           (termlist-apply-expansions-correct-ind . list)))



;; (defthm-term-apply-expansions-correct-flg
;;   (defthm term-apply-expansions-correct
;;     (implies (and (pseudo-termp x)
;;                   (just-exp-hints-okp hints)
;;                   (expev-theoremp (conjoin-clauses (hint-alists-to-clauses hints))))
;;              (equal (expev (term-apply-expansions x hints lambdasp) a)
;;                     (expev x a)))
;;     :hints ((and stable-under-simplificationp
;;                  '(:in-theory (enable expev-constraint-0)
;;                    :expand ((:free (a b) (pseudo-termp (cons a b)))))))
;;     :flag term)
;;   (defthm termlist-apply-expansions-correct
;;     (implies (and (pseudo-term-listp x)
;;                   (just-exp-hints-okp hints)
;;                   (expev-theoremp (conjoin-clauses (hint-alists-to-clauses hints))))
;;              (equal (expev-lst (termlist-apply-expansions x hints lambdasp) a)
;;                     (expev-lst x a)))
;;     :flag list))

;; (verify-guards term-apply-expansions
;;   :hints ((and stable-under-simplificationp
;;                '(:expand ((:free (a b) (pseudo-termp (cons a b))))))))

;; (in-theory (disable term-apply-expansions))

(local
 (defsection butlast/last/append

   (defthm expev-of-disjoin
     (iff (expev (disjoin x) a)
          (or-list (expev-lst x a)))
     :hints(("Goal" :in-theory (enable or-list len)
             :induct (len x))))

   (defthm expev-lst-of-append
     (equal (expev-lst (append x y) a)
            (append (expev-lst x a)
                    (expev-lst y a))))

   (defthm len-of-expev-lst
     (equal (len (expev-lst x a))
            (len x)))

   (defthm expev-lst-of-butlast
     (equal (expev-lst (butlast clause n) a)
            (butlast (expev-lst clause a) n))
     :hints (("goal" :induct (butlast clause n))
             '(:cases ((consp clause)))))

   (defthm expev-lst-of-last
     (equal (expev-lst (last x) a)
            (last (expev-lst x a)))
     :hints (("goal" :induct (last x)
              :expand ((last x)
                       (:free (b)
                        (last (cons (expev (car x) a) b))))
              :in-theory (disable (:d last)))
             '(:cases ((consp x)))))

   (defthm append-butlast-last
     (equal (append (butlast x 1) (last x))
            x))

   (defthm pseudo-term-listp-of-last
     (implies (pseudo-term-listp x)
              (pseudo-term-listp (last x))))

   (defthm pseudo-term-listp-of-butlast
     (implies (pseudo-term-listp x)
              (pseudo-term-listp (butlast x n))))

   (defthm not-or-list-of-butlast-if-not-or-list
     (implies (not (or-list x))
              (not (or-list (butlast x n)))))

   (defthm pseudo-term-listp-append
     (implies (and (pseudo-term-listp x)
                   (pseudo-term-listp y))
              (pseudo-term-listp (append x y))))))

(defsection just-expand-cp

  (local (defthm true-listp-butlast
           (true-listp (butlast lst n))))


  (defund just-expand-cp (clause hints state)
    (declare (xargs :guard (pseudo-term-listp clause)
                    :stobjs state))
    (b* (((unless (and (true-listp hints)
                       (just-exp-hints-okp (caddr hints))))
          (mv "bad hints" nil))
         ((list last-only lambdasp hints) hints)
         (clause
          (if last-only
              (append (butlast clause 1)
                      (expand-with-hints-list
                       (last clause) hints lambdasp (w state)))
            (expand-with-hints-list
             clause hints lambdasp (w state)))))
      (mv nil (list clause))))

  (local (in-theory (enable just-expand-cp)))
  (local (in-theory (disable butlast-redefinition or-list last)))

  (defthm just-expand-cp-correct
    (implies (and (expev-meta-extract-global-facts)
                  (pseudo-term-listp clause)
                  (alistp a)
                  (expev-theoremp
                   (conjoin-clauses
                    (clauses-result (just-expand-cp clause hints state)))))
             (expev (disjoin clause) a))
    :hints (("goal" :do-not-induct t
             :use ((:instance expev-falsify
                    (x (disjoin (car (mv-nth 1 (just-expand-cp clause hints state)))))))))
    :rule-classes :clause-processor))


(defsection expand-marked-cp

  (local (defthm true-listp-butlast
           (true-listp (butlast lst n))))


  (defund expand-marked-cp (clause hints state)
    (declare (xargs :guard (pseudo-term-listp clause)
                    :stobjs state))
    (b* (((unless (true-listp hints))
          (mv "bad hints" nil))
         ((list last-only) hints)
         (clause
          (if last-only
              (append (remove-expand-mes-list (butlast clause 1))
                      (expand-marked-list (last clause) (w state)))
            (expand-marked-list clause (w state)))))

      (mv nil (list clause))))

  (local (in-theory (enable expand-marked-cp)))
  (local (in-theory (disable butlast-redefinition or-list last)))

  (defthm expand-marked-cp-correct
    (implies (and (expev-meta-extract-global-facts)
                  (pseudo-term-listp clause)
                  (alistp a)
                  (expev-theoremp
                   (conjoin-clauses
                    (clauses-result (expand-marked-cp clause hints state)))))
             (expev (disjoin clause) a))
    :hints (("goal" :do-not-induct t
             :use ((:instance expev-falsify
                    (x (disjoin (car (mv-nth 1 (expand-marked-cp clause hints state)))))))))
    :rule-classes :clause-processor))

(defsection remove-expand-marks-cp

  (local (defthm true-listp-butlast
           (true-listp (butlast lst n))))


  (defund remove-expand-marks-cp (clause hints)
    (declare (xargs :guard (pseudo-term-listp clause)))
    (b* (((unless (true-listp hints))
          (mv "bad hints" nil))
         ((list butlast-only) hints)
         (clause
          (if butlast-only
              (append (remove-expand-mes-list (butlast clause 1))
                      (last clause))
            (remove-expand-mes-list clause))))

      (mv nil (list clause))))

  (local (in-theory (enable remove-expand-marks-cp)))
  (local (in-theory (disable butlast-redefinition or-list last)))

  (defthm remove-expand-marks-cp-correct
    (implies (and (expev-meta-extract-global-facts)
                  (pseudo-term-listp clause)
                  (alistp a)
                  (expev-theoremp
                   (conjoin-clauses
                    (clauses-result (remove-expand-marks-cp clause hints)))))
             (expev (disjoin clause) a))
    :hints (("goal" :do-not-induct t
             :use ((:instance expev-falsify
                    (x (disjoin (car (mv-nth 1 (remove-expand-marks-cp clause hints)))))))))
    :rule-classes :clause-processor))

(defsection mark-expands-cp

  (defund mark-expands-cp (clause hints)
    (declare (xargs :guard (pseudo-term-listp clause)))
    (b* (((unless (and (true-listp hints)
                       (just-exp-hints-okp (caddr hints))))
          (mv "bad hints" nil))
         ((list last-only lambdasp hints) hints)
         ; ((when (atom clause)) (mv nil (list nil)))
         (new-clause
          (if last-only
              (append (butlast clause 1)
                      (mark-expands-with-hints-list
                       (last clause) hints lambdasp))
            (mark-expands-with-hints-list
             clause hints lambdasp))))
      (mv nil (list new-clause))))

  (local (in-theory (enable mark-expands-cp)))
  (local (in-theory (disable butlast-redefinition or-list last)))

  (defthm mark-expands-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (expev-theoremp
                   (conjoin-clauses
                    (clauses-result (mark-expands-cp clause hints)))))
             (expev (disjoin clause) a))
    :hints (("goal" :do-not-induct t
             :use ((:instance expev-falsify
                    (x (disjoin (car (mv-nth 1 (mark-expands-cp clause hints)))))))))
    :rule-classes :clause-processor))

(defmacro just-expand (expand-lst &key lambdasp mark-only last-only)
  `(let* ((hints (just-expand-cp-parse-hints ',expand-lst (w state)))
          (cproc ,(if mark-only
                      ``(mark-expands-cp clause '(,',last-only ,',lambdasp ,hints))
                    ``(just-expand-cp clause '(,',last-only ,',lambdasp ,hints) state))))
     `(:computed-hint-replacement
       ((use-by-computed-hint clause))
       :clause-processor
       ,cproc)))

(defmacro expand-marked (&key last-only)
  ``(:computed-hint-replacement
     ((use-by-computed-hint clause))
     :clause-processor
     (expand-marked-cp clause (list ,',last-only) state)))

(defmacro remove-expand-marks (&key butlast-only)
  ``(:computed-hint-replacement
     ((use-by-computed-hint clause))
     :clause-processor
     (remove-expand-marks-cp clause (list ,',butlast-only))))


(local
 (encapsulate nil
   (value-triple 1)
   (local (defthm foo (implies (consp x)
                               (equal (len x) (+ 1 (len (cdr x)))))
            :hints (("goal" :do-not '(simplify preprocess eliminate-destructors)
                     :in-theory (disable len))
                    (let ((res (just-expand ((len x)))))
                      (progn$ (cw "hint: ~x0~%" res)
                              res))
                    '(:do-not nil))
            :rule-classes nil))))

(local
 (encapsulate nil
   (value-triple 2)
   (local (defthm foo (implies (consp x)
                               (equal (len x) (+ 1 (len (cdr x)))))
            :hints (("goal" :do-not '(simplify preprocess eliminate-destructors)
                     :in-theory (disable len))
                    (let ((res (just-expand ((len x)) :mark-only t)))
                      (progn$ (cw "hint: ~x0~%" res)
                              res))
                    '(:do-not nil)
                    (and stable-under-simplificationp
                         '(:in-theory (e/d (expand-marked-meta) (len)))))
            :rule-classes nil))))

;; must use :lambdasp t or this won't work
(local
 (encapsulate nil
   (value-triple 3)
   (local (defthm foo (implies (consp x)
                               (let ((x (list x x)))
                                 (equal (len x) (+ 1 (len (cdr x))))))
            :hints (("goal" :do-not '(simplify preprocess eliminate-destructors)
                     :in-theory (disable len))
                    (just-expand ((len x)) :lambdasp t)
                    '(:do-not nil))))))

(local
 (encapsulate nil
   (value-triple 4)
   (local (defthm foo (implies (consp x)
                               (equal (len x) (+ 1 (len (cdr x)))))
            :hints (("goal" :do-not '(simplify preprocess eliminate-destructors)
                     :in-theory (disable len))
                    (let ((res (just-expand ((len x)) :mark-only t)))
                      (progn$ (cw "hint: ~x0~%" res)
                              res))
                    '(:do-not nil)
                    (and stable-under-simplificationp
                         (expand-marked)))
            :rule-classes nil))))

(defsection clause-to-term

  (verify-termination dumb-negate-lit)

  ;; BOZO this is here because dumb-negate-lit-lst (built in) needs a
  ;; pseudo-term-listp guard and doesn't have one
  (defun dumb-negate-lit-list (lst)
    (declare (xargs :guard (pseudo-term-listp lst)))
    (cond ((endp lst) nil)
          (t (cons (dumb-negate-lit (car lst))
                   (dumb-negate-lit-list (cdr lst))))))

  (local (defthm dumb-negate-lit-correct
           (implies (pseudo-termp x)
                    (iff (expev (dumb-negate-lit x) a)
                         (not (expev x a))))))

  (local (in-theory (disable dumb-negate-lit)))

  (local (defthm dumb-negate-lit-list-conjoin-correct
           (implies (pseudo-term-listp x)
                    (iff (expev (conjoin (dumb-negate-lit-list x)) a)
                         (not (expev (disjoin x) a))))))

  (local (in-theory (disable dumb-negate-lit-list)))

  (defund clause-to-term (clause)
    (declare (xargs :guard (pseudo-term-listp clause)))
    (let* ((hyp-term (conjoin (dumb-negate-lit-list
                               (butlast clause 1))))
           (concl-term (car (last clause)))
           (thm-term (if (equal hyp-term ''t) concl-term
                       `(implies ,hyp-term ,concl-term))))
    (list (list thm-term))))


  (local (in-theory (enable clause-to-term)))

  (local (defthm expev-car-last
           (implies (expev (car (last clause)) a)
                    (or-list (expev-lst clause a)))
           :hints (("goal" :induct (len clause)
                    :in-theory (disable last)
                    :expand ((last clause))))))

  (defthm clause-to-term-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (expev (conjoin-clauses (clause-to-term clause)) a))
             (expev (disjoin clause) a))
    :rule-classes :clause-processor))



;; (defmacro just-induct-and-expand (term &key expand-others lambdasp mark-only)
;;   `'(:computed-hint-replacement
;;      ((and (equal (car id) '(0))
;;            '(:induct ,term))
;;       (and (equal (car id) '(0 1))
;;            (just-expand (,term . ,expand-others) :lambdasp ,lambdasp
;;                         :last-only t
;;                         :mark-only ,mark-only))
;;       '(:do-not nil))
;;      :clause-processor clause-to-term
;;      :do-not '(preprocess simplify)))


(defmacro just-induct-and-expand (term &key expand-others lambdasp)
  `(if (equal (car id) '(0))
       (b* ((hints (just-expand-cp-parse-hints (cons ',term ',expand-others) (w state)))
            (cproc `(mark-expands-cp clause '(nil ,',lambdasp ,hints))))
         `(:computed-hint-replacement
           ((and (equal (car id) '(0)) '(:clause-processor clause-to-term))
            (and (equal (car id) '(0)) '(:induct ,',term)))
           :clause-processor ,cproc))
     (and (equal (car id) '(0 1))
          (expand-marked :last-only t))))



(defun just-induct/expand-default-hint (fnname id wait-til-stablep world)
  (declare (Xargs :mode :program))
  ;; This is a version that can be used as a default hint such as for
  ;; std::define returnspec theorems or fty::deffixequiv forms.  To install, use either
  ;;
  ;;  (std::set-returnspec-default-hints
  ;;   ((just-induct/expand-default-hint 'fnname id t world)))
  ;;
  ;; to wait until stable after inducting to expand calls, or
  ;;
  ;;  (std::set-returnspec-default-hints
  ;;   ((just-induct/expand-default-hint 'fnname id nil world)))
  ;;
  ;; to expand calls of the function immediately after inducting.
  ;;
  ;; (replace with set-deffixequiv-default-hints to use in deffixequiv proofs.)
  (and (eql (len (acl2::recursivep fnname t world)) 1) ;; singly recursive
       (eql 0 (acl2::access acl2::clause-id id :forcing-round))
       (let* ((pool-lst (acl2::access acl2::clause-id id :pool-lst))
              (formals (fgetprop fnname 'formals nil world)))
         (cond ((not pool-lst)
                `(:induct (,fnname . ,formals)
                  :in-theory (disable (:d ,fnname))))
               ((equal pool-lst '(1))
                (let ((expand-hints (just-expand-cp-parse-hints
                                     `((:free ,formals (,fnname . ,formals))) world)))
                  `(:computed-hint-replacement
                    ((and (or (not ',wait-til-stablep) stable-under-simplificationp)
                          (expand-marked)))
                    :clause-processor (mark-expands-cp clause '(t t ,expand-hints)))))))))

(defun just-expand-mrec-expanders (fns world)
  (declare (Xargs :mode :program))
  (if (atom fns)
      nil
    (let ((formals (fgetprop (car fns) 'formals nil world)))
      (cons `(:free ,formals (,(car fns) . ,formals))
            (just-expand-mrec-expanders (cdr fns) world)))))

(defun just-expand-mrec-default-hint (fnname id wait-til-stablep world)
  (declare (Xargs :mode :program))
  ;; This is a version that can be used as a default hint for mutual recursions
  ;; such as std::defines returnspec theorems or deffixequiv-mutual forms.  It
  ;; doesn't provide the induction hint; it expects the flag defthm form to
  ;; provide one.  To install, use, e.g.,
  ;;
  ;;  (std::set-returnspec-mrec-default-hints
  ;;   ((just-expand-mrec-default-hint 'fnname id t world)))
  ;;
  ;; where the 't' says to wait until stable after inducting to expand calls,
  ;; which is usually preferable for mutual inductions because there are
  ;; extraneous cases that simple Boolean logic should get rid of before
  ;; expanding calls.
  (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
       (equal '(1) (acl2::access acl2::clause-id id :pool-lst))
       (let* ((fns (acl2::recursivep fnname t world))
              (expand-hints (just-expand-cp-parse-hints
                             (just-expand-mrec-expanders fns world)
                             world)))
         `(:computed-hint-replacement
           ((and (or (not ',wait-til-stablep) stable-under-simplificationp)
                 (expand-marked)))
           :in-theory (disable . ,fns)
           :clause-processor (mark-expands-cp clause '(t t ,expand-hints))))))

(defun all-fns-in-cliques (fnnames world)
  (declare (Xargs :mode :program))
  (if (atom fnnames)
      nil
    (append (recursivep (car fnnames) t world)
            (all-fns-in-cliques (cdr fnnames) world))))

(defun just-expand-mrec-multi-hint (fnnames id wait-til-stablep world)
  (declare (Xargs :mode :program))
  (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
       (equal '(1) (acl2::access acl2::clause-id id :pool-lst))
       (let* ((fns (all-fns-in-cliques fnnames world))
              (expand-hints (just-expand-cp-parse-hints
                             (just-expand-mrec-expanders fns world)
                             world)))
         `(:computed-hint-replacement
           ((and (or (not ',wait-til-stablep) stable-under-simplificationp)
                 (expand-marked)))
           :in-theory (disable . ,fns)
           :clause-processor (mark-expands-cp clause '(t t ,expand-hints))))))


(local
 (progn
   ;; just a test

   (defun ind (x y z)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x)
         (list z y)
       (if (eq y nil)
           (cons x z)
         (ind (cdr x) (nthcdr z y) z))))

   ;; The following fails because y gets substituted out too quickly:
   ;; (defthm true-listp-ind
   ;;   (implies (true-listp z)
   ;;            (true-listp (ind x y z)))
   ;;   :hints (("goal" :in-theory (disable (:definition ind))
   ;;            :induct (ind x y z)
   ;;            :expand ((ind x y z)))))

   (encapsulate nil
     (value-triple 'just-induct-test)
     (local (in-theory (disable (:definition ind))))
     (local
      (defthm true-listp-ind
        (implies (true-listp z)
                 (true-listp (ind x y z)))
        :hints (;; ("goal" :in-theory (disable (:definition ind))
                ;;  :do-not-induct t)
                (just-induct-and-expand (ind x y z))))))
   (encapsulate nil
     (value-triple 'just-induct-mark-only-test)
     (local
      (defthm true-listp-ind
        (implies (true-listp z)
                 (true-listp (ind x y z)))
        :hints (;; ("goal" :in-theory (disable (:definition ind))
                ;;  :do-not-induct t)
                (just-induct-and-expand (ind x y z))
                ;; (and stable-under-simplificationp
                ;;      '(:in-theory (e/d (expand-marked-meta)
                ;;                        (ind))))
                ))))))
