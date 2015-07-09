; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "is anyone using this?  If so please remove this message.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; util-definitions.lisp
;; John D. Powell
;(in-package "UTIL")

;;
;; This file isolates util definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the util book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(defun subterm-rec (x y)
  (declare (type t x y))
  (if (consp y)
      (let ((term (car y)))
        (or (equal x term)
            (and (consp term)
                 (subterm-rec x (cdr term)))
            (subterm-rec x (cdr y))))
    nil))

(defun subterm-p (x y)
  (declare (type t x y))
  (and (consp y)
       (subterm-rec x (cdr y))))

;; We rewrite larger symbols into smaller symbols and smaller (non
;; constant) terms into larger terms.

;; What about (equiv ram (goo ram)) ?  - presumably we would want to
;; eliminate (goo ram) ?  Which is to say, if one is a subterm of the
;; other, prehaps we should collapse the larger term into the smaller
;; term ?

(defun good-rewrite-order (x y)
  (declare (xargs :mode :program))
  (if (and (symbolp x)
           (symbolp y))
      (smaller-term y x)
    (if (quotep x)
        (and (quotep y)
             (<< (cadr y) (cadr x)))
      (or (quotep y)
          (and (smaller-term x y)
               (not (subterm-p x y)))
          (subterm-p y x)))))

;; This library should be used more extensively , for example IHS.

;;
;; fixequiv is an equivalence relation for "fix"
;;

(defun fixequiv (x y)
  (equal (fix x) (fix y)))

(defthm acl2-numberp-fix
  (acl2-numberp (fix x)))

(defthm acl2-numberp-implies-fix-reduction
  (implies
   (acl2-numberp x)
   (equal (fix x) x))
  :hints (("Goal" :in-theory (enable fix))))

(defthm fixequiv-fix
  (fixequiv (fix x) x))

;; Which other functions would benefit from this ?

(defthmd equal-fix
  (and
   (equal (equal (fix x) y)
          (and
           (acl2-numberp y)
           (fixequiv x y)))
   (equal (equal y (fix x))
          (and
           (acl2-numberp y)
           (fixequiv y x)))))

(defthm <=-commute-implies-fixequiv
  (implies
   (and
    (<= a x)
    (<= x a))
   (fixequiv a x))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (fix fixequiv)
                                  (equal-fix)))))

(defthm <-from-<=-not-fixequiv-implies-<
  (implies
   (and
    (<= a x)
    (not (fixequiv a x)))
   (< a x)))

(in-theory (disable fixequiv))
(in-theory (disable fix))

;;
;; fixlist-equiv
;;

(defun fixlist (list)
  (if (consp list)
      (cons (fix (car list))
            (fixlist (cdr list)))
    nil))

; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
; definition.
(defun acl2-number-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (acl2-numberp (car l))
                (acl2-number-listp (cdr l))))))

(defthm acl2-number-listp-fixlist
  (acl2-number-listp (fixlist list)))

(defthm acl2-number-listp-fixlist-reduction
  (implies
   (acl2-number-listp list)
   (equal (fixlist list) list)))

(defun fixlist-equiv (x y)
  (equal (fixlist x)
         (fixlist y)))

(defthm fixlist-equiv-definition
  (equal (fixlist-equiv x y)
         (if (consp x)
             (and (consp y)
                  (fixequiv (car x) (car y))
                  (fixlist-equiv (cdr x) (cdr y)))
           (not (consp y))))
  :hints (("Goal" :in-theory (enable equal-fix)))
  :rule-classes (:definition))

(defthm fixlist-equiv-fixlist-reduction
  (fixlist-equiv (fixlist x) x))

(in-theory (disable fixlist-equiv))

;;
;; A means of evaluating constant expressions.
;;

(defun def::subtype-events (name args declare body)

  (declare (xargs :mode :program))

  (let ((implies-name (packn-pos (list "IMPLIES-" name) name))
        (name-implies (packn-pos (list name "-IMPLIES") name)))

    `(encapsulate
         ()

       (defun ,name ,args
         ,@declare
         ,body)

       (defthm ,implies-name
         (implies
          ,body
          (,name ,@args)))

       (defthm ,name-implies
         (implies
          (,name ,@args)
          ,body)
         :rule-classes (:rewrite :forward-chaining))

       (in-theory (disable (:rewrite ,name-implies)))
       (in-theory (disable ,name))

       (rule-set type-backchain (:rewrite ,name-implies))
       (rule-set type-definitions ,name)

       )))

(defun subtype-strip-decls-rec (body list)
  (if (consp list)
      (met ((decls res) (subtype-strip-decls-rec (car list) (cdr list)))
           (mv (cons body decls) res))
    (mv nil body)))

(defun subtype-strip-decls (list)
  (if (consp list)
      (subtype-strip-decls-rec (car list) (cdr list))
    (mv nil nil)))

;;====================================================================
;;
;; Here are some functions for constructing fancy documentation.
;; Perhaps we shouldn just put documentation support into a separate
;; "doc" package.
;;
;;====================================================================

(defun href (x)
  (concatenate 'string "~il[" x "]"))

(defun docref (x)
  (concatenate 'string "~l[" x "]"))

(defun \n () "~nl[]")

(defun verbatim (x)
  (concatenate 'string "~bv[]" x "~ev[]"))

(defun quoted (x)
  (concatenate 'string "~bq[]" x "~eq[]"))

(defun clause-eval-clique (x)
  (declare (ignore x))
  t)

(defthm clause-eval-clique-theorem
  (clause-eval-clique (clause-eval x a)))

(defthm clause-eval-disjoin2
  (iff (clause-eval (disjoin2 x y) a)
       (or (clause-eval x a)
           (clause-eval y a))))

(defthm clause-eval-conjoin2
  (iff (clause-eval (conjoin2 x y) a)
       (and (clause-eval x a)
            (clause-eval y a))))

(in-theory (disable disjoin2 conjoin2))

(defthm open-disjoin
  (equal (disjoin (cons a list))
         (if (consp list)
             (disjoin2 a (disjoin list))
           a)))

(defthm clause-eval-disjoin
  (and
   (implies
    (not (consp list))
    (iff (clause-eval (disjoin list) a) nil))
   (implies
    (consp list)
    (iff (clause-eval (disjoin list) a)
         (or (clause-eval (car list) a)
             (clause-eval (disjoin (cdr list)) a))))))

(in-theory (disable disjoin))

(defthm open-conjoin
  (equal (conjoin (cons a list))
         (if (consp list)
             (conjoin2 a (conjoin list))
           a)))

(defthm clause-eval-conjoin
  (and
   (implies
    (not (consp list))
    (iff (clause-eval (conjoin list) a) t))
   (implies
    (consp list)
    (iff (clause-eval (conjoin list) a)
         (and (clause-eval (car list) a)
              (clause-eval (conjoin (cdr list)) a))))))

(in-theory (disable conjoin))

(defun clause-not (x)
  `(if ,x (quote nil) (quote t)))

(defun clause-implies (x y)
  `(if ,x ,y (quote t)))

;; We use clause-cons to add a "true fact" to a list of clauses.
;; To do this, we must negate the term.

(defun clause-cons (a clause)
  (cons (clause-not a) clause))

(defthm clause-eval-clause-not
  (iff (clause-eval (clause-not x) a)
       (not (clause-eval x a))))

(defthm clause-eval-clause-implies
  (iff (clause-eval (clause-implies x y) a)
       (implies (clause-eval x a)
                (clause-eval y a))))

(in-theory (disable clause-not))
(in-theory (disable clause-implies))

(defthm equal-booleans-reducton
  (implies
   (and
    (booleanp x)
    (booleanp y))
   (equal (equal x y)
          (iff x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm iff-reduction
  (equal (iff x y)
         (and (implies x y)
              (implies y x))))

(defun ifixequiv (x y)
  (equal (ifix x) (ifix y)))

(defthm ifixequiv-ifix
  (ifixequiv (ifix x) x))

#+joe
(defthm default-ifix
  (implies
   (not (integerp x))
   (ifixequiv x 0)))

(defthmd equal-ifix
  (equal (equal (ifix x) y)
         (and (integerp y)
              (ifixequiv x y))))

(in-theory (disable ifixequiv))

(in-theory (disable ifix))

;; For when you want the convenience of "nth" without the annoying
;; guard overhead.

(defun ith (n list)
  (declare (type t n list))
  (if (consp list)
      (if (zp (nfix n))
          (car list)
        (ith (1- n) (cdr list)))
    nil))

(defthm open-ith-not-zp
  (implies
   (not (zp n))
   (equal (ith n list)
          (ith (1- n) (cdr list)))))

(defthm open-ith-consp
  (implies
   (consp list)
   (equal (ith n list)
          (if (zp n) (car list)
            (ith (1- n) (cdr list))))))

(defthm ith-non-increasing
  (<= (acl2-count (ith n list)) (acl2-count list))
  :rule-classes (:linear))

;; If you need other rules about ith, you might want to switch over to nth

(defthmd ith-to-nth
  (equal (ith n list)
         (nth n list)))

;We make our own mv-nth function, so that we can disable it without getting theory warnings
;about how mv-nth cannot be completely disabled (since it is built-in in a deep way).
(defund val (n l)
  (declare (xargs :guard (and (integerp n)
                              (>= n 0)
                              (true-listp l))))
  (mv-nth n l))

(defthm mv-nth-to-val
  (equal (mv-nth n l)
         (val n l))
  :hints (("Goal" :in-theory (enable val))))

(defthm val-of-cons
  (equal (val n (cons a l))
         (if (zp n)
             a
           (val (+ -1 n) l)))
  :hints (("Goal" :in-theory (e/d (val) ( mv-nth-to-val)))))

;;
;; met* is useful in formulating rewrite rules involving functions
;; returning multiple values.
;;
(defun val-map (n binding var)
  (declare (type integer n))
  (if (consp binding)
      (cons `(,(car binding) (val ,n ,var))
            (val-map (1+ n) (cdr binding) var))
    nil))

;; Faux multi-vlaued functions
;; ---------------------------

;; The macro mvlist can be used in conjunction with metlist in place
;; of mv in conjunction with mv-let/met to return and bind multiple
;; values.

(defun metlist-fn (n vars)
  (if (consp vars)
      (cons `(,(car vars) (val ,n gensym::metlist))
            (metlist-fn (1+ n) (cdr vars)))
    nil))

(defun nfixequiv (x y)
  (equal (nfix x) (nfix y)))

(defthm nfixequiv-nfix
  (nfixequiv (nfix x) x))

#+joe
(defthm default-nfix
  (implies
   (not (natp x))
   (nfixequiv x 0)))

(defthmd equal-nfix
  (equal (equal (nfix x) y)
         (and (natp y)
              (nfixequiv x y))))

(in-theory (disable nfixequiv))

(in-theory (disable nfix))

(defthm not-hide-forward
  (implies
   (not (hide x))
   (not x))
  :hints (("Goal" :expand (hide x)))
  :rule-classes (:forward-chaining))

(defthm not-rewrite-equiv-forward
  (implies
   (not (rewrite-equiv term))
   (not term))
  :rule-classes (:forward-chaining))

(defun member? (x list)
  (declare (type t x list))
  (if (consp list)
      (or (equal x (car list))
          (member? x (cdr list)))
    nil))

(defun equiv-var-term (equivs term)
  (declare (xargs :mode :program))
  (and (consp term)
       (equal (car term) 'not)
       (consp (cdr term))
       (consp (cadr term))
       (let ((term (cadr term)))
         (and (member? (car term) equivs)
              (consp (cdr term))
              (consp (cddr term))
              (let ((lhs (cadr term))
                    (rhs (caddr term)))
                (or (and (good-rewrite-order lhs rhs) `(not (hide (rewrite-equiv ,term))))
                    (and (good-rewrite-order rhs lhs) `(not (hide (rewrite-equiv (,(car term) ,rhs ,lhs)))))
                    nil))))))

(defun find-equiv (equivs clause)
  (declare (xargs :mode :program))
  (if (consp clause)
      (let ((term (car clause)))
        (let ((nterm (equiv-var-term equivs term)))
          (or (and nterm (cons term nterm))
              (find-equiv equivs (cdr clause)))))
    nil))

(defun clause-contains (term1 clause)
  (declare (type t clause))
  (if (consp clause)
      (or (equal (car clause) term1)
          (clause-contains term1 (cdr clause)))
    nil))

(defun replace-1 (term1 term2 clause)
  (declare (type t term1 term2 clause))
  (if (consp clause)
      (if (equal (car clause) term1)
          (cons term2 (cdr clause))
        (cons (car clause)
              (replace-1 term1 term2 (cdr clause))))
    nil))

(defun rewrite-equiv-clause-processor (clause hints)
  (if (consp hints)
      (let ((term1 (car hints))
            (term2 (cdr hints)))
        (let ((clause (replace-1 term1 term2 clause)))
          (list
           clause
           (list (clause-implies term2 term1)))))
    (list clause)))

(local (in-theory (disable alistp)))

(defthm rewrite-equiv-clause-processor-works
  (implies
   (and
    (pseudo-term-listp cl)
    (alistp a)
    (rewrite-equiv-eval (conjoin-clauses
                         (rewrite-equiv-clause-processor cl hints)) a))
   (rewrite-equiv-eval (disjoin cl) a))
  :rule-classes :clause-processor
  :otf-flg t)

;;
;; This would probably work better as a clause processor.
;;
;; What we would need to do is to create two subgoals: one
;; containing the new rewrite-equiv in place of the equivalence
;; and the other with an assertion that the old equivalence
;; justified the replacment.
;;
(defun slow-rewrite-equiv-hint (stbl old equivs clause)
  (declare (xargs :mode :program))
  (if (and old (clause-contains old clause)) nil
    (let ((default (and old `(:COMPUTED-HINT-REPLACEMENT
                              ((slow-rewrite-equiv-hint stable-under-simplificationp nil ',equivs clause))
                              :cases (t)
                              ))))
      (or (and (or old stbl)
               (let ((hint (find-equiv equivs (reverse clause))))
                 (or (and hint
                          (let ((old (car hint)))
                            (let ((hint `(:clause-processor (rewrite-equiv-clause-processor clause ',hint))))
                              `(:COMPUTED-HINT-REPLACEMENT
                                ((slow-rewrite-equiv-hint stable-under-simplificationp ',old ',equivs clause))
                                ,@hint
                                ))))
                     default)))
          default))))

;;
;; OK .. again without clause processors.
;;
#+joe
(defun slow-rewrite-equiv-hint (stbl old equivs clause)
  (declare (xargs :mode :program))
  (if (and old (clause-contains old clause)) nil
    (let ((default (and old `(:COMPUTED-HINT-REPLACEMENT
                              ((slow-rewrite-equiv-hint stable-under-simplificationp nil ',equivs clause))
                              ))))
      (or (and (or stbl old)
               (let ((hint (find-equiv equivs clause)))
                 (or (and hint
                          (let ((old (car hint))
                                (new (cdr hint)))
                            `(:COMPUTED-HINT-REPLACEMENT
                              ((slow-rewrite-equiv-hint stable-under-simplificationp ',old ',equivs clause))
                              :cases (,new))))
                     default)))
          default))))

;; ===================================================================
;;
;; The data structure used to hold the rule set state.
;;
;; ===================================================================

;; DAG - Should come from "lists"
(defthm true-listp-append-rewrite
  (equal (true-listp (append x y))
         (true-listp y)))

(defun wf-rule-list (list)
  (declare (type t list))
  (true-listp list))

(defthm wf-rule-list-implies-true-listp
  (implies
   (wf-rule-list list)
   (true-listp list))
  :rule-classes (:forward-chaining))

;; ===================================================================
;;
;; wf-set-ref: A reference to a rule set (or library).  It is either
;; an atom (just the name of the set) or a cons pair in which the
;; first atom is the name of the set and the second is the specific
;; version of that set.
;;
;; ===================================================================

(defun wf-set-ref (ref)
  (declare (type t ref))
  (or (eqlablep ref)
      (and (consp ref)
           (eqlablep (car ref))
           (eqlablep (cdr ref)))))

(defthm wf-set-ref-not-consp
  (implies
   (and
    (wf-set-ref ref)
    (not (consp ref)))
   (eqlablep ref))
  :rule-classes (:forward-chaining))

(defthm wf-set-ref-consp
  (implies
   (and
    (wf-set-ref ref)
    (consp ref))
   (and (eqlablep (car ref))
        (eqlablep (cdr ref))))
  :rule-classes (:forward-chaining))

(in-theory (disable wf-set-ref))

;; ===================================================================
;;
;; wf-set-ref-list: list[wf-set-ref]
;;
;; ===================================================================

(defun wf-set-ref-list (list)
  (declare (type t list))
  (if (consp list)
      (and (wf-set-ref (car list))
           (wf-set-ref-list (cdr list)))
    (null list)))

(defthm wf-set-ref-list-append
  (implies
   (true-listp x)
   (equal (wf-set-ref-list (append x y))
          (and (wf-set-ref-list x)
               (wf-set-ref-list y)))))

(defthm wf-set-ref-list-implies-true-listp
  (implies
   (wf-set-ref-list list)
   (true-listp list))
  :rule-classes (:forward-chaining))

;; ===================================================================
;;
;; A version entry data structure
;;
;; version-entry: [
;;   version: eqlablep
;;   include-rules : wf-rule-list
;;   omit-rules    : wf-rule-list
;;   include-sets  : wf-set-ref-list
;;   omit-sets     : wf-set-ref-list
;; ]
;;
;; ===================================================================

(defun weak-version-entry (entry)
  (declare (type t entry))
  (and (true-listp entry)
       (equal (len entry) 5)))

(defun versi0n (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (car entry))

(defun include-rules (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (cadr entry))

(defun omit-rules (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (caddr entry))

(defun include-sets (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (cadddr entry))

(defun omit-sets (entry)
  (declare (type (satisfies weak-version-entry) entry))
  (car (cddddr entry)))

(defun wf-version-entry (entry)
  (declare (type t entry))
  (and (weak-version-entry entry)
       (eqlablep (versi0n entry))
       (wf-rule-list (include-rules entry))
       (wf-rule-list (omit-rules entry))
       (wf-set-ref-list (include-sets entry))
       (wf-set-ref-list (omit-sets entry))))

(defthm wf-version-entry-implications
  (implies
   (wf-version-entry entry)
   (and (weak-version-entry entry)
        (eqlablep (versi0n entry))
        (wf-rule-list (include-rules entry))
        (wf-rule-list (omit-rules entry))
        (wf-set-ref-list (include-sets entry))
        (wf-set-ref-list (omit-sets entry))))
  :rule-classes (:forward-chaining))

(defthm wf-version-entry-deduction-implicit
  (implies
   (and (weak-version-entry entry)
        (eqlablep (versi0n entry))
        (wf-rule-list (include-rules entry))
        (wf-rule-list (omit-rules entry))
        (wf-set-ref-list (include-sets entry))
        (wf-set-ref-list (omit-sets entry)))
   (wf-version-entry entry))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((wf-version-entry entry)))))

(defun version-entry (versi0n include-rules omit-rules include-sets omit-sets)
  (declare (type (satisfies eqlablep) versi0n)
           (type (satisfies wf-rule-list) include-rules omit-rules)
           (type (satisfies wf-set-ref-list) include-sets omit-sets))
  (list versi0n include-rules omit-rules include-sets omit-sets))

(defthm version-entry-is-weak-version-entry
  (weak-version-entry (version-entry versi0n include-rules omit-rules include-sets omit-sets))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((version-entry versi0n include-rules omit-rules include-sets omit-sets)))))


(defthm version-entry-accessor-of-constructor
  (and
   (equal (versi0n (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          versi0n)
   (equal (include-rules (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          include-rules)
   (equal (omit-rules (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          omit-rules)
   (equal (include-sets (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          include-sets)
   (equal (omit-sets (version-entry versi0n include-rules omit-rules include-sets omit-sets))
          omit-sets)))

(defthm wf-version-entry-deduction-explicit
  (implies
   (and (eqlablep versi0n)
        (wf-rule-list include-rules)
        (wf-rule-list omit-rules)
        (wf-set-ref-list include-sets)
        (wf-set-ref-list omit-sets))
   (wf-version-entry (version-entry versi0n include-rules omit-rules include-sets omit-sets)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((version-entry versi0n include-rules omit-rules include-sets omit-sets)))))

(in-theory (disable wf-version-entry weak-version-entry version-entry))
(in-theory (disable versi0n include-rules omit-rules include-sets omit-sets))

;; ===================================================================
;;
;; wf-version-list: list[wf-version-entry]
;;
;; ===================================================================

(defun wf-version-list (list)
  (declare (type t list))
  (if (consp list)
      (and (wf-version-entry (car list))
           (wf-version-list (cdr list)))
    (null list)))

(defthm wf-version-list-implies-true-listp
  (implies
   (wf-version-list list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defun contains-version-entry (set list)
  (declare (type (satisfies eqlablep) set)
           (type (satisfies wf-version-list) list))
  (if (consp list)
      (or (equal set (versi0n (car list)))
          (contains-version-entry set (cdr list)))
    nil))

(defun get-version-entry (set list)
  (declare (type (satisfies eqlablep) set)
           (type (satisfies wf-version-list) list))
  (if (consp list)
      (if (equal set (versi0n (car list)))
          (car list)
        (get-version-entry set (cdr list)))
    (new-version-entry :version set)))

(defthm wf-version-entry-get-version-entry
  (implies
   (and
    (wf-version-list list)
    (eqlablep set))
   (wf-version-entry (get-version-entry set list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms
                                    ((get-version-entry set list)))))

(defun set-version-entry (set entry list)
  (declare (type (satisfies wf-version-list) list)
           (type (satisfies eqlablep) set)
           (type (satisfies wf-version-entry) entry))
  (if (consp list)
      (if (equal set (versi0n (car list)))
          (cons entry (cdr list))
        (cons (car list) (set-version-entry set entry (cdr list))))
    (list entry)))

(defthm wf-version-list-set-version-entry
  (implies
   (and
    (wf-version-entry entry)
    (wf-version-list list))
   (wf-version-list (set-version-entry set entry list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms
                                    ((set-version-entry set entry list)))))

;; ===================================================================
;;
;; A rule set entry data structure
;;
;; rule-set-entry : [
;;   set-name: eqlablep
;;   default-set-version: eqlablep
;;   version-list: wf-version-list
;; ]
;;
;; ===================================================================

(defun weak-rule-set-entry (entry)
  (declare (type t entry))
  (and (true-listp entry)
       (equal (len entry) 3)))

(defun set-name (entry)
  (declare (type (satisfies weak-rule-set-entry) entry))
  (car entry))

(defun default-set-version (entry)
  (declare (type (satisfies weak-rule-set-entry) entry))
  (cadr entry))

(defun version-list (entry)
  (declare (type (satisfies weak-rule-set-entry) entry))
  (caddr entry))

(defun wf-rule-set-entry (entry)
  (declare (type t entry))
  (and (weak-rule-set-entry entry)
       (eqlablep (set-name entry))
       (eqlablep (default-set-version entry))
       (wf-version-list (version-list entry))))

(defthm wf-rule-set-entry-implications
  (implies
   (wf-rule-set-entry entry)
   (and (weak-rule-set-entry entry)
        (eqlablep (set-name entry))
        (eqlablep (default-set-version entry))
       (wf-version-list (version-list entry))))
  :rule-classes (:forward-chaining))

(defthm wf-rule-set-entry-deduction-implicit
  (implies
   (and (weak-rule-set-entry entry)
        (eqlablep (set-name entry))
        (eqlablep (default-set-version entry))
       (wf-version-list (version-list entry)))
   (wf-rule-set-entry entry))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((wf-rule-set-entry entry)))))

(defun rule-set-entry (set-name default-set-version version-list)
  (declare (type (satisfies eqlablep) set-name default-set-version)
           (type (satisfies wf-version-list) version-list))
  (list set-name default-set-version version-list))

(defthm rule-set-entry-is-weak-rule-set-entry
  (weak-rule-set-entry (rule-set-entry set-name default-set-version version-list))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((rule-set-entry set-name default-set-version version-list)))))


(defthm rule-set-entry-accessor-of-constructor
  (and
   (equal (set-name (rule-set-entry set-name default-set-version version-list))
          set-name)
   (equal (default-set-version (rule-set-entry set-name default-set-version version-list))
          default-set-version)
   (equal (version-list (rule-set-entry set-name default-set-version version-list))
          version-list)))

(defthm wf-rule-set-entry-deduction-explicit
  (implies
   (and (eqlablep set-name)
        (eqlablep default-set-version)
        (wf-version-list version-list))
   (wf-rule-set-entry (rule-set-entry set-name default-set-version version-list)))
  :rule-classes ((:forward-chaining :trigger-terms
                                    ((rule-set-entry set-name default-set-version version-list)))))

(in-theory (disable wf-rule-set-entry weak-rule-set-entry rule-set-entry))
(in-theory (disable set-name default-set-version version-list))

;; ===================================================================
;;
;; wf-rule-set-list: list[wf-rule-set-entry]
;;
;; ===================================================================

(defun wf-rule-set-list (list)
  (declare (type t list))
  (if (consp list)
      (and (wf-rule-set-entry (car list))
           (wf-rule-set-list (cdr list)))
    (null list)))

(defthm wf-rule-set-list-implies-true-listp
  (implies
   (wf-rule-set-list list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defun contains-rule-set-entry (set list)
  (declare (type (satisfies eqlablep) set)
           (type (satisfies wf-rule-set-list) list))
  (if (consp list)
      (or (equal set (set-name (car list)))
          (contains-rule-set-entry set (cdr list)))
    nil))

(defun get-rule-set-entry (set list)
  (declare (type (satisfies eqlablep) set)
           (type (satisfies wf-rule-set-list) list))
  (if (consp list)
      (if (equal set (set-name (car list)))
          (car list)
        (get-rule-set-entry set (cdr list)))
    (new-rule-set-entry :set-name set)))

(defthm wf-rule-set-entry-get-rule-set-entry
  (implies
   (and
    (wf-rule-set-list list)
    (eqlablep set))
   (wf-rule-set-entry (get-rule-set-entry set list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms
                                    ((get-rule-set-entry set list)))))

(defun set-rule-set-entry (set entry list)
  (declare (type (satisfies wf-rule-set-list) list)
           (type (satisfies eqlablep) set)
           (type (satisfies wf-rule-set-entry) entry))
  (if (consp list)
      (if (equal set (set-name (car list)))
          (cons entry (cdr list))
        (cons (car list) (set-rule-set-entry set entry (cdr list))))
    (list entry)))

(defthm wf-rule-set-list-set-rule-set-entry
  (implies
   (and
    (wf-rule-set-entry entry)
    (wf-rule-set-list list))
   (wf-rule-set-list (set-rule-set-entry set entry list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms
                                    ((set-rule-set-entry set entry list)))))

;; ===================================================================
;;
;; The rule set data structure
;;
;; rule-set: [
;;  default-library : eqlablep
;;  default-version : eqlablep
;;  rule-set-list   : wf-rule-set-list
;; ]
;;
;; ===================================================================

(defun weak-rule-set (set)
  (declare (type t set))
  (and (true-listp set)
       (equal (len set) 3)))

(defun default-library (rule-set)
  (declare (type (satisfies weak-rule-set) rule-set))
  (car rule-set))

(defun default-version (rule-set)
  (declare (type (satisfies weak-rule-set) rule-set))
  (cadr rule-set))

(defun rule-set-list (rule-set)
  (declare (type (satisfies weak-rule-set) rule-set))
  (caddr rule-set))

(defun wf-rule-set (set)
  (declare (type t set))
  (and (weak-rule-set set)
       (eqlablep (default-library set))
       (eqlablep (default-version set))
       (wf-rule-set-list (rule-set-list set))))

(defthm wf-rule-set-implications
  (implies
   (wf-rule-set set)
   (and (weak-rule-set set)
        (eqlablep (default-library set))
        (eqlablep (default-version set))
        (wf-rule-set-list (rule-set-list set))))
  :rule-classes (:forward-chaining))

(defthm wf-rule-set-deduction-implicit
  (implies
   (and (weak-rule-set set)
        (eqlablep (default-library set))
        (eqlablep (default-version set))
        (wf-rule-set-list (rule-set-list set)))
   (wf-rule-set set))
  :rule-classes (:rewrite :forward-chaining))


;; Constructor
;;
(defun rule-set (default-library default-version rule-set-list)
  (declare (type (satisfies eqlablep) default-library)
           (type (satisfies eqlablep) default-version)
           (type (satisfies wf-rule-set-list) rule-set-list))
  (list default-library default-version rule-set-list))

(defthm rule-set-is-weak-rule-set
  (weak-rule-set (rule-set default-library default-version rule-set-list))
  :rule-classes ((:forward-chaining :trigger-terms
                                    ((rule-set default-library default-version rule-set-list)))))

(defthm rule-set-accessor-of-constructor
  (and
   (equal (default-library (rule-set default-library default-version rule-set-list))
          default-library)
   (equal (default-version (rule-set default-library default-version rule-set-list))
          default-version)
   (equal (rule-set-list (rule-set default-library default-version rule-set-list))
          rule-set-list)))

(defthm wf-rule-set-deduction-explicit
  (implies
   (and (eqlablep default-library)
        (eqlablep default-version)
        (wf-rule-set-list rule-set-list))
   (wf-rule-set (rule-set default-library default-version rule-set-list)))
  :rule-classes ((:forward-chaining :trigger-terms
                                    ((rule-set default-library default-version rule-set-list)))))

(in-theory (disable wf-rule-set weak-rule-set rule-set))
(in-theory (disable default-library default-version rule-set-list))

;; ===================================================================
;;
;; Utility functions for manipulating the rule-set data structure
;;
;; ===================================================================

;; ===================================================================
;; add-rules-to-ref-in-rule-set
;; ===================================================================

(defun add-rules-to-ref-in-rule-set (ref include-rules omit-rules rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-rule-list) include-rules omit-rules)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list  (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (rule-set-entry (get-rule-set-entry key rule-set-list))
         (version-list   (version-list rule-set-entry))
         (version        (if (consp ref) (cdr ref) (default-set-version rule-set-entry)))
         (version-entry  (get-version-entry version version-list))
         (version-entry  (update-version-entry version-entry
                                               :include-rules (append include-rules
                                                                      (include-rules version-entry))
                                               :omit-rules (append omit-rules
                                                                   (omit-rules version-entry))))
         (version-list   (set-version-entry version version-entry version-list))
         (rule-set-entry (update-rule-set-entry rule-set-entry
                                                :version-list version-list))
         (rule-set-list  (set-rule-set-entry key rule-set-entry rule-set-list)))
    (update-rule-set rule-set
                     :rule-set-list rule-set-list)))

(defthm wf-rule-set-add-rules-to-ref-in-rule-set
  (implies
   (and
    (wf-set-ref ref)
    (wf-rule-list include-rules)
    (wf-rule-list omit-rules)
    (wf-rule-set rule-set))
   (wf-rule-set (add-rules-to-ref-in-rule-set ref include-rules omit-rules rule-set)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((add-rules-to-ref-in-rule-set ref include-rules omit-rules rule-set)))))

(in-theory (disable add-rules-to-ref-in-rule-set))

;; ===================================================================
;; add-sets-to-ref-in-rule-set
;; ===================================================================

;; o Check to make sure that all of the sets being
;;   added actually exist before we call this.

(defun add-sets-to-ref-in-rule-set (ref include-sets omit-sets rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-set-ref-list) include-sets omit-sets)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list  (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (rule-set-entry (get-rule-set-entry key rule-set-list))
         (version-list   (version-list rule-set-entry))
         (version        (if (consp ref) (cdr ref) (default-set-version rule-set-entry)))
         (version-entry  (get-version-entry version version-list))
         (version-entry  (update-version-entry version-entry
                                               :include-sets (append include-sets
                                                                      (include-sets version-entry))
                                               :omit-sets (append omit-sets
                                                                   (omit-sets version-entry))))
         (version-list   (set-version-entry version version-entry version-list))
         (rule-set-entry (update-rule-set-entry rule-set-entry
                                                :version-list version-list))
         (rule-set-list  (set-rule-set-entry key rule-set-entry rule-set-list)))
    (update-rule-set rule-set
                     :rule-set-list rule-set-list)))

(defthm wf-rule-set-add-sets-to-ref-in-rule-set
  (implies
   (and
    (wf-set-ref ref)
    (wf-set-ref-list include-sets)
    (wf-set-ref-list omit-sets)
    (wf-rule-set rule-set))
   (wf-rule-set (add-sets-to-ref-in-rule-set ref include-sets omit-sets rule-set)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((add-sets-to-ref-in-rule-set ref include-sets omit-sets rule-set)))))

(in-theory (disable add-sets-to-ref-in-rule-set))

;; ===================================================================
;; set-ref-default-version-in-rule-set
;; ===================================================================

(defun set-ref-default-version-in-rule-set (ref version rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies eqlablep) version)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list  (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (rule-set-entry (get-rule-set-entry key rule-set-list))
         (rule-set-entry (update-rule-set-entry rule-set-entry
                                                :default-set-version version))
         (rule-set-list  (set-rule-set-entry key rule-set-entry rule-set-list)))
    (update-rule-set rule-set
                     :rule-set-list rule-set-list)))

;; ===================================================================
;; set-default-library
;; ===================================================================

(defun set-default-library (ref rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((key            (if (consp ref) (car ref) ref))
         (version        (if (consp ref) (cdr ref) nil)))
    (update-rule-set rule-set
                     :default-library key
                     :default-version version)))

;; ===================================================================
;; get-default-library-ref
;; ===================================================================

(defun get-default-library-ref (rule-set)
  (declare (type (satisfies wf-rule-set) rule-set))
  (cons (default-library rule-set)
        (default-version rule-set)))

;; ===================================================================
;; d/e list:
;;
;;   A list containing pairs of lists.  The first list in a given pair
;; is the disable set, the second is an enable set.
;;
;; The following functions are all in :program mode because we don't
;; have a guarantee (don't care to ensure) that they terminate ..
;; although we do what we can in the construction of the rule-set data
;; structure to ensure that they will.
;;
;; ref-to-de:
;;
;;   Computes a d/e list from a reference
;;
;; ref-to-disable:
;;
;;   Computes a disable list from a reference
;;
;; ref-list-to-de:
;;
;;   Maps ref-to-de over a list of references.
;;
;; ref-list-to-disable:
;;
;;   Maps ref-to-disable over a list of references.
;;
;; ===================================================================

(mutual-recursion

 (defun ref-list-to-disable (list rule-set disable)
   (if (consp list)
       (let ((disable (ref-to-disable (car list) rule-set disable)))
         (ref-list-to-disable (cdr list) rule-set disable))
     disable))

 (defun ref-to-disable (ref rule-set disable)
   (let* ((rule-set-list  (rule-set-list rule-set))
          (key            (if (consp ref) (car ref) ref))
          (rule-set-entry (get-rule-set-entry key rule-set-list))
          (version-list   (version-list rule-set-entry))
          (version        (if (consp ref) (cdr ref) (default-set-version rule-set-entry)))
          (version-entry  (get-version-entry version version-list))
          ;;
          ;; Is there any reason to include the omit-rules here, too?
          ;;
          (disable        (append (include-rules version-entry) disable)))
     (ref-list-to-disable (include-sets version-entry) rule-set disable)))

 (defun ref-list-to-de (list rule-set res)
   (declare (xargs :mode :program))
   (if (consp list)
       (let ((res (ref-to-de (car list) rule-set res)))
         (ref-list-to-de (cdr list) rule-set res))
     res))

 (defun ref-to-de (ref rule-set res)
   (declare (xargs :mode :program))
   (let* ((rule-set-list  (rule-set-list rule-set))
          (key            (if (consp ref) (car ref) ref))
          (rule-set-entry (get-rule-set-entry key rule-set-list))
          (version-list   (version-list rule-set-entry))
          (version        (if (consp ref) (cdr ref) (default-set-version rule-set-entry)))
          (version-entry  (get-version-entry version version-list))
          (res            (cons (cons (omit-rules version-entry)
                                      (include-rules version-entry))
                                res))
          (res            (cons (list (ref-list-to-disable (omit-sets version-entry) rule-set nil))
                                res)))
     (ref-list-to-de (include-sets version-entry) rule-set res)))

 )

(defun assert (value test ctx msg)
  (declare (type t ctx msg))
  (prog2$ (if (not test) (acl2::hard-error ctx "~p0" (list (cons #\0 msg))) nil)
          value))

(defun ref-exists (ref rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (rule-set-exits (contains-rule-set-entry key rule-set-list))
         (rule-set-entry (get-rule-set-entry key rule-set-list))
         (version-list   (version-list rule-set-entry))
         (version        (if (consp ref) (cdr ref) nil))
         (version-exists (contains-version-entry version version-list)))
    (and rule-set-exits
         version-exists)))

(defun ref-set-exists (list rule-set)
  (declare (type (satisfies wf-rule-set) rule-set)
           (type (satisfies wf-set-ref-list) list))
  (if (consp list)
      (let ((ref (car list)))
        (and (ref-exists ref rule-set)
             (ref-set-exists (cdr list) rule-set)))
    t))

(defun define-new-set (ref extends omits rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-set-ref-list) extends omits)
           (xargs :guard (or (null rule-set)
                             (wf-rule-set rule-set))))
  (let* ((rule-set       (or rule-set (new-rule-set)))
         (rule-set       (assert rule-set (and (ref-set-exists extends rule-set)
                                               (ref-set-exists omits   rule-set))
                                 'define-new-set "All extended/omitted rule sets must already exist"))
         (rule-set-list  (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (version        (if (consp ref) (cdr ref) nil))

         (rule-set-entry (get-rule-set-entry key rule-set-list))
         (rule-set-entry (update-rule-set-entry rule-set-entry
                                                :default-set-version version))
         (version-list   (version-list rule-set-entry))
         (version-entry  (get-version-entry version version-list))
         (include-sets   (include-sets version-entry))
         (omit-sets      (omit-sets version-entry))
         (version-entry  (assert version-entry (and (or (null omit-sets) (equal omit-sets omits))
                                                    (or (null include-sets) (equal include-sets extends)))
                                 'define-new-set "Fundamental redefinition of rule-classes is prohibited"))
         (version-entry  (update-version-entry version-entry
                                               :include-sets extends
                                               :omit-sets omits))
         (version-list   (set-version-entry version version-entry version-list))
         (rule-set-entry (update-rule-set-entry rule-set-entry
                                                :version-list version-list))
         (rule-set-list  (set-rule-set-entry key rule-set-entry rule-set-list)))
    (update-rule-set rule-set
                     :rule-set-list rule-set-list)))

(defun query-ref (ref rule-set)
  (declare (type (satisfies wf-set-ref) ref)
           (type (satisfies wf-rule-set) rule-set))
  (let* ((rule-set-list  (rule-set-list rule-set))
         (key            (if (consp ref) (car ref) ref))
         (rule-set-entry (get-rule-set-entry key rule-set-list)))
    (if (consp ref)
        (let* ((version        (cdr ref))
               (version-list   (version-list rule-set-entry)))
          (get-version-entry version version-list))
      rule-set-entry)))

(defun alt-e/d-to-ed-list (e list rule-set)
  (declare (xargs :mode :program))
  (if (consp list)
      (append (if e (ref-list-to-de (car list) rule-set nil)
                (list (list (ref-list-to-disable (car list) rule-set nil))))
              (alt-e/d-to-ed-list (not e) (cdr list) rule-set))
    nil))

(defun d/e-list (theory list world)
  (declare (xargs :mode :program))
  (if (consp list)
      (let ((disable (caar list))
            (enable  (cdar list)))
        (acl2::union-theories-fn
         (acl2::set-difference-theories-fn
          (d/e-list theory (cdr list) world)
          disable
          t world)
         enable
         t world))
    (if (equal theory :here) (current-theory :here) theory)))

#|

  o First, implement the exising rule set infrastructure with this as
an underpinning.

  o Add additional versioning capabilities as permitted.

;; Associated with each version are:
;; - the classes to disable
;; - the classes to enable
;; - the rules to disable
;; - the rules to enable

;; - may not redefine (change) a version extension.
;; - must be defined in terms of an existing version.
;; - by default, a version extends nil (the initial version)

(defun update-library-version (new old list)
  (let ((hit (assoc new list)))
    (if (consp hit)
        (if (equal (cdr hit) old) list
          (error "Cannot Redefine"))
      (cons (cons new old) list))))
|#
