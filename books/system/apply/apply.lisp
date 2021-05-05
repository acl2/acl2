; ACL2 Version 7.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2017, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

; See the Refresher on books/system/, etc. in books/system/apply/apply-prim for
; some background.

; One way to think of this book is that it was derived by taking its source
; file counterpart, e.g., apply.lisp, and sprinkling in the include-books,
; defthms, declarations, and hints to get the source file admitted in
; guard-verified, :logic mode fashion by a version of ACL2 in which these
; functions weren't already defined.  We supply minimal comments here except
; when discussing the termination/guard verification issues.  See the
; corresponding source files for explanations of the definitions below!

(in-package "ACL2")          ; on /books/projects/apply/

; -----------------------------------------------------------------
; 0. Set-up

; The following books are needed when building ACL2 with :acl2-devel.  For
; documentation of the acl2-devel process, see :DOC
; verify-guards-for-system-functions, or see the comment in source constant
; *system-verify-guards-alist*.
#+acl2-devel
(include-book "system/legal-variablep" :dir :system)
#+acl2-devel
(include-book "system/termp" :dir :system)

; For a normal (not acl2-devel) run, we locally re-enable runes that were
; disabled during the build.
#-acl2-devel
(local (in-theory (enable apply$-primp badge-prim
                          badge (:executable-counterpart badge)
                          (:executable-counterpart tamep)
                          (:executable-counterpart tamep-functionp)
                          (:executable-counterpart suitably-tamep-listp)
                          ev$ ev$-list apply$
                          (:executable-counterpart apply$))))

; -----------------------------------------------------------------
; 1. Badges

(defun badge (fn)
  (declare (xargs :guard t))
  (cond
   ((apply$-primp fn) (badge-prim fn))
   ((eq fn 'BADGE) *generic-tame-badge-1*)
   ((eq fn 'TAMEP) *generic-tame-badge-1*)
   ((eq fn 'TAMEP-FUNCTIONP) *generic-tame-badge-1*)
   ((eq fn 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*)
   ((eq fn 'APPLY$) *apply$-badge*)
   ((eq fn 'EV$) *ev$-badge*)
; Otherwise, badge is undefined unless a warrant tells us what it is.
   (t (badge-userfn fn))))

(in-theory (disable apply$-primp badge-prim))

(defthm badge-type
  (or (null (badge fn))
      (apply$-badgep (badge fn)))
  :rule-classes
  ((:forward-chaining
    :corollary (implies (badge fn)
                        (apply$-badgep (badge fn))))))

(in-theory (disable badge))

; -----------------------------------------------------------------
; 2. Tameness

(mutual-recursion

(defun tamep (x)
  (declare (xargs :measure (acl2-count x)
                  :guard t
                  :verify-guards nil))
  (cond ((atom x) (symbolp x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cddr x))))
        ((symbolp (car x))
         (let ((bdg (badge (car x))))
           (cond
            ((null bdg) nil)
            ((eq (access apply$-badge bdg :ilks) t)
             (suitably-tamep-listp (access apply$-badge bdg :arity)
                                   nil
                                   (cdr x)))
            (t (suitably-tamep-listp (access apply$-badge bdg :arity)
                                     (access apply$-badge bdg :ilks)
                                     (cdr x))))))
        ((consp (car x))
         (let ((fn (car x)))
           (and (tamep-lambdap fn)
                (suitably-tamep-listp (length (cadr fn))
                                      nil
                                      (cdr x)))))
        (t nil)))

(defun tamep-functionp (fn)
  (declare (xargs :measure (acl2-count fn)
                  :guard t))
  (if (symbolp fn)
      (let ((bdg (badge fn)))
        (and bdg (eq (access apply$-badge bdg :ilks) t)))
    (and (consp fn)
         (tamep-lambdap fn))))

(defun suitably-tamep-listp (n flags args)

; We take advantage of the fact that (car nil) = (cdr nil) = nil.

  (declare (xargs :measure (acl2-count args)
                  :guard (and (natp n)
                              (true-listp flags))))
  (cond
   ((zp n) (null args))
   ((atom args) nil)
   (t (and
       (let ((arg (car args)))
         (case (car flags)
           (:FN
            (and (consp arg)
                 (eq (car arg) 'QUOTE)
                 (consp (cdr arg))
                 (null (cddr arg))
                 (tamep-functionp (cadr arg))))
           (:EXPR
            (and (consp arg)
                 (eq (car arg) 'QUOTE)
                 (consp (cdr arg))
                 (null (cddr arg))
                 (tamep (cadr arg))))
           (otherwise
            (tamep arg))))
       (suitably-tamep-listp (- n 1) (cdr flags) (cdr args))))))
)

(verify-guards tamep
  :hints
  (("Goal" :use ((:instance badge-type (fn fn))
                 (:instance badge-type (fn (car x)))))))

; In order to verify the guards of the apply$ clique we need various properties
; implied by tamep.  We prove them here.

; The following three events are local because they're not important to proofs
; about apply; they're just used to establish the guards.

(local
 (defun suitably-tamep-listp-induction (n flags args)
   (cond
    ((zp n) (list flags args))
    (t (suitably-tamep-listp-induction (- n 1) (cdr flags) (cdr args))))))

(local
 (defthm suitably-tamep-listp-implicant-1
   (implies (and (suitably-tamep-listp n flags args)
                 (natp n))
            (and (true-listp args)
                 (equal (len args) n)))
   :hints (("Goal" :induct (suitably-tamep-listp-induction n flags args)))
   :rule-classes :forward-chaining))

(local
 (defthm tamep-implicant-1
   (implies (and (tamep x)
                 (consp x))
            (true-listp x))
   :hints (("Goal" :expand (tamep x)
            :use ((:instance badge-type (fn (car x))))))))

; We disable the executable counterparts of tamep because badge-userfn is
; undefined, so running tamep on constants, such as (tamep '(CONS A B)) fails
; and introduces a HIDE.  However, expansion of the definitional axioms allow
; us to use the badge properties of warrants.

(in-theory (disable (:executable-counterpart tamep)
                    (:executable-counterpart tamep-functionp)
                    (:executable-counterpart suitably-tamep-listp)))

; -----------------------------------------------------------------
; 3. Definition of APPLY$ and EV$

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defun ev$-measure (x a)
  (declare (ignore a))
  (llist (acl2-count x) 0))

(defun ev$-list-measure (x a)
  (declare (ignore a))
  (llist (acl2-count x) 0))

(defun apply$-measure (fn args)
  (cond
   ((consp fn)
    (llist (acl2-count fn) 0))
   ((eq fn 'apply$)
    (llist (+ 1 (acl2-count (car args))) 0))
   ((eq fn 'ev$)
    (llist (+ 1 (acl2-count (car args))) 0))
   (t (llist 0 0))))

(defun apply$-lambda-measure (fn args)
  (declare (ignore args))
  (llist (acl2-count (lambda-object-body fn)) 1))

; We restrict the following to builds with #+acl2-devel (see :DOC
; verify-guards-for-system-functions), thus avoiding redefinition errors (due
; to the measure changing from calls of :?)  when certifying with ordinary ACL2
; builds.
#+acl2-devel
(mutual-recursion

(defun apply$ (fn args)
  (declare (xargs :guard (apply$-guard fn args)
                  :verify-guards nil
                  :guard-hints (("Goal" :do-not-induct t))
                  :measure (apply$-measure fn args)
                  :well-founded-relation l<))
  (cond
   ((consp fn)
    (apply$-lambda fn args))
   ((apply$-primp fn)
    (apply$-prim fn args))
   ((eq fn 'BADGE)
    (badge (car args)))
   ((eq fn 'TAMEP)
    (tamep (car args)))
   ((eq fn 'TAMEP-FUNCTIONP)
    (tamep-functionp (car args)))
   ((eq fn 'SUITABLY-TAMEP-LISTP)
    (ec-call (suitably-tamep-listp (car args) (cadr args) (caddr args))))
   ((eq fn 'APPLY$)
    (if (tamep-functionp (car args))
        (ec-call (APPLY$ (car args) (cadr args)))
      (untame-apply$ fn args)))
   ((eq fn 'EV$)
    (if (tamep (car args))
        (EV$ (car args) (cadr args))
      (untame-apply$ fn args)))
   (t (apply$-userfn fn args))))

(defun apply$-lambda (fn args)
  (declare (xargs :guard (apply$-lambda-guard fn args)
                  :guard-hints (("Goal" :do-not-induct t))
                  :measure (apply$-lambda-measure fn args)
                  :well-founded-relation l<))
  (apply$-lambda-logical fn args))

(defun ev$ (x a)
  (declare (xargs :guard t
                  :measure (ev$-measure x a)
                  :well-founded-relation l<))
  (cond
   ((not (tamep x))
    (untame-ev$ x a))
   ((variablep x)
    (ec-call (cdr (ec-call (assoc-equal x a)))))
   ((fquotep x)
    (cadr x))
   ((eq (car x) 'if)
    (if (ev$ (cadr x) a)
        (ev$ (caddr x) a)
      (ev$ (cadddr x) a)))
   ((eq (car x) 'APPLY$)
    (apply$ 'APPLY$
            (list (cadr (cadr x)) (EV$ (caddr x) a))))
   ((eq (car x) 'EV$)
    (apply$ 'EV$ (list (cadr (cadr x)) (EV$ (caddr x) a))))
   (t
    (APPLY$ (car x)
            (EV$-LIST (cdr x) a)))))

(defun ev$-list (x a)
  (declare (xargs :guard t
                  :measure (ev$-list-measure x a)
                  :well-founded-relation l<))
  (cond
   ((atom x) nil)
   (t (cons (EV$ (car x) a)
            (EV$-LIST (cdr x) a)))))
)

(defthm len-ev$-list ; useful for verifying guards for apply$
  (equal (len (ev$-list x a))
         (len x)))

#+acl2-devel
(verify-guards apply$)

(in-theory (disable ev$ ev$-list
                    badge
                    (:executable-counterpart badge)
                    apply$
                    (:executable-counterpart apply$)))

; -----------------------------------------------------------------
; 4. Executable Versions of BADGE and TAMEP

; -----------------------------------------------------------------
; 5. BADGER and the Badge-Table

; -----------------------------------------------------------------
; 6. Essay on CHECK-ILKS

; Note: We do all this work locally and do not export it.  Our only objective
; is to see check-ilks and know that Pass 2 of guess-ilks-alist implies it.

(local (include-book "tools/flag" :dir :system))

(local
 (encapsulate nil

; To define check-ilks in :logic mode and to reason about guess-ilks-alist, we
; have to verify the termination of some :program mode functions that otherwise
; don't have to be in :logic mode.

   (progn
     (defun count-to-nil (x)
       (if (atom x)
           (if (null x) 0 1)
           (+ 1
              (count-to-nil (car x))
              (count-to-nil (cdr x)))))

     (verify-termination EXECUTABLE-BADGE)

     (verify-termination
       (executable-tamep
        (declare (xargs :measure (acl2-count x))))
       (executable-tamep-functionp
        (declare (xargs :measure (acl2-count fn))))
       (executable-suitably-tamep-listp
        (declare (xargs :measure (acl2-count args)))))

     (verify-termination WEAK-WELL-FORMED-LAMBDA-OBJECTP)

     (verify-termination CHANGED-FUNCTIONAL-OR-EXPRESSIONAL-FORMALP)


     (verify-termination accumulate-ilk)

     (verify-termination
       (guess-ilks-alist (declare (xargs :measure (acl2-count term))))
       (guess-ilks-alist-list (declare (xargs :measure (acl2-count terms)))))

     )

   (defun find-badge-ilk (var formals ilks)
     (cond
      ((endp formals) nil)
      ((eq var (car formals)) (car ilks))
      (t (find-badge-ilk var (cdr formals) (cdr ilks)))))

   (mutual-recursion

    (defun check-ilks (fn new-formals new-badge term ilk wrld)

; Here we are checking conditions (b), (c), (d) and (e) of our assurances about
; non-erroneous results from badger.

; (b) Every function called in body has a badge (including fn if we consider
;     new-badge the badge of fn).

; (c) Every subterm of body with occurrence ilk :FN is:
;     a formal variable of fn with ilk :FN in new-badge, or
;     a quoted tame function symbol other than fn, or
;     a quoted, well-formed (fully translated and closed), tame lambda
;     expression that does not call fn.

; (d) Every subterm of body with occurrence ilk :EXPR is:
;     a formal variable of fn with ilk :EXPR in new-badge, or
;     a quoted, well-formed (fully translated), tame term that does not call
;     fn.

; (e) If the nth formal, vn, of fn has ilk :FN or :EXPR then vn is passed
;     unchanged into the nth slot of every recursive call of fn.

; Since we rely on our assurances to build the model, and since the assurances
; are phrased as above but checked as below, and since our proof actually
; establishes that the code below returns T when badger succeeds, it behooves
; the reader to inspect this definition and confirm that it implies (b)-(e)!

      (declare (xargs :measure (acl2-count term)))
      (cond
       ((variablep term)
        (eq (find-badge-ilk term new-formals
                            (access apply$-badge new-badge :ilks))
            ilk))
       ((fquotep term)
        (cond
         ((eq ilk :FN)
          (or (and (symbolp (cadr term))
                   (or (not (equal fn (cadr term)))
                       (executable-badge fn wrld))
                   (executable-tamep-functionp (cadr term) wrld))
              (and (consp (cadr term))
                   (and (weak-well-formed-lambda-objectp (cadr term) wrld)
                        (or (not (ffnnamep fn (lambda-object-body (cadr term))))
                            (executable-badge fn wrld))
                        (executable-tamep-lambdap (cadr term) wrld)))))
         ((eq ilk :EXPR)
          (and (termp (cadr term) wrld)
               (not (ffnnamep fn (cadr term)))
               (executable-tamep (cadr term) wrld)))
         (t t)))
       ((flambdap (ffn-symb term)) nil)
       ((or (eq ilk :FN)
            (eq ilk :EXPR))
        nil)
       ((eq fn (ffn-symb term))
        (and
         (check-ilks-list fn new-formals new-badge
                          (fargs term)
                          (access apply$-badge new-badge :ilks)
                          wrld)
         (or (eq (access apply$-badge new-badge :ilks) t)
             (not (changed-functional-or-expressional-formalp
                   (formals fn wrld)
                   (access apply$-badge new-badge :ilks)
                   (fargs term))))))
       (t (let ((bdg (executable-badge (ffn-symb term) wrld)))
            (and bdg
                 (check-ilks-list fn new-formals new-badge
                                  (fargs term)
                                  (access apply$-badge bdg :ilks)
                                  wrld))))))

    (defun check-ilks-list (fn new-formals new-badge terms ilks wrld)
      (declare (xargs :measure (acl2-count terms)))
      (cond
       ((endp terms) t)
       (t (and
           (check-ilks fn new-formals new-badge
                       (car terms)
                       (cond ((eq ilks T) nil)
                             (t (car ilks)))
                       wrld)
           (check-ilks-list fn new-formals new-badge
                            (cdr terms)
                            (cond ((eq ilks T) T)
                                  (t (cdr ilks)))
                            wrld)))))
    )

   (in-theory (disable executable-badge
                       executable-tamep
                       executable-tamep-functionp
                       weak-well-formed-lambda-objectp
                       changed-functional-or-expressional-formalp))

   (make-flag checker guess-ilks-alist)

   (mutual-recursion
    (defun alist-okp (term formals badge alist wrld)
      (cond
       ((variablep term)
        (and (member term formals)
             (assoc term alist)
             (member (cdr (assoc term alist)) '(nil :fn :expr))
             (equal
              (find-badge-ilk term formals (access apply$-badge badge :ilks))
              (cdr (assoc term alist)))))
       ((fquotep term) t)
       (t (and (symbolp (car term))
               (true-listp (fgetprop (car term) 'formals t wrld))
               (alist-okp-list (fargs term) formals badge alist wrld)))))
    (defun alist-okp-list (terms formals badge alist wrld)
      (cond
       ((endp terms) t)
       (t (and (alist-okp (car terms) formals badge alist wrld)
               (alist-okp-list (cdr terms) formals badge alist wrld))))))

   (defthm-checker
     (defthm guess-ilks-alist-lemma
       (implies (and (alist-okp term formals new-badge alist wrld)
                     (null (mv-nth 0 (guess-ilks-alist fn new-badge term
                                                       ilk wrld alist)))
                     new-badge)
                (equal (mv-nth 1 (guess-ilks-alist fn new-badge term
                                                   ilk wrld alist))
                       alist))
       :flag guess-ilks-alist)
     (defthm guess-ilks-alist-list-lemma
       (implies (and (alist-okp-list terms formals new-badge alist wrld)
                     (null
                      (mv-nth 0 (guess-ilks-alist-list fn new-badge terms
                                                       ilks wrld alist)))
                     new-badge)
                (equal
                 (mv-nth 1 (guess-ilks-alist-list fn new-badge terms
                                                  ilks wrld alist))
                 alist))
       :flag guess-ilks-alist-list)
     :hints (("Goal" :in-theory (enable accumulate-ilk))))

; Two similar concepts are needed: Badge-alistp is used to check the
; *badge-prim-falist* and badge-userfn-structure-okp is used to check the
; :badge-userfn-structure of the badge-table.

   (defun badge-alistp (alist)
     (cond
      ((atom alist) (eq alist nil))
      (t (and (consp (car alist))
              (symbolp (caar alist))
              (apply$-badgep (cdar alist))
              (badge-alistp (cdr alist))))))

   (defun badge-userfn-structure-okp (alist)

; Every element is supposed to be a weak-badge-userfn-structure-tuplep.  We
; access the fn component with car because the assoc does that.  We access the
; warrantp and badge components with the specially-defined macros so we don't
; care where they really are below as long as the system source code is
; sensible.

     (cond
      ((atom alist) (eq alist nil))
      (t (and (weak-badge-userfn-structure-tuplep (car alist))
              (symbolp (car (car alist)))
              (booleanp
               (access-badge-userfn-structure-tuple-warrantp (car alist)))
              (apply$-badgep
               (access-badge-userfn-structure-tuple-badge (car alist)))
              (badge-userfn-structure-okp (cdr alist))))))

   (defthm apply$-badgep-hons-get-lemma
     (implies (and (badge-alistp alist)
                   (hons-get fn alist))
              (apply$-badgep (cdr (hons-get fn alist))))
     :hints (("Goal" :in-theory (enable hons-assoc-equal))))

   (defthm apply$-badgep-executable-badge-lemma
     (implies (and (badge-userfn-structure-okp alist)
                   (assoc fn alist))
              (apply$-badgep
               (access-badge-userfn-structure-tuple-badge
                (assoc-equal fn alist)))))

   (defthm apply$-badgep-executable-badge
     (implies (and (badge-alistp
                    (unquote
                     (getpropc '*badge-prim-falist* 'const nil wrld)))
                   (badge-userfn-structure-okp
                    (cdr (assoc-equal :badge-userfn-structure
                                      (table-alist 'badge-table wrld))))
                   (executable-badge fn wrld))
              (apply$-badgep (executable-badge fn wrld)))
     :hints (("Goal" :in-theory (e/d (executable-badge)
                                     (hons-get
                                      apply$-badgep))))
     :rule-classes nil)

   (defthm-checker

     (defthm guess-ilks-alist-correct
       (implies (and (null
                      (mv-nth 0 (guess-ilks-alist fn new-badge term
                                                  ilk wrld alist)))
                     (alist-okp term formals new-badge alist wrld)
                     (badge-alistp
                      (unquote
                       (getpropc '*badge-prim-falist* 'const nil wrld)))
                     (badge-userfn-structure-okp
                      (cdr (assoc-equal :badge-userfn-structure
                                        (table-alist 'badge-table wrld))))
                     (apply$-badgep new-badge)
                     (member ilk '(nil :fn :expr))
                     (termp term wrld))
                (check-ilks fn formals new-badge term ilk wrld))
       :flag guess-ilks-alist)

     (defthm guess-ilks-alist-list-correct
       (implies (and (null
                      (mv-nth 0 (guess-ilks-alist-list fn new-badge terms
                                                       ilks wrld alist)))
                     (alist-okp-list terms formals new-badge alist wrld)
                     (badge-alistp
                      (unquote
                       (getpropc '*badge-prim-falist* 'const nil wrld)))
                     (badge-userfn-structure-okp
                      (cdr (assoc-equal :badge-userfn-structure
                                        (table-alist 'badge-table wrld))))
                     (apply$-badgep new-badge)
                     (or (eq ilks t)
                         (and (true-listp ilks)
                              (subsetp ilks '(nil :fn :expr))))
                     (term-listp terms wrld))
                (check-ilks-list fn formals new-badge terms ilks wrld))
       :flag guess-ilks-alist-list)
     :hints (("Subgoal *1/28" :use ((:instance apply$-badgep-executable-badge
                                               (fn (car term)))))))
   ))

; -----------------------------------------------------------------
; 7. Functional Equivalence

; We now develop the notion of two functions being equivalent.  The basic idea
; is that fn1 is functionally equivalent to fn2 if they are both tame and
; apply$ cannot distinguish them.  We define fn-equal to be this concept, but
; first need the quantified statement that apply$ cannot distinguish the two.

(defun-sk apply$-equivalence (fn1 fn2)
  (declare (xargs :guard t))
  (forall (args)
    (equal (ec-call (apply$ fn1 args))
           (ec-call (apply$ fn2 args)))))

(defun fn-equal (fn1 fn2)
  (declare (xargs :guard t))
  (if (equal fn1 fn2)
      t
      (and (tamep-functionp fn1)
           (tamep-functionp fn2)
           (apply$-equivalence fn1 fn2))))

(local
 (defthm apply$-equivalence-necc-rewriter
   (implies (equal (apply$ fn1 (apply$-equivalence-witness fn1 fn2))
                   (apply$ fn2 (apply$-equivalence-witness fn1 fn2)))
            (equal (apply$ fn1 args)
                   (apply$ fn2 args)))
   :hints (("Goal" :in-theory (disable APPLY$-EQUIVALENCE-NECC)
            :use APPLY$-EQUIVALENCE-NECC))))

(defequiv fn-equal :package :legacy)

(defcong fn-equal equal (apply$ fn args) 1 :package :legacy)

(in-theory (disable fn-equal))

; Every time a mapping function is introduced we also prove the fn-equal
; congruence rule.  Here is how we generate it.  For example,

; (generate-fn-equal-congruences '(collect lst fn) 1 '(nil :fn))

; produces the list containing just

; (defcong fn-equal equal (collect lst fn) 2)

(defun defcong-fn-equal-equal-events (term i c1-cn)
  (declare (xargs :guard (and (natp i)
                              (true-listp c1-cn))))
  (cond
   ((endp c1-cn) nil)
   ((eq (car c1-cn) :FN)
    (cons `(defcong fn-equal equal ,term ,i
             :package :legacy
             :hints
             (("Goal" :in-theory (disable (:executable-counterpart force)))))
          (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn))))
   (t (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn)))))

; -----------------------------------------------------------------
; 8. DEFWARRANT

; -----------------------------------------------------------------
; 9. DEFUN$

; -----------------------------------------------------------------
; 10. The LAMB Hack
;     Deprecated as noted above.

; -----------------------------------------------------------------
; 11. The Defattach

; -----------------------------------------------------------------
; 12. Loop$ Scions

; See loop.lisp.
