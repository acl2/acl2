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

; Refresher on books/system/, etc.

; The books on books/system/ are critical to the construction of the released
; version of ACL2 because they address certain bootstrapping problems.  See the
; comment in ACL2 sources constant *system-verify-guards-alist* or see :DOC
; verify-guards-for-system-functions.  But, roughly put, during bootstrapping
; some functions cannot be admitted in logic mode or cannot have their guards
; verified because the requisite logical machinery (e.g., lexicographic
; relations) does not exist yet.  Such functions are therefore admitted
; initially in :PROGRAM mode and then magically upgraded to guard-verified
; :LOGIC mode at the very end of the bootstrapping process.  The books on
; books/system/ address the question ``Is the magic right?''

; The books address that question by introducing the definitions of the
; relevant functions, identical to the definitions in the source code but in
; :logic mode and with appropriate :measures and :guards, and availing
; themselves of all the normal events of ACL2 (including the inclusion of of
; distributed books) to verify termination and guards.  The build process we
; follow before an ACL2 release stipulates that we build an intermediate ACL2
; image with the :acl2-devel feature on (where the problematic functions are
; left in :program mode) and then use that image to certify the books/system/
; books and the cone of books supporting it.  The process also confirms that
; the data stored in *system-verify-guards-alist* is correct wrt to the
; certified books/system/ books, thus insuring that the assumption of those
; facts by the normal build is probably ok.  We say probably here because there
; is, perhaps, still room for circularity but we are just using ``best
; practice'' to assure ourselves that our claims are true.

; Turning to the books/system/apply/ books specifically, they are concerned
; with apply$ and its supporters.  See the Essay on the APPLY$ Integration for
; some background.

; One way to think of each of these books is that it was derived by taking its
; source file counterpart, e.g., apply-prim.lisp in the case of this book,
; books/system/apply/apply-prim, and sprinkling in the include-books, defthms,
; declarations, and hints to get the source file admitted in guard-verified,
; :logic mode fashion by a version of ACL2 in which these functions weren't
; already defined.  But, historically, it happened the other way: apply$ wasn't
; in ACL2 Version_7.4, it was introduced in a collection of certified books,
; and then we stripped out of those books everything but the definitions, which
; we moved into the ACL2 sources for Version_8.0.  These books are therefore
; more aptly described as the ``original'' books admitting apply$, et al.

; We supply minimal comments here except when discussing the termination/guard
; verification issues.  See the corresponding source files for explanations of
; the definitions below!

; Historical Note: Prior to integration of apply$ into the sources, each of
; these books introducing the logical definitions supporting apply$ carried a
; warning not to edit the file except the version found on
; books/projects/apply-model.  That warning was appropriate because we wanted
; the distributed apply books in the Community Books to exactly match the
; foundational books showing that models can be built.  But now apply$ is in
; the sources, we regard the foundational work as static (supporting the paper
; and justifying the basic approach to apply$), and we are free (under the
; usual soundness caveats) to improve apply$ going forward, we no longer insist
; that these files exactly match the foundational work on apply$.

(in-package "ACL2")

(include-book "apply-prim-support")

; Sol Swords supplied an optimization for the proof of
; APPLY$-PRIM-META-FN-CORRECT that relies on the following local include-book.
; For more on that see "explanation from Sol" below.
(local (include-book "centaur/misc/evaluator-metatheorems" :dir :system))

; We locally re-enable runes that were disabled during the build.
(local (in-theory (enable apply$-primp badge-prim)))

; We now prove that badge-prim returns either nil or a badge of the form
; (APPLY$-BADGE arity out-arity . T).  This would be trivial except for the
; fact that there are so many cases (because the alist is so long).  So we
; resort to a standard trick for proving something about a big constant: define
; a function, named check-it! below, to check the property computationally,
; prove that the property holds of x if (check-it x) is t, then derive the main
; theorem by instantiating that lemma with {x <-- '<big-constant>}.

(encapsulate
  nil
  (local
   (defthm apply$-badgep-properties ; only selected properties!
     (implies (apply$-badgep x)
              (and (consp x)
                   (natp (access apply$-badge x :arity))
                   (natp (access apply$-badge x :out-arity))
                   (or (eq (access apply$-badge x :ilks) t)
                       (and (true-listp (access apply$-badge x :ilks))
                            (equal (len (access apply$-badge x :ilks))
                                   (access apply$-badge x :arity))))))

; Note: Unfortunately, record accessors translate into lambda applications.
; :Rewrite rules handle this appropriately by beta reducing the lambda
; applications in the conclusion.  But :linear rules do not.  So we've written
; all the rules in terms of car/cdr nests rather than access terms.

     :rule-classes
     ((:compound-recognizer
       :corollary (implies (apply$-badgep x)
                           (consp x)))
      (:linear
       :corollary (implies (apply$-badgep x)
                           (<= 0 (CAR (CDR x)))))
      (:rewrite
       :corollary (implies (apply$-badgep x)
                           (integerp (CAR (CDR x)))))
      (:linear
       :corollary (implies (apply$-badgep x)
                           (<= 0 (CAR (CDR (CDR x))))))
      (:rewrite
       :corollary (implies (apply$-badgep x)
                           (integerp (CAR (CDR (CDR x))))))
      (:rewrite
       :corollary (implies (and (apply$-badgep x)
                                (not (eq (CDR (CDR (CDR x))) t)))
                           (and (true-listp (CDR (CDR (CDR x))))
                                (equal (len (CDR (CDR (CDR x))))
                                       (CAR (CDR x)))))))))

  (local
   (defun check-it! (alist)
     (cond ((atom alist) t)
           (t (and (consp (car alist))
                   (apply$-badgep (cdr (car alist)))
                   (eq (access apply$-badge (cdr (car alist)) :ilks) t)
                   (check-it! (cdr alist)))))))
  (local
   (defthm check-it!-works
     (implies (check-it! alist)
              (implies (hons-get fn alist)
                       (and (consp (hons-get fn alist))
                            (apply$-badgep (cdr (hons-get fn alist)))
                            (eq (access apply$-badge (cdr (hons-get fn alist))
                                        :ilks)
                                t))))
     :rule-classes nil))

  (defthm badge-prim-type

; This lemma is needed in the proof of the lemma BADGE-TYPE in apply.lisp,
; despite the fact that it is not named in the BADGE-TYPE's Summary.  Tau is
; mentioned in Summary and BADGE-PRIM-TYPE generates a tau rule.

    (implies (apply$-primp fn)
             (and (apply$-badgep (badge-prim fn))
                  (eq (cdr (cdr (cdr (badge-prim fn)))) t)))
    :hints (("Goal" :use (:instance check-it!-works (alist *badge-prim-falist*))
             :in-theory (disable check-it! hons-get)))
    :rule-classes
    ((:rewrite
      :corollary (implies (apply$-primp fn)
                          (and (apply$-badgep (badge-prim fn))
                               (eq (cdr (cdr (cdr (badge-prim fn)))) t))))
     (:forward-chaining
      :corollary (implies (apply$-primp fn)
                          (apply$-badgep (badge-prim fn)))))))

(defun n-car-cadr-caddr-etc (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
      (cons `(CAR ,x)
            (n-car-cadr-caddr-etc (- n 1) `(CDR ,x)))))

; The following is commented out, because otherwise we get an error due to an
; attempt to redundantly define a function with raw Lisp code.
; (defun apply$-prim (fn args)
;   (declare (xargs :guard (true-listp args)))
;   (make-apply$-prim-body))

; To prove termination and guards of apply$, for example, we will need to
; manipulate terms involving apply$-prim.  Leaving that function enabled causes
; us to blow up because the defun of apply$-prim contains a case statement with
; ~800 cases.  Rewriting it causes stack overflow with the nominal rewrite
; stack size of 1000.  For example, we cannot prove: (thm (equal (apply$-prim
; 'tamep (list x)) (tamep x))).  We will therefore temporarily enlarge the
; stack and verify a metafunction which will enable MUCH faster reduction of
; (apply$-prim 'fn args), and then disable apply$-prim.  We also disable
; apply$-primp, leaving only the executable-counterpart enabled to resolve the
; question of whether a given quoted symbol is a primitive.

(set-rewrite-stack-limit 4000) ; local to this book

(defun meta-apply$-prim (term)
  (declare (xargs :guard (pseudo-termp term)

; There is no need to verify guards here.  For that, see
; books/projects/apply/base.lisp.

                  :verify-guards nil))
  (cond ((and (consp term)
              (eq (ffn-symb term) 'apply$-prim)
              (quotep (fargn term 1))
              (symbolp (cadr (fargn term 1))))
         (let* ((fn (cadr (fargn term 1)))
                (args (fargn term 2))
                (temp (hons-get fn *badge-prim-falist*)))
           (cond
            ((null temp)
             term)
            (t (if (int= (access apply$-badge (cdr temp) :out-arity) 1)
                   `(,fn ,@(n-car-cadr-caddr-etc
                            (access apply$-badge (cdr temp) :arity)
                            args))
                   `(mv-list ',(access apply$-badge (cdr temp) :out-arity)
                             (,fn ,@(n-car-cadr-caddr-etc
                                     (access apply$-badge (cdr temp) :arity)
                                     args))))))))
        (t term)))

; Occasionally the value of *first-order-like-terms-and-out-arities*, computed
; when ACL2 is built, is changed due to, e.g., the addition of a new built-in
; function.  The following form tells the build system that this book depends
; on that constant, and needs to be rebuilt if it is changed.
; (depends-on "build/first-order-like-terms-and-out-arities.certdep" :dir :system)
(make-event
 `(encapsulate
    nil

; We introduce the relevant evaluator; defevaluator works in a
; very restricted theory (*DEFEVALUATOR-FORM-BASE-THEORY*) and so
; we do not have to worry about disabling all the functions
; involved in the defun of apply$-prim.

    (with-output
      :off (prove event)
      (defevaluator apply$-prim-meta-fn-ev
        apply$-prim-meta-fn-ev-list
        ((apply$-prim fn args)
         ,@(strip-cars *first-order-like-terms-and-out-arities*))))

    (local
     (with-output
       :off (prove event)
       (def-evaluator-expander apply$-prim-meta-fn-ev)))

; To prove correctness we need to force car-cadr-caddr-etc
; to open.

    (local
     (defthm n-car-cadr-caddr-etc-opener
       (implies (natp n)
                (equal (n-car-cadr-caddr-etc (+ 1 n) args)
                       (cons (list 'car args)
                             (n-car-cadr-caddr-etc n (list 'CDR args)))))))

; Next is correctness of the apply$-prim simplifier.

; Some day we may fix the well-formedness-guarantee code so that at the time a
; meta function is applied, we only check the non-primitive functions in the
; supplied arities-alist.  That could be done by checking the list at the time
; we store the meta lemma and removing any function that is a primitive.  We
; know -- or can at least sanely assume -- that the arities of all the system
; primitives won't change.  Then the built-in constant to be checked at
; apply-time would be much reduced -- in fact, to NIL in the case of
; meta-apply$-prim.

; If the above fix is ever made, it would be good to add a well-formedness
; guarantee lemma.

; The original proof of the next lemma didn't involve the proof-builder, but
; has been observed to take considerably longer that way.

;   (with-output
;     :off (prove event)
;     (defthm apply$-prim-meta-fn-correct
;       (equal (apply$-prim-meta-fn-ev term alist)
;              (apply$-prim-meta-fn-ev (meta-apply$-prim term) alist))
;       :hints (("Goal" :in-theory (disable (:executable-counterpart break$))))
;       :rule-classes ((:meta :trigger-fns (apply$-prim)))))

    (local
     (defthm hide-is-identity
       (equal (hide x) x)
       :hints (("Goal" :expand ((hide x))))))

    (local
     (make-event
      `(defthm open-apply$-prim-of-quote
         (implies (syntaxp (quotep fn))
                  (equal (apply$-prim fn args)
                         ,(body 'apply$-prim nil (w state))))

; At one time we called body above with a second argument of t, which returns
; the normalized body.  But the proof for #+acl2-devel builds, using (:repeat
; :prove) further below, stopped working sometime before mid-October, 2021.  A
; workaround was to replace :prove there by (:orelse :prove (:prove :hints
; (("Goal" :in-theory (current-theory :here))))).  But Sol Swords suggested the
; use of nil above (to obtain the unnormalized body) together with the
; following :instructions to complete this proof quickly.  Here is a relevant
; explanation from Sol, referring to the :bash instruction further below.

#|
 After the bash instruction each goal is of the following form
 1. (CONSP TERM)
 2. (EQUAL (CAR TERM) 'APPLY$-PRIM)
 3. (CONSP (CADR TERM))
 4. (EQUAL (CAR (CADR TERM)) 'QUOTE)
 5. (EQUAL (CADR (CADR TERM)) 'ACL2-NUMBERP)

 The current subterm is:
 (EQUAL (APPLY$-PRIM-META-FN-EV TERM ALIST)
        (APPLY$-PRIM-META-FN-EV (CONS 'ACL2-NUMBERP
                                      (N-CAR-CADR-CADDR-ETC 1 (CADDR TERM)))
                                ALIST))

 The LHS is supposed to reduce to e.g. 
 (APPLY$-PRIM 'ACL2-NUMBERP
              (APPLY$-PRIM-META-FN-EV (CADDR TERM)
                                      ALIST))
 and then (using open-apply$-prim-of-quote)
 (ACL2-NUMBERP (CAR (APPLY$-PRIM-META-FN-EV (CADDR TERM)
                                            ALIST)))
 and the RHS is supposed to reduce to that same thing using
 APPLY$-PRIM-META-FN-EV-EXPANDER-CORRECT.

 However, the OPEN-APPLY$-PRIM-OF-QUOTE rule had several cases for
 which instead of expanding to a call of the given function, it
 expanded to a constant due to normalization. There are a bunch of
 these, e.g. insist, member-eq-exec$guard-check, hard-error, etc. I
 don't know why this wasn't a problem before.  It seems it's not a
 problem in non-devel acl2 because tau solves it.
|#

         :instructions (:promote
                        (:drop 1)
                        (:prove :hints (("goal" :by apply$-prim)))))))

    (defthm apply$-prim-meta-fn-correct
      (equal (apply$-prim-meta-fn-ev term alist)
             (apply$-prim-meta-fn-ev (meta-apply$-prim term)
                                     alist))
      :instructions
      ((quiet!
        (:bash ("Goal" :in-theory '((:definition hons-assoc-equal)
                                    (:definition hons-equal)
                                    (:definition hons-get)
                                    (:definition meta-apply$-prim)
                                    (:definition quotep)
                                    ;; (:definition apply$-prim)
                                    (:executable-counterpart car)
                                    (:executable-counterpart cdr)
                                    (:executable-counterpart consp)
                                    ;; (:meta apply$-prim-meta-fn-ev-expander-correct)
                                    )))
        (:in-theory (union-theories
                     '(; (:definition apply$-prim)
                       (:rewrite open-apply$-prim-of-quote)
                       (:definition n-car-cadr-caddr-etc)
                       ;; (:definition hons-equal)
                       ;; (:definition hons-get)
                       (:meta apply$-prim-meta-fn-ev-expander-correct)
                       (:REWRITE APPLY$-PRIM-META-FN-EV-CONSTRAINT-8)
                       n-car-cadr-caddr-etc-opener
                       (natp)
                       ;; apply$-prim-meta-fn-ev-constraint-1
                       apply$-prim-meta-fn-ev-constraint-2
                       quotep
                       car-cons cdr-cons hide-is-identity)
                     (union-theories *expandable-boot-strap-non-rec-fns*
                                     (intersection-theories
                                       (current-theory :here)
                                       (executable-counterpart-theory :here))))
                     )
        (:repeat :prove)))
      :rule-classes ((:meta :trigger-fns (apply$-prim))))

    (defthm apply$-primp-implies-symbolp
      (implies (apply$-primp fn)
               (symbolp fn))
      :rule-classes :forward-chaining)

    ))

(in-theory (disable apply$-prim apply$-primp))
