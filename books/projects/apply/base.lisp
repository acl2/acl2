; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

(in-package "ACL2")

; We will locally (but see below) include system/apply/apply and then
; explicitly identify some basic lemmas from it that we believe are generally
; useful to user-level proofs involving apply$.  A lot of these lemmas are
; redundant during the certification of this book but will be available to the
; user of this book.  Recall that system/apply/apply is used during the build
; of ACL2 itself, to support the sources' claims that the functions terminate
; and are guard verified.  Many of the redundant lemmas mentioned below are
; critical to those proofs -- so they have to be in system/apply/apply -- but
; are tedious to prove so we don't want to prove them again from scratch here.

; Our include-book below is non-local for a #+acl2-devel build, so that
; functions can be in logic mode as necessary (e.g., suitably-tamep-listp).  We
; need this book for #+acl2-devel builds because it is included in
; books/system/apply/loop.lisp, which is certified during devel builds in order
; to put loop$ scions in guard-verified logic mode.

; (depends-on "build/first-order-like-terms-and-out-arities.certdep" :dir :system)

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

#-acl2-devel
(local (include-book "system/apply/apply" :dir :system))
#+acl2-devel
(include-book "system/apply/apply" :dir :system)

; Redundant with system/apply/apply
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
                                    (CAR (CDR x))))))))

; Redundant with system/apply/apply
(defthm badge-prim-type
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
                          (apply$-badgep (badge-prim fn))))))

(set-rewrite-stack-limit 4000) ; local to this book

; Redundant with system/apply/apply-prim
(defun meta-apply$-prim (term)
  (declare (xargs :guard (pseudo-termp term)
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

(verify-guards meta-apply$-prim)

; Redundant with system/apply/apply
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

    (with-output
      :off (prove event)
      (defthm apply$-prim-meta-fn-correct
        (equal (apply$-prim-meta-fn-ev term alist)
               (apply$-prim-meta-fn-ev (meta-apply$-prim term) alist))
        :hints (("Goal" :in-theory (disable (:executable-counterpart break$))))
        :rule-classes ((:meta :trigger-fns (apply$-prim)))))

    (defthm apply$-primp-implies-symbolp
      (implies (apply$-primp fn)
               (symbolp fn))
      :rule-classes :forward-chaining)

    ))

; Redundant with system/apply/apply
(defthm badge-type
  (or (null (badge fn))
      (apply$-badgep (badge fn)))
  :rule-classes
  ((:forward-chaining
    :corollary (implies (badge fn)
                        (apply$-badgep (badge fn))))))

; The following lemmas are not redundant with system/apply/apply but are
; useful:

(defun suitably-tamep-listp-induction (n flags args)
  (cond
   ((zp n) (list flags args))
   (t (suitably-tamep-listp-induction (- n 1) (cdr flags) (cdr args)))))

(defthm suitably-tamep-listp-implicant-1
  (implies (and (suitably-tamep-listp n flags args)
                (natp n))
           (and (true-listp args)
                (equal (len args) n)))
  :hints (("Goal" :induct (suitably-tamep-listp-induction n flags args)))
  :rule-classes :forward-chaining)

(defthm tamep-implicant-1
  (implies (and (tamep x)
                (consp x))
           (true-listp x))
  :hints (("Goal" :expand (tamep x)
           :use ((:instance badge-type (fn (car x))))))
  :rule-classes :forward-chaining)

(defthm apply$-lambda-opener
  (equal (apply$-lambda fn args)
         (ev$ (lambda-object-body fn)
              (pairlis$ (lambda-object-formals fn)
                        args))))

; Redundant with system/apply/apply
(defequiv fn-equal)

; Redundant with system/apply/apply
(defcong fn-equal equal (apply$ fn args) 1)

; Having recovered the basic lemmas we need to reason about apply$ at the most
; fundamental level, we develop more interesting lemmas for the user's sake.

; We will rationalize our enabled theory for the user at the end of this book,
; so these intermediate in-theories are just kind of ad hoc.

(in-theory (enable ev$ ev$-list
                   badge
                   (:executable-counterpart badge)
                   apply$
                   (:executable-counterpart apply$)))

; TODO: We have found that ev$-def-fact below, if stored as a :definition, gets
; in the way of some proofs in applications books (exactly which books has been
; lost in in the mists of time...).  But, oddly, we have been unsuccessful at
; disabling that :definition rule.  (We haven't pursued this possible bug yet.)
; And in earlier versions of books/projects/apply/report.lisp we needed to
; force ev$ open more often than the :definition rule opened it automatically.
; So we prove an opener below.  But we need the :definition rule to do it!  And
; since we can't apparently disable the :definition rule, we prove it locally.
; And since we like to advertise the fact that ev$ has a rather beautiful
; definition for tamep terms, we prove ev$-def-fact as :rule-classes nil.

; Hints at resolving the above mystery: By proving ev$-def after including this
; book and then doing :pr ev$-def we see that
; Clique:       (EV$)
; Controller-alist: ((EV$ T NIL))
; so we speculate the problem mentioned above might have to do with the
; induction heuristic being applied to a disabled rule.  But we haven't
; investigated this possibility yet.

(encapsulate
 nil
 (defthm ev$-def-fact
   (implies (tamep x)
            (equal (ev$ x a)
                   (cond
                    ((variablep x)
                     (cdr (assoc x a)))
                    ((fquotep x)
                     (cadr x))
                    ((eq (car x) 'if)
                     (if (ev$ (cadr x) a)
                         (ev$ (caddr x) a)
                         (ev$ (cadddr x) a)))
                    (t (apply$ (car x) (ev$-list (cdr x) a))))))
   :hints (("Goal" :expand ((EV$ X A))))
   :rule-classes nil)

 (local
  (defthm ev$-def
    (implies (tamep x)
             (equal (ev$ x a)
                    (cond
                     ((variablep x)
                      (cdr (assoc x a)))
                     ((fquotep x)
                      (cadr x))
                     ((eq (car x) 'if)
                      (if (ev$ (cadr x) a)
                          (ev$ (caddr x) a)
                          (ev$ (cadddr x) a)))
                     (t (apply$ (car x) (ev$-list (cdr x) a))))))
    :hints (("Goal" :use ev$-def-fact))
    :rule-classes (:definition)))

 (defthm ev$-opener
   (and (implies (symbolp x)
                 (equal (ev$ x a) (cdr (assoc x a))))
        (equal (ev$ (list 'quote obj) a)
               obj)
        (implies (suitably-tamep-listp 3 nil args) ; See note on forcing below.
                 (equal (ev$ (cons 'if args) a)
                        (if (ev$ (car args) a)
                            (ev$ (cadr args) a)
                          (ev$ (caddr args) a))))
        (implies (and (not (eq fn 'quote))
                      (not (eq fn 'if))
                      (tamep (cons fn args))) ; See note on forcing below.
                 (equal (ev$ (cons fn args) a)
                        (apply$ fn (ev$-list args a)))))
   :hints (("Subgoal 1" :expand (ev$ (cons fn args) a)))))

; Note: At one time we FORCEd the two tameness requirements ab ove.  We found
; that unsatisfactory because proofs sometimes failed for hard-to-debug reasons
; if the relevant apply$-fn lemma proved by (defwarrant fn) was disabled.
; E.g., if square is a warranted function and apply$-square is disabled, then
; the following theorem is provable without knowledge of square, but the user
; who tries to avoid knowledge of square by disabling apply$-square will be
; sorely disappointed.

; (thm (implies (and ;; (warrant square)
;                (natp k1) (natp k2) (natp k3)
;                (<= k1 k2) (<= k2 k3))
;               (equal (f2 k1 k3)
;                      (append (f2 k1 k2)
;                              (f2 (1+ k2) k3))))
;      :hints (("Goal" :in-theory (disable apply$-square))))

; The reason this fails is that ev$-opener continues to fire, forcing tameness
; requirements that are obscure to most users.

; Removing the forcing doesn't negatively affect any proof as of the pre-
; release of Version 8.2.  But we have very little experience with user
; engagement with apply$, much less with direct use of ev$.  So this decision
; to remove the forcing may be only a superficial solution.  Another solution
; would be to document ev$ and its opener in gory detail!

(defthm ev$-list-def
  (equal (ev$-list x a)
         (cond
          ((endp x) nil)
          (t (cons (ev$ (car x) a)
                   (ev$-list (cdr x) a)))))
  :rule-classes
  ((:definition)))

(in-theory (disable ev$ ev$-list))

; We will continue to rely on the defun of apply$ for a while but will
; eventually prove theorems that handle all apply$s that can be handled.

(defthm beta-reduction
  (and (equal (apply$ (list 'LAMBDA vars body) args)
              (ev$ body (pairlis$ vars args)))
       (equal (apply$ (list 'LAMBDA vars dcl body) args)
              (ev$ body (pairlis$ vars args)))))

(defthm apply$-primp-badge
  (implies (apply$-primp fn)
           (equal (badge fn)
                  (badge-prim fn)))
  :hints (("Goal" :in-theory (enable badge))))

(defthm badge-BADGE
  (equal (badge 'BADGE) *generic-tame-badge-1*))

(defthm badge-TAMEP
  (equal (badge 'TAMEP) *generic-tame-badge-1*))

(defthm badge-TAMEP-FUNCTIONP
  (equal (badge 'TAMEP-FUNCTIONP) *generic-tame-badge-1*))

(defthm badge-SUITABLY-TAMEP-LISTP
  (equal (badge 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*))

(defthm badge-APPLY$
  (equal (badge 'APPLY$) *apply$-badge*))

(defthm badge-EV$
  (equal (badge 'EV$) *ev$-badge*))

(defthm apply$-primitive
  (implies (apply$-primp fn)
           (equal (apply$ fn args)
                  (apply$-prim fn args))))

(defthm apply$-BADGE
  (equal (apply$ 'BADGE args)
         (badge (car args))))

(defthm apply$-TAMEP
  (equal (apply$ 'TAMEP args)
         (tamep (car args))))

(defthm apply$-TAMEP-FUNCTIONP
  (equal (apply$ 'TAMEP-FUNCTIONP args)
         (tamep-functionp (car args))))

(defthm apply$-SUITABLY-TAMEP-LISTP
  (equal (apply$ 'SUITABLY-TAMEP-LISTP args)
         (suitably-tamep-listp (car args) (cadr args) (caddr args))))

(defthm apply$-APPLY$
  (implies (tamep-functionp (car args))
           (equal (apply$ 'APPLY$ args)
                  (apply$ (car args) (cadr args))))
  :hints (("Goal" :in-theory (enable apply$))))

(defthm apply$-EV$
  (implies (tamep (car args))
           (equal (apply$ 'EV$ args)
                  (ev$ (car args) (cadr args))))
  :hints (("Goal" :in-theory (enable apply$))))

; We will arrange for (TAKE n args) to expand as though it were defined without
; an accumulator.  We will also arrange for it to expand completely when n is a
; constant.  This seems very reasonable!  But if you use this book and don't
; want TAKE treated this way:

; (in-theory (e/d (take) (alternative-take take-opener)))

(encapsulate
  nil
  (local
   (defun take1 (n args)
     (cond ((zp n) nil)
           (t (cons (car args) (take1 (- n 1) (cdr args)))))))

  (local
   (defthm take1-take-gen
     (equal (first-n-ac n lst ac)
            (revappend ac (take1 n lst)))))

  (defthm alternative-take
    (equal (take n lst)
           (if (zp n)
               nil
               (cons (car lst)
                     (take (- n 1) (cdr lst)))))
    :rule-classes :definition)

  (in-theory (disable take))

  (defthm take-opener
    (implies (syntaxp (quotep n))
             (equal (take n lst)
                    (if (zp n)
                        nil
                        (cons (car lst)
                              (take (- n 1) (cdr lst))))))
    :rule-classes :rewrite))

(defthm pairlis$-takes-arity-args
  (equal (pairlis$ x (take (len x) y))
         (pairlis$ x y)))

(defthm apply$-lambda-takes-arity-args
  (implies (consp fn)
           (equal (apply$-lambda fn args)
                  (apply$-lambda fn (take (len (cadr fn)) args))))
  :hints
  (("Goal" ; :in-theory (disable take)
    :expand ((apply$-lambda fn args)
             (apply$-lambda fn (take (len (cadr fn)) args)) )))
  :rule-classes nil)

(defthm apply$-lambda-arity-1
  (implies (and (consp fn)
                (equal (len (cadr fn)) 1))
           (equal (apply$-lambda fn (list (car args)))
                  (apply$-lambda fn args)))
  :hints (("Goal" :use apply$-lambda-takes-arity-args)))

(local
 (defthm hide-is-identity
   (equal (hide x) x)
   :hints (("Goal" :expand ((hide x))))))

(defthm apply$-prim-takes-arity-args
  (implies (apply$-primp fn)
           (equal (apply$-prim fn args)
                  (apply$-prim fn (take (apply$-badge-arity (badge-prim fn))
                                        args))))
  :hints (("Goal" :in-theory '(apply$-prim
                               apply$-primp
                               badge-prim
                               take-opener
                               (:executable-counterpart zp)
                               car-cons
                               cdr-cons
                               hons-get
                               (:executable-counterpart hons-assoc-equal)
                               hide-is-identity
                               )))
  :rule-classes nil)

(defthm apply$-prim-arity-1
  (implies (and (apply$-primp fn)
                (equal (apply$-badge-arity (badge-prim fn)) 1))
           (equal (apply$-prim fn (list (car args)))
                  (apply$-prim fn args)))
  :hints (("Goal" :use apply$-prim-takes-arity-args)))

(defthm apply$-userfn-arity-1
  (implies (and (badge-userfn fn)
                (equal (apply$-badge-arity (badge-userfn fn)) 1))
           (equal (apply$-userfn fn (list (car args)))
                  (apply$-userfn fn args)))
  :hints (("Goal" :use apply$-userfn-takes-arity-args)))

(defthm apply$-symbol-arity-1
  (implies (and (symbolp fn)
                (badge fn)
                (equal (apply$-badge-arity (badge fn)) 1))
           (equal (apply$ fn (list (car args)))
                  (apply$ fn args)))
  :hints (("Goal" :in-theory (enable apply$ badge))))

; Two classic rules about len that we think are always reasonable!

(defthm equal-len-0
  (equal (equal (len x) 0)
         (not (consp x))))

(defthm equal-len-1
  (equal (equal (len x) 1)
         (and (consp x)
              (not (consp (cdr x))))))

(defthm apply$-consp-arity-1
  (implies (and (consp fn)
                (equal (len (lambda-object-formals fn)) 1))
           (equal (apply$ fn (list (car args)))
                  (apply$ fn args)))
  :hints (("Goal" :expand ((apply$ fn (list (car args)))))))

; Recall the discussion of the deprecated LAMB Hack in apply.lisp:

; Historical Note:  Once upon a time we had a final step:

;    10. The LAMB Hack
;        Define (LAMB vars body) to be `(LAMBDA ,vars ,body) to provide a
;        rewrite target for functional-equivalence lemmas.  Since ACL2 doesn't
;        rewrite constants, we won't even try to simplify a quoted lambda.  We
;        are not satisfied with the treatment of functional equivalence yet and
;        LAMB is sort of a reminder and placeholder for future work.

; However, we have removed that from the sources because we are not yet
; convinced it is a good way to address the problem of rewriting equivalent
; LAMBDAs.  We plan to experiment with solutions in the user-maintained books.
; As of Version_8.0, our best shot is in
; books/projects/apply/base.lisp (formerly apply-lemmas.lisp), but this may
; change.

(defun$ lamb (vars body)
  (list 'LAMBDA vars body))

(encapsulate
  nil
  (defthm consp-lamb
    (and (consp (lamb args body))
         (true-listp (lamb args body)))
    :rule-classes :type-prescription)
  (defthm consp-cdr-lamb
    (consp (cdr (lamb args body))))
  (defthm consp-cddr-lamb
    (consp (cddr (lamb args body))))
  (defthm cdddr-lamb
    (equal (cdddr (lamb args body)) nil))
  (defthm car-lamb
    (equal (car (lamb args body)) 'LAMBDA))

  (defthm lambda-formals-lamb
    (equal (lambda-formals (lamb args body)) args))

  (defthm lambda-body-lamb
    (equal (lambda-body (lamb args body)) body))

;;; We need to re-enable apply$ for this proof.
  (defthm lamb-reduction
    (equal (apply$ (lamb vars body) args)
           (ev$ body (pairlis$ vars args)))
    :hints (("Goal" :in-theory (enable apply$)))))

(in-theory (disable lamb (:executable-counterpart lamb)))

(defthm lamb-v-v-is-identity
  (implies (symbolp v)
           (fn-equal (lamb (list v) v) 'IDENTITY))
  :hints (("goal" :in-theory (enable fn-equal))))

(defthm lambda-v-fn-v-is-fn
  (implies (and (symbolp v)
                (equal (apply$-badge-arity (badge fn)) 1)
                (not (eq fn 'quote))
                (tamep (list fn v)))
           (fn-equal (lamb (list v) (list fn v))
                     fn))
  :hints
  (("Goal"
    :in-theory (e/d (fn-equal badge)
                    (badge-type apply$-badgep-properties))
    :use ((:instance badge-type (fn fn)))
    :expand
    ((tamep (list fn v))
     (ev$
      (list fn v)
      (list
       (cons
        v
        (car (apply$-equivalence-witness (lamb (list v) (list fn v))
                                         fn)))))))))

(defun$ ok-fnp (fn)
  (and (not (eq fn 'quote))
       (tamep `(,fn X))))

; We also propose an approach to (certain, trivial) functional composition
; needs.

; But like the LAMB hack, we see this as a placeholder for more work.

; (compose f g) is f o g = (lambda (v) (f (g v))), for tame functions of arity
; 1.

; Wikipedia notes that the meaning of the ``(f o g)'' notation varies among
; authors.  To some, (f o g) applied to v is (f (g v)) while to others it is (g
; (f v)).  Our convention is that g is the inner function, i.e., applied first,
; and f is the outer one, in keeping with the syntactic order of f and g in the
; notation.

; We considered allowing g to be of arbitrary arity: since g must be tame, it
; has a badge and we could obtain its arity n from that and then create (lambda
; (v1 ... vn) (f (g v1 ... vn))).  But g must return 1 result so f must be of
; arity 1 since we don't have currying.  It just seems simpler to assume that
; both are arity 1.  The remaining questions are: (a) Should we name this
; function ``compose-arity-1-fns'' or something suggestive of the restriction?
; (b) Should we impose a guard requiring g to be of arity 1?  In the spirit of
; ``this is a placeholder'' we just ignore those questions for now!

(defun$ compose (f g)
  (lamb '(v) `(,f (,g v))))

(defthm ok-fnp-compose
  (implies (and (ok-fnp f)
                (ok-fnp g))
           (ok-fnp (compose f g)))
  :hints (("Goal" :in-theory (e/d (lamb) (badge))
           :expand ((tamep (cons g '(x)))
                    (tamep (cons g '(v)))
                    (tamep (list f (cons g '(v))))))))

(defthm apply$-composition
  (implies (and (ok-fnp f)
                (ok-fnp g))
           (equal (apply$ (compose f g) (list a))
                  (apply$ f (list (apply$ g (list a))))))
  :hints (("Goal" :in-theory (e/d (lamb)(badge))
           :expand ((ev$ (list f (cons g '(v)))
                         (list (cons 'v a)))
                    (ev$ (cons g '(v)) (list (cons 'v a)))
                    (tamep (cons g '(x)))
                    (tamep (cons f '(x)))
                    (tamep (list f (cons g '(v))))))))

(in-theory (disable compose))

(in-theory
 (disable
  (:DEFINITION FN-EQUAL)
  (:DEFINITION EV$-LIST)
  (:DEFINITION EV$)
  (:DEFINITION APPLY$)
  (:DEFINITION BADGE)
  (:DEFINITION APPLY$-PRIM)
  (:DEFINITION BADGE-PRIM)
  (:DEFINITION APPLY$-PRIMP)

; Proofs seem to proceed more easily with these enabled.  We have our doubts
; though, because they introduce a lot of cases.  Perhaps we're missing some
; effective lemmas?  In any case, for the moment we'll leave them enabled!

; (:DEFINITION LAMBDA-OBJECT-FORMALS)
; (:DEFINITION LAMBDA-OBJECT-DCL)
; (:DEFINITION LAMBDA-OBJECT-BODY)
; (:DEFINITION LAMBDA-OBJECT-SHAPEP)

  (:EXECUTABLE-COUNTERPART APPLY$-EQUIVALENCE)
  (:EXECUTABLE-COUNTERPART APPLY$)
  (:EXECUTABLE-COUNTERPART SUITABLY-TAMEP-LISTP)
  (:EXECUTABLE-COUNTERPART TAMEP-FUNCTIONP)
  (:EXECUTABLE-COUNTERPART TAMEP)
  (:EXECUTABLE-COUNTERPART BADGE)))
