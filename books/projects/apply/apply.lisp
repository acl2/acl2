; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Apply for Tame Functions in ACL2

; This is a WORK IN PROGRESS!

; It is our intention EVENTUALLY to restrict make-applicable so that the
; following is true: any chronology certified with this book has the property
; that, at least theoretically, one could define a suitable apply$, certify the
; chronology, and then prove that the Applicablep hypothesis for every function
; admitted by make-applicable is in fact a theorem.

; Warning: This version of apply.lisp does not have that property!  It is
; possible to use this book in a certified book that may contain theorems that
; are valid because their Applicablep hypotheses are unsatisfiable!

; (ld "apply.lisp" :ld-pre-eval-print t)
; (certify-book "apply")

(in-package "ACL2")

; -----------------------------------------------------------------
; The Axioms about F-Classes and Apply$:  There aren't any!

(defstub f-classes-nonprim (fn) t)
(defstub apply$-nonprim (fn args) t)

; -----------------------------------------------------------------
; These two stubs are used as the ``default values'' of (apply$ fn args) and
; (ev$ x a) when the arguments are not suitably tame.

(defstub untame-apply$ (fn args) t)
(defstub untame-ev$ (x a) t)

; -----------------------------------------------------------------
; Handling the Primitives

(include-book "apply-prim")

; The Role of F-Classes-Table

; The f-classes-table associates function names with their f-classes.  It is
; not used directly by the logic.  It is used in the computation of the
; f-classes of newly introduced functions.  See classify-formals.

; Classify-formals can't use (f-classes fn) to find the classes of fn's formals
; because f-classes is not always defined (it calls the defstub
; f-classes-nonprim whose value is determined by the apply hyp, if any, for
; fn).  So we need an easy way to recover the f-classes that are known and that
; is what the table is.

; We could shorten the table by removing the primitives from it; that would
; mean that to determine the f-classes of fn we'd first test (apply$-primp fn)
; and, failing that test, then look in the table.  But that's the same amount
; of work as looking in the full table, which is conceptually simpler.

(table f-classes-table nil
       (append (pairlis-x2 (strip-cars *apply$-primitives*) t)
               '((tamep . t)
                 (tamep-functionp . t)
                 (suitably-tamep-listp . t)
                 (apply$ . (:fn nil))
                 (ev$ . (:expr nil))))
       :clear)

; The tamep clique could have been included in the apply$ primitives.  But
; doing so would have required declaring f-classes-nonprim and apply$-nonprim
; inside apply-prim.lisp so we could define f-classes and hence the tamep
; clique there.  But that obscures the development of apply unnecessarily and
; we decided that it's better to handle the functions here.

(defun f-classes (fn)
  (cond
   ((apply$-primp fn) t)
   ((eq fn 'F-CLASSES) t)
   ((eq fn 'TAMEP) t)
   ((eq fn 'TAMEP-FUNCTIONP) t)
   ((eq fn 'SUITABLY-TAMEP-LISTP) t)
   ((eq fn 'APPLY$) '(:fn nil))
   ((eq fn 'EV$) '(:expr nil))
   (t (f-classes-nonprim fn))))

; -----------------------------------------------------------------
; Tameness

(mutual-recursion
 (defun tamep (x)
   (cond ((atom x) t)
         ((fquotep x) t)
         ((consp (car x)) ; lambda expr, all vanilla!
          (and (tamep-functionp (car x))
               (suitably-tamep-listp (cdr x) t)))
         ((f-classes (car x))
          (suitably-tamep-listp (cdr x) (f-classes (car x))))
         (t nil)))

 (defun tamep-functionp (fn)
   (if (symbolp fn)
       (eq (f-classes fn) t)
       (and (consp fn)
            (eq (car fn) 'LAMBDA)
            (tamep (lambda-body fn)))))

 (defun suitably-tamep-listp (x flags)

; Note that when we have exhausted x we must have exhausted flags.  That is
; flags may be too short but may not be too long.  This is a delicate aspect of
; the axiom we want for defining ev$.

   (cond
    ((atom x) (atom flags)) 
    ((atom flags)
     (and (tamep (car x))
          (suitably-tamep-listp (cdr x) flags)))
    ((eq (car flags) :fn)
     (and (quotep (car x))
          (tamep-functionp (cadr (car x)))
          (suitably-tamep-listp (cdr x) (cdr flags))))
    ((eq (car flags) :expr)
     (and (quotep (car x))
          (tamep (cadr (car x)))
          (suitably-tamep-listp (cdr x) (cdr flags))))
    (t
     (and (tamep (car x))
          (suitably-tamep-listp (cdr x) (cdr flags))))))
 )

; We disable the executable counterparts of tamep because f-classes-nonprim is
; undefined, so running tamep on constants, such as (tamep '(CONS A B)) fails
; and introduces a HIDE.  However, expansion of the definitional axioms allow
; us to use the f-classes axioms.  In a real implementation we would try to
; make f-classes semi-executable under the hood by some kind of attachment that
; accesses the f-classes-table.

(in-theory (disable (:executable-counterpart tamep)
                    (:executable-counterpart tamep-functionp)
                    (:executable-counterpart suitably-tamep-listp)))

; -----------------------------------------------------------------
; Definition of APPLY$ and EV$

(defun ev$-measure (x a)
  (declare (ignore a))
  (acl2-count x))

(defun apply$-measure (fn args)
  (cond
   ((consp fn)
    (acl2-count fn))
   ((eq fn 'apply$)
    (+ 1 (acl2-count (car args))))
   ((eq fn 'ev$)
    (+ 1 (acl2-count (car args))))
   (t 0)))

(defun ev$-list-measure (x a)
  (declare (ignore a))
  (acl2-count x))

(mutual-recursion
 (defun APPLY$ (fn args)
   (declare (xargs :measure (apply$-measure fn args)
                   ))
   (cond
    ((consp fn)
     (EV$ (lambda-body fn)
          (pairlis$ (lambda-formals fn) args)))
    ((apply$-primp fn)
     (apply$-prim fn args))

; See note above about handling the tamep clique as a primitive versus handling
; it here.

    ((eq fn 'F-CLASSES)
     (f-classes (car args)))
    ((eq fn 'TAMEP)
     (tamep (car args)))
    ((eq fn 'TAMEP-FUNCTIONP)
     (tamep-functionp (car args)))
    ((eq fn 'SUITABLY-TAMEP-LISTP)
     (suitably-tamep-listp (car args) (cadr args)))
    ((eq fn 'APPLY$)
     (if (tamep-functionp (car args))
         (APPLY$ (car args) (cadr args))
         (untame-apply$ fn args)))
    ((eq fn 'EV$)
     (if (tamep (car args))
         (EV$ (car args) (cadr args))
         (untame-apply$ fn args)))
    (t (apply$-nonprim fn args))))

 (defun EV$ (x a)
   (declare (xargs :measure (ev$-measure x a)))
   (cond
    ((not (tamep x))
     (untame-ev$ x a))
    ((variablep x)
     (cdr (assoc x a)))
    ((fquotep x)
     (cadr x))
    ((eq (car x) 'if)
     (if (ev$ (cadr x) a)
         (ev$ (caddr x) a)
         (ev$ (cadddr x) a)))
    ((eq (car x) 'APPLY$)
     (if (consp (cdr x))
         (apply$ 'APPLY$
                 (list (cadr (cadr x)) (EV$ (caddr x) a)))
         (untame-ev$ x a)))
    ((eq (car x) 'EV$)
     (if (consp (cdr x))
         (apply$ 'EV$ (list (cadr (cadr x)) (EV$ (caddr x) a)))
         (untame-ev$ x a)))
    (t
     (APPLY$ (car x)
             (EV$-LIST (cdr x) a)))))

 (defun EV$-LIST (x a)
   (declare (xargs :measure (ev$-list-measure x a)))
   (cond
    ((endp x) nil)
    (t (cons (EV$ (car x) a)
             (EV$-LIST (cdr x) a)))))

)

; About the definition of EV$:

; Below we prove a simpler version of the defun of EV$, conditioned by the
; hypothesis that x is tamep.  So why do we define EV$ as we do above?  In the
; two clauses dealing with calls of APPLY$ and EV$ we apply$ the relevant
; function symbol rather than just calling it, e.g., we write (apply$ 'apply$
; ...)  instead of (apply$ ...).  We do it this way so that we can more easily
; prove that in all cases, ev$ handles function calls calling apply$ on the
; ev$-list of the arguments.  But note that we don't write it quite that way
; because we need to prove termination.  That is, instead of calling ev$-list
; we actually write an explicit list of the two arguments (list (cadr (cadr x))
; (EV$ (caddr x) a)).  Note in particular that we do not ev$ the first argument
; but just take its cadr!  This insures termination and is equivalent to (ev$
; (cadr x) a) PROVIDED the argument is tame!  Note also that we could have
; called (ev$-list (cdr x) a) had we known (cdr x) was suitably tame but that
; would require admitting this clique as a reflexive function: the fact that
; (ev$ (cadr x) a) is smaller than (cadr x) when (cadr x) is tame requires
; reasoning about ev$ before it is admitted.

; TODO: We have found that ev$-def-fact, if stored as a :definition, gets in
; the way of some proofs in applications books, like model.lisp.  But, oddly,
; we have been unsuccessful at disabling that :definition rule.  (I haven't
; pursued this possible bug yet.)  And in foldr-exercises.lisp we need to force
; ev$ open more often than the :definition rule does.  So we prove an opener
; below.  But we need the :definition rule to do it!  And since we can't
; apparently disable the :definition rule, we prove it locally.  And since we
; like to advertise the fact that ev$ has a rather beautiful definition for
; tamep terms, we prove ev$-def-fact as :rule-classes nil.

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
   (and (implies (variablep x)
                 (equal (ev$ x a) (cdr (assoc x a))))
        (equal (ev$ (cons 'quote args) a)
               (car args))
        (implies (force (suitably-tamep-listp args t))
                 (equal (ev$ (cons 'if args) a)
                        (if (ev$ (car args) a)
                            (ev$ (cadr args) a)
                            (ev$ (caddr args) a))))
        (implies (and (not (eq fn 'quote))
                      (not (eq fn 'if))
                      (force (tamep (cons fn args))))
                 (equal (ev$ (cons fn args) a)
                        (apply$ fn (ev$-list args a)))))
   :hints (("Subgoal 1" :expand (ev$ (cons fn args) a)))))

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
; eventually prove theorems that handle all apply$s that can be handled.  The
; first two rules for apply$ are:

(defthm beta-reduction
  (equal (apply$ (list 'LAMBDA vars body) args)
         (ev$ body (pairlis$ vars args))))

(defthm f-classes-primitive
  (implies (apply$-primp fn)
           (equal (f-classes fn) t)))

(defthm f-classes-f-classes
  (equal (f-classes 'f-classes) t))

(defthm f-classes-tamep
  (equal (f-classes 'tamep) t))

(defthm f-classes-tamep-functionp
  (equal (f-classes 'tamep-functionp) t))

(defthm f-classes-suitably-tamep-listp
  (equal (f-classes 'suitably-tamep-listp) t))

(defthm f-classes-apply$
  (equal (f-classes 'apply$) '(:fn NIL)))

(defthm f-classes-ev$
  (equal (f-classes 'ev$) '(:expr NIL)))

(defthm apply$-primitive
  (implies (apply$-primp fn)
           (equal (apply$ fn args)
                  (apply$-prim fn args))))

(defthm apply$-f-classes
  (equal (apply$ 'F-CLASSES args)
         (f-classes (car args))))

(defthm apply$-tamep
  (equal (apply$ 'TAMEP args)
         (tamep (car args))))

(defthm apply$-tamep-functionp
  (equal (apply$ 'TAMEP-FUNCTIONP args)
         (tamep-functionp (car args))))

(defthm apply$-suitably-tamep-listp
  (equal (apply$ 'SUITABLY-TAMEP-LISTP args)
         (suitably-tamep-listp (car args) (cadr args))))

(in-theory (disable f-classes
                    (:executable-counterpart f-classes)
                    apply$
                    (:executable-counterpart apply$)))

; -----------------------------------------------------------------
; The Applicability Hypotheses

; Suppose AP is defined (with the new defun$) to be a tame function of two
; arguments.  Then the new defun$ will also do:

; (defun-sk applicablep-AP nil
;   (forall (args) (and (equal (f-classes 'AP) t)
;                       (equal (apply$ 'AP args)
;                              (ap (car args) (cadr args))))))

; (defthm apply$-AP
;   (implies (force (applicablep-AP))
;            (and (equal (f-classes 'AP) t)
;                 (equal (apply$ 'AP args)
;                        (ap (car args) (cadr args))))))

; (in-theory (disable applicablep-AP))

; which will mean that if we have the hypothesis (applicablep-AP), we will rewrite
; (f-classes 'AP) to T and rewrite (apply$ 'AP args) to the appropriate call of
; ap.  [Actually, instead of f-classes and apply$ above the defun-sk is about
; f-classes-nonprim and apply$-nonprim.  But the snippet above is spiritually
; correct.]

; ----------------------------------------------------------------- 
; Sugarcoating Applicability Hypotheses

; We don't want to write or read things like:

; (implies (and (applicablep-AP)                                  ; [1]
;               (applicablep-REV)
;               (applicablep-COLLECT)
;               ... other hyps...)
;          concl)

; We prefer to write and read:

; (implies (and (Applicablep AP REV COLLECT)                      ; [2]
;                ... other hyps...)
;           concl)

; In this section we arrange for this abbreviation.  Note that (applicablep ap
; rev collect) does not expand into a conjunction!  That would put individual
; applicablep-fn hypotheses into the hypotheses and they would not be collected
; together again by prettyprinting.  Instead, we keep them together in a list.
; Furthermore, each hypotheses is marked by a special function and we have
; rules that tell us how to find these hypotheses in the list.

; First, we adopt the convention that every applicablep hypothesis, h, is
; marked by being embedded in a call of the identity function
; applicablep-marker.  The reason for this marking will become clearer in a
; moment.

; Then we define applicablep as a macro that expands, in the case of [2] above,
; to

; (applicablep-listp (list (applicablep-marker (applicablep-ap))  ; [3]
;                          (applicablep-marker (applicablep-rev))
;                          (applicablep-marker (applicablep-collect))))

; Then we prove two theorems that enable us to relieve marked applicablep-fn
; hyps by inspecting calls of applicablep-listp.

; Finally, we arrange to prettyprint [3] as [2].

(defun applicablep-marker (x) x)

(defun make-applicablep-name (fn)
  (declare (xargs :guard (symbolp fn)))
  (intern-in-package-of-symbol
   (coerce
    (append '(#\A #\P #\P #\L #\I #\C #\A #\B #\L #\E #\P #\-)
            (coerce (symbol-name fn) 'list))
    'string)
   fn))

(encapsulate
 nil
 (local
  (defthm character-listp-cdr
    (implies (character-listp x)
             (character-listp (cdr x)))))

 (defun unmake-applicablep-name (hyp-name)
   (declare (xargs :guard (symbolp hyp-name)))
   (intern-in-package-of-symbol
    (coerce (cddddr (cddddr (cddddr (coerce (symbol-name hyp-name) 'list))))
            'string)
    hyp-name)))

(defun make-list-applicablep (names)
  (declare (xargs :guard (symbol-listp names)))
  (cond ((endp names) nil)
        (t (cons (list 'applicablep-marker
                       (list (make-applicablep-name (car names))))
                 (make-list-applicablep (cdr names))))))


(defmacro Applicablep (&rest names)
  (declare (xargs :guard (symbol-listp names)))
  `(applicablep-listp (list ,@(make-list-applicablep names))))

(defun applicablep-listp (lst)

; This is just the conjunction over lst, but has the unusual name so we can
; expect it only to be used with conjunctions of apply hyps.

  (if (endp lst)
      t
      (and (car lst)
           (applicablep-listp (cdr lst)))))

(defthm applicablep-lemma1
  (implies (and (applicablep-listp lst)
                (member (applicablep-marker a) lst))
           (applicablep-marker a)))

(defthm applicablep-lemma2
  (implies (and (applicablep-listp lst1)
                (subsetp lst2 lst1))
           (applicablep-listp lst2)))

(in-theory (disable applicablep-marker applicablep-listp
                    (:executable-counterpart applicablep-marker)
                    (:executable-counterpart applicablep-listp)))

(defun applicablep-untranslate-preprocess1 (term)
  (cond
   ((variablep term)
    :unrecognized)
   ((fquotep term)
    (cond
     ((equal term *nil*)
      nil)
     (t :unrecognized)))
   ((eq (ffn-symb term) 'cons)
    (let ((rest (applicablep-untranslate-preprocess1 (fargn term 2))))
      (cond
       ((eq rest :unrecognized)
        :unrecognized)
       (t
        (let ((hyp (fargn term 1)))
          (case-match hyp
            (('applicablep-marker (applicablep-name))
             (cond
              ((symbolp applicablep-name)
               (let ((fn-name (unmake-applicablep-name applicablep-name)))
                 (cond
                  ((eq applicablep-name (make-applicablep-name fn-name))
                   (cons fn-name rest))
                  (t :unrecognized))))
              (t :unrecognized)))
            (& :unrecognized)))))))
   (t :unrecognized)))

(defun applicablep-untranslate-preprocess (term w)

; When this function returns nil it means that we do not do anything special to
; term, i.e., it is untranslated and prettyprinted by ACL2's standard
; mechanism.  If we return non-nil, the returned ``term'' is prettyprinted in
; its place.

  (declare (ignore w))
  (case-match term
    (('applicablep-listp term)
     (let ((temp (applicablep-untranslate-preprocess1 term)))
       (cond
        ((eq temp :unrecognized)
         nil)
        (t `(Applicablep ,@temp)))))
    (& nil)))

(table user-defined-functions-table
       'untranslate-preprocess
       'applicablep-untranslate-preprocess)

; -----------------------------------------------------------------
; The F-Classes Table:

; In order to compute the f-classes of a new defun, we must be able to look up
; the f-classes of all the pre-defined functions.  We will have apply
; hypotheses telling us the relevant f-classes, but we need an easier way to
; find f-classes than inspecting the defun-sk for the function's apply
; hypothesis.  So we maintain a table for that purpose.  Every time a new
; function is introduced, we extend the table.

; But first, we have to be able to compute the f-classes of a term from the
; f-classes in the table.  Here is how we do that.

; Every formal has one of these flags assigned to it:
; nil (meaning :vanilla)
; :fn
; :expr
; :unknown
; with the convention that if any formal is :unknown, they all are.
; Furthermore, if all of the formals are :vanilla, then we assign the classes t
; to it.

; We never put :unknown into the table, so if a function has an :unknown
; formal, the function just isn't in the table at all and any function that
; calls it will inherit an :unknown classification.  Thus, the table entries
; are always either t or lists of nil, :fn, and/or :expr flags.

; TODO: We don't deal with mutual recursion yet!

; TODO: We handle lambda applications in function bodies by beta reducing them.
; This can be pretty inefficient.

; TODO: I think the above conflicts with the treatment of lambdas in tamep,
; which treats all lambda formals as :vanilla.  I think I may be misclassifying
; some formals.  Provoke an oddity!

; Let's assume that 
; (a) body does not return multiple values,
; (b) body does not use STATE or any stobj,
; (c) every :fn slot and :expr slot of every function called in body is
;     occupied by either a quoted constant or a formal variable, and
; (d) body does not call any functions of :unknown classes.

; We call these the pre-check conditions.

; Then to check that the ith formal, var, has class :fn we can proceed as
; follows:

;   let n1 be the number of times var occurs as the actual in a :fn slot.
;   Let n2 be the number of times var occurs as the actual in the ith slot of a
;   recursive call.
;   Let n3 be the number of recursive calls.
;   Let k be the number of times var occurs in the body.

;   Then if n1 > 0, n2=n3, and n1+n2 = k then we know that var occurs at least
;   once in a functional slot, it is always passed identically in recursion,
;   and it occurs nowhere else.

; The analogous check works for formals of class :expr.

; To check that a formal is of class :vanilla, we check that every occurrence
; is in a :vanilla slot.

; If any formal is not of one of the classes, it is :unknown.

; Note that this works only if the pre-check conditions hold.  For example, x
; in (apply$ (cons x x) y) would be classed as :vanilla were it not for
; pre-check condition (c).

; Note about Lambda Applications

; We beta reduce all lambda applications when classifying the formals of
; defuns.  This is pretty inefficient for large defuns.  We might want to
; re-implement it.  But there is a subtlety here.

; Consider ((lambda (x y) (cons (apply$ x y) (apply$ x y))) fn args).  To count
; the number of times fn occurs in a :fn slot, we beta reduce this application
; to (cons (apply$ fn args) (apply$ fn args)) and then report that fn is used 2
; times.  Since we are comparing this sense of ``how many'' with count-occur,
; we must do beta reduction in count-occur.  That's odd because if asked how
; many times fn occurs in the lambda application above the answer is surely 1.
; But to be comparable to the way we count :fn occurrences we have to say 2.
; So if we optimize the way we count special (and other occurrences) to
; eliminate the beta reductions, be sure to keep all the counts comparable.

(mutual-recursion
 (defun all-special-slots-okp (fn flag term f-classes-alist)
   (declare (xargs :mode :program))
   (cond
    ((variablep term)
     t)
    ((fquotep term)
     t)
    ((or (eq flag :fn)
         (eq flag :expr))
     nil)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (all-special-slots-okp
      fn flag
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))
      f-classes-alist))
    ((eq fn (ffn-symb term))
     (all-special-slots-okp-list fn nil (fargs term) f-classes-alist))
    (t (let ((pair (assoc (ffn-symb term) f-classes-alist)))
         (cond
          ((null pair) nil)
          ((eq (cdr pair) t)
           (all-special-slots-okp-list fn nil (fargs term) f-classes-alist))
          (t (all-special-slots-okp-list fn (cdr pair) (fargs term) f-classes-alist)))))))

 (defun all-special-slots-okp-list (fn flags terms f-classes-alist)
   (cond
    ((endp terms) t)
    (t (and (all-special-slots-okp fn (car flags) (car terms) f-classes-alist)
            (all-special-slots-okp-list fn (cdr flags) (cdr terms) f-classes-alist))))))

(defun pre-check-body-for-classify-formals (fn body f-classes-alist wrld)
  (declare (xargs :mode :program))
  (and (all-nils (getprop fn 'stobjs-in nil 'current-acl2-world wrld))
       (equal (length (getprop fn 'stobjs-out nil 'current-acl2-world wrld)) 1)
       (null (car (getprop fn 'stobjs-out nil 'current-acl2-world wrld)))
       (all-special-slots-okp fn :vanilla body f-classes-alist)))

(mutual-recursion
 (defun count-special-occurrences (fn var spec-flag flag term f-classes-alist)
   (declare (xargs :mode :program))
   (cond
    ((variablep term)
     (cond ((and (eq var term)
                 (eq spec-flag flag))
            1)
           (t 0)))
    ((fquotep term)
     0)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (count-special-occurrences
      fn var spec-flag flag
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))
      f-classes-alist))
    ((eq fn (ffn-symb term))
     (count-special-occurrences-list fn var spec-flag nil (fargs term) f-classes-alist))
    (t (let ((pair (assoc (ffn-symb term) f-classes-alist)))
         (cond
          ((null pair) 0)
          ((eq (cdr pair) t)
           (count-special-occurrences-list fn var spec-flag nil (fargs term) f-classes-alist))
          (t (count-special-occurrences-list fn var spec-flag (cdr pair) (fargs term) f-classes-alist)))))))  

 (defun count-special-occurrences-list (fn var spec-flag flags terms f-classes-alist)
   (cond
    ((endp terms) 0)
    (t (+ (count-special-occurrences fn var spec-flag (car flags) (car terms) f-classes-alist)
          (count-special-occurrences-list fn var spec-flag (cdr flags) (cdr terms) f-classes-alist))))))

(mutual-recursion
 (defun count-unchanged-formal (fn var i term)
   (declare (xargs :mode :program))
   (cond
    ((variablep term) 0)
    ((fquotep term) 0)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (count-unchanged-formal
      fn var i
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))))
    (t
     (+ (if (and (eq fn (ffn-symb term))
                 (eq var (nth i term)))
            1
            0)
        (count-unchanged-formal-list fn var i (fargs term))))))
 (defun count-unchanged-formal-list (fn var i terms)
   (cond
    ((endp terms) 0)
    (t (+ (count-unchanged-formal fn var i (car terms))
          (count-unchanged-formal-list fn var i (cdr terms)))))))

(mutual-recursion
 (defun count-calls (fn term)
   (declare (xargs :mode :program))
   (cond
    ((variablep term) 0)
    ((fquotep term) 0)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (count-calls
      fn
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))))
    (t (+ (if (eq fn (ffn-symb term)) 1 0)
          (count-calls-list fn (fargs term))))))
 (defun count-calls-list (fn terms)
   (cond
    ((endp terms) 0)
    (t (+ (count-calls fn (car terms))
          (count-calls-list fn (cdr terms)))))))

(mutual-recursion
 (defun count-occur (var term)
   (declare (xargs :mode :program))
   (cond
    ((variablep term)
     (if (eq var term) 1 0))
    ((quotep term) 0)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (count-occur
      var
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))))
    (t (count-occur-list var (fargs term)))))
 (defun count-occur-list (var terms)
   (cond
    ((endp terms) 0)
    (t (+ (count-occur var (car terms))
          (count-occur-list var (cdr terms)))))))

(defun functional-formalp (fn var i term f-classes-alist)
  (declare (xargs :mode :program))
  (let ((n1 (count-special-occurrences fn var :fn nil term f-classes-alist))
        (n2 (count-unchanged-formal fn var i term))
        (n3 (count-calls fn term))
        (k (count-occur var term)))
    (and (> n1 0)
         (= n2 n3)
         (= (+ n1 n2) k))))

(defun expressional-formalp (fn var i term f-classes-alist)
  (declare (xargs :mode :program))
  (let ((n1 (count-special-occurrences fn var :expr nil term f-classes-alist))
        (n2 (count-unchanged-formal fn var i term))
        (n3 (count-calls fn term))
        (k (count-occur var term)))
    (and (> n1 0)
         (= n2 n3)
         (= (+ n1 n2) k))))

(defun vanilla-formalp (fn var term f-classes-alist)
  (declare (xargs :mode :program))
  (let ((n1 (count-special-occurrences fn var nil nil term f-classes-alist))
        (k (count-occur var term)))
    (= n1 k)))

(defun classify-formal (fn var i term f-classes-alist)
  (declare (xargs :mode :program))
  (cond
   ((functional-formalp fn var i term f-classes-alist) :fn)
   ((expressional-formalp fn var i term f-classes-alist) :expr)
   ((vanilla-formalp fn var term f-classes-alist) nil)
   (t :unknown)))

(defun classify-formals1 (fn vars i term f-classes-alist)
  (declare (xargs :mode :program))
  (cond
   ((endp vars) nil)
   (t (cons (classify-formal fn (car vars) i term f-classes-alist)
            (classify-formals1 fn (cdr vars) (+ 1 i) term f-classes-alist)))))

(defun classify-formals (fn wrld)
  (declare (xargs :mode :program))
  (let ((body (body fn nil wrld))
        (formals (formals fn wrld))
        (f-classes-alist (table-alist 'f-classes-table wrld)))
    (cond
     ((pre-check-body-for-classify-formals fn body f-classes-alist wrld)
      (let ((flags (classify-formals1 fn formals 1 body f-classes-alist)))
        (cond
         ((member-eq :unknown flags) :unknown)
         ((all-nils flags) t)
         (t flags))))
     (t :unknown))))

; -----------------------------------------------------------------
; Functional Equivalence

; We now develop the notion of two functions being equivalent.  The basic idea
; is that fn1 is functionally equivalent to fn2 if they are both tame and
; apply$ cannot distinguish them.  We define fn-equal to be this concept, but
; first need the quantified statement that apply$ cannot distinguish the two.

(defun-sk apply$-equivalence (fn1 fn2)
  (forall (args)
    (equal (apply$ fn1 args)
           (apply$ fn2 args))))

(defun fn-equal (fn1 fn2)
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

(defequiv fn-equal)

; The following rewrite rule is needed to prove that fn-equal is an equivalence
; and to prove that fn-equal is an equality preserving congruence for mapping
; functions.  But it might be too expensive in general.  It's possibly saving
; grace is the presence of fn2 as a free var.  We'll start this development by
; making it non-local and enabled but that might change.

(defthm fn-equal-apply$-rewriter
    (implies (and (fn-equal fn1 fn2)
                  (syntaxp (and (not (equal fn1 fn2))
                                (term-order fn1 fn2))))
             (equal (apply$ fn1 args)
                    (apply$ fn2 args))))

(in-theory (disable fn-equal))

; Every time a mapping function is introduced we also prove the fn-equal
; congruence rule.  Here is how we generate it.  For example,

; (generate-fn-equal-congruences '(collect lst fn) 1 '(nil :fn))

; produces the list containing just

; (defcong fn-equal equal (collect lst fn) 2)

(defun defcong-fn-equal-equal-events (term i f-classes)
  (cond
   ((endp f-classes) nil)
   ((eq (car f-classes) :FN)
    (cons `(defcong fn-equal equal ,term ,i)
          (defcong-fn-equal-equal-events term (+ 1 i) (cdr f-classes))))
   (t (defcong-fn-equal-equal-events term (+ 1 i) (cdr f-classes)))))

; -----------------------------------------------------------------
; Creating the Applicablep Hypothesis for Fn

; Given a fn whose f-classes are known (and not :unknown!), we can create the
; Applicablep Hypothesis for fn with make-applicablep-event.  The three
; functions defined immediately below are just helpers for that function.

(defun applicablep-tamep-hyps (formals f-classes var)
  (declare (xargs :mode :program))
  (cond ((endp formals) nil)
        ((eq (car f-classes) :fn)
         (cons `(TAMEP-FUNCTIONP (CAR ,var))
               (applicablep-tamep-hyps (cdr formals) (cdr f-classes) (list 'CDR var))))
        ((eq (car f-classes) :expr)
         (cons `(TAMEP (CAR ,var))
               (applicablep-tamep-hyps (cdr formals) (cdr f-classes) (list 'CDR var))))
        (t (applicablep-tamep-hyps (cdr formals) (cdr f-classes) (list 'CDR var)))))

(defun applicablep-actuals (formals var)
  (declare (xargs :mode :program))
  (cond ((endp formals) nil)
        (t
         (cons `(CAR ,var)
               (applicablep-actuals (cdr formals) (list 'CDR var))))))

(defun applicablep-ARGS-instance (f-classes)
  (cond ((endp f-classes) nil)
        ((eq (car f-classes) :fn)
         (cons 'EQUAL (applicablep-ARGS-instance (cdr f-classes))))
        ((eq (car f-classes) :expr)
         (cons 'T (applicablep-ARGS-instance (cdr f-classes))))
        (t (cons nil (applicablep-ARGS-instance (cdr f-classes))))))

(defun make-applicablep-event (fn formals f-classes)

; This function should only be called if f-classes is t or a list containing at
; least one :FN or :EXPR flag.  It should not be called on :UNKNOWN or on a
; list of nils.  This function returns a list of events that add the
; appropriate defun-sk event for fn (if any) and then proves the necessary
; rewrite rule.

  (declare (xargs :mode :program))
  (let* ((name (make-applicablep-name fn))
         (rule-name (intern-in-package-of-symbol
                     (coerce (append '(#\A #\P #\P #\L #\Y #\$ #\-)
                                     (coerce (symbol-name fn) 'list))
                             'string)
                     fn))
         (necc-name (intern-in-package-of-symbol
                     (coerce
                      (append (coerce (symbol-name name) 'list)
                              '(#\- #\N #\E #\C #\C))
                      'string)
                     fn)))
    (cond
     ((eq f-classes t)
      `((defun-sk ,name ()
          (forall (args)
            (and (equal (f-classes-nonprim ',fn) t)
                 (equal (apply$-nonprim ',fn args)
                        (,fn ,@(applicablep-actuals formals 'args))))))
        (in-theory (disable ,name))
        (defthm ,rule-name
          (implies (force (Applicablep ,fn))
                   (and (equal (f-classes ',fn) t)
                        (equal (apply$ ',fn args)
                               (,fn ,@(applicablep-actuals formals 'args)))))
          :hints (("Goal" :use ,necc-name
                   :expand ((:free (x) (HIDE (f-classes x))))
                   :in-theory (e/d (f-classes apply$
                                    (:executable-counterpart applicablep-marker)
                                    (:executable-counterpart applicablep-listp))
                                   (,necc-name)))))))
     (t
      (let* ((hyp-list (applicablep-tamep-hyps formals f-classes 'ARGS))
             (hyp (if (null (cdr hyp-list))
                      (car hyp-list)
                      `(AND ,@hyp-list))))
        `((defun-sk ,name ()
            (forall (args)
              (implies ,hyp
                       (and (equal (f-classes-nonprim ',fn) ',f-classes)
                            (equal (apply$-nonprim ',fn args)
                                   (,fn ,@(applicablep-actuals formals 'args)))))))
          (in-theory (disable ,name))
          (defthm ,rule-name
            (and (implies (force (Applicablep ,fn))
                          (equal (f-classes ',fn) ',f-classes))
                 (implies (and (force (Applicablep ,fn))
                               ,hyp)
                          (equal (apply$ ',fn args)
                                 (,fn ,@(applicablep-actuals formals 'args)))))

; Notice that the necc-name theorem is of the form (forall (args) (and ...))
; but the theorem above is essentially (and ... (forall (args) ...)) because
; the first conjunct is free of ARGS.  We had to write necc-name that way
; because of the requirements of defun-sk.  But now we have to extract the fact
; that we know (Applicablep fn) --> (f-classes 'fn) = <whatever>, by instantiating
; necc-name with a suitable ARGS that makes the right components suitably tame.

; The first :instance below takes care of the f-classes conjunct and the second
; takes care of the apply$ conjunct.

            :hints
            (("Goal"
              :use ((:instance ,necc-name
                               (ARGS ',(applicablep-ARGS-instance f-classes)))
                    (:instance ,necc-name))
              :expand ((:free (x) (HIDE (f-classes x))))
              :in-theory (e/d (f-classes apply$
                                         (:executable-counterpart applicablep-marker)
                                         (:executable-counterpart applicablep-listp))
                              (,necc-name)))))))))))

(defun ancestral-all-fnnames1 (flg x wrld ans)
  (declare (xargs :mode :program))
  (cond
   (flg ; x is a list of fnnames
    (cond ((null x) ans)
          (t (ancestral-all-fnnames1
              t (cdr x) wrld
              (ancestral-all-fnnames1 nil (car x) wrld ans)))))
   ((or (member-eq x ans)
        (member-eq x '(apply$ ev$ ev$-list)))
    ans)
   (t (ancestral-all-fnnames1
       t (all-fnnames (body x nil wrld)) wrld
       (cons x ans)))))

(defun remove-fns-with-known-f-classes (lst f-classes)
  (declare (xargs :mode :program))
  (cond
   ((null lst) nil)
   ((assoc-eq (car lst) f-classes)
    (remove-fns-with-known-f-classes (cdr lst) f-classes))
   (t (cons (car lst)
            (remove-fns-with-known-f-classes (cdr lst) f-classes)))))

(defmacro make-applicable (fn)
  `(with-output
    :off :all
    :stack :push
    :gag-mode nil
    (make-event
     (with-output
      :stack :pop
      (let ((fn ',fn)
            (wrld (w state)))
        (cond
         ((and (symbolp fn)
               (arity fn wrld)
               (not (eq (getprop fn 'symbol-class nil 'current-acl2-world wrld)
                        :PROGRAM))
               (body fn nil wrld))
          (cond
           ((assoc-eq fn (table-alist 'f-classes-table  wrld))
            (prog2$
             (cw "~%~x0 is already applicable, with f-classes ~x1.~%"
                 fn
                 (cdr (assoc-eq fn (table-alist 'f-classes-table  wrld))))
             (value '(value-triple :invisible))))
           (t
; We know fn is a logic mode function symbol.
            (let ((f-classes (classify-formals fn wrld)))
              (cond
               ((eq f-classes :UNKNOWN)
                (let ((ancestral-fns
                       (remove-fns-with-known-f-classes
                        (ancestral-all-fnnames1 nil fn wrld nil)
                        (table-alist 'f-classes-table wrld))))
                  (cond
                   ((null (cdr ancestral-fns))
                    (er soft 'make-applicable
                        "~x0 cannot be made applicable because of one of the ~
                         following: (a) it returns multiple values, (b) it ~
                         uses STATE or some other stobj (or the primordial ~
                         state-like formal STATE-STATE), (c) it does not ~
                         respect the syntactic conventions on the use of ~
                         functional and/or expressional argument positions in ~
                         its body (e.g., it uses one of its formals in both a ~
                         functional slot and a vanilla slot)."
                        fn))
                   (t
                    (er soft 'make-applicable
                        "~x0 cannot be made applicable at this time because it ~
                        (somehow) calls one or more functions that are not ~
                        yet applicable.  You should try to make these other ~
                        functions applicable first.  Of course, they may not ~
                        satisfy our restrictions on applicability and so it ~
                        may be impossible.  We recommend that you try to make ~
                        each of the following functions applicable in the ~
                        order they are listed: ~x1."
                        fn ancestral-fns)))))
               (t (value
                   `(encapsulate
                     nil
                     ,@(make-applicablep-event fn (formals fn wrld) f-classes)
                     (table f-classes-table
                            ',fn ',f-classes :put)
                     ,@(if (eq f-classes t)
                           nil
                           (defcong-fn-equal-equal-events (cons fn (formals fn wrld))
                             1 f-classes))
                     (with-output
                      :stack :pop
                      (value-triple (cw "~%~x0 is now applicable, with f-classes ~x1.~%~%"
                                        ',fn ',f-classes)))))))))))
         ((and (symbolp fn)
               (arity fn wrld)
               (null (body fn nil wrld)))
          (er soft 'make-applicable
              "~x0 is a declared function and cannot be made ~
              applicable.  Sorry!"
              fn))
         (t (er soft 'make-applicable
                "Make-applicable should only be called on a defined logical ~
                 function symbol.  It is not permitted to call it on a ~
                 non-symbol, a symbol that is not a function symbol, or a ~
                 function symbol in :PROGRAM mode.  ~x0 is an inappropriate ~
                 argument."
                fn))))))))

(defmacro defun$ (fn formals &rest rest)
  (let ( ;(body (car (last rest)))
;(dcls (all-but-last rest))
        )
    `(progn
      (defun ,fn ,formals ,@rest)
      (make-applicable ,fn))))

; -----------------------------------------------------------------
; The Lamb Hack

; It is helpful to avoid using constants for lambda expressions so that we can
; rewrite them with fn-equal rewrite rules.  ACL2's rewriter returns term as
; soon as it detects (fquotep term).  So a rewrite rule like (fn-equal (list
; 'lambda (list v) v) 'identity) would not fire on '(lambda (v) v) in a
; fn-equal slot because we don't rewrite constants.  Therefore, we will write
; (lamb '(v) 'v) and rewrite lamb expressions.  We want lamb and its executable
; counterpart to be disabled in proofs.  But we want it to execute at the top
; level so we can run things like (sumlist '(1 2 3) (lamb '(x) 'x)).  So we
; merely constrain lamb logically and attach an executable function to it.

(encapsulate
 ((lamb (args body) t))
 (local
  (defun lamb (args body)
    (list 'lambda args body)))
 (defthm consp-lamb
   (and (consp (lamb args body))
        (true-listp (lamb args body)))
   :rule-classes :type-prescription)
 (defthm car-lamb
   (equal (car (lamb args body)) 'lambda))

 (defthm lambda-formals-lamb
   (equal (lambda-formals (lamb args body)) args))

 (defthm lambda-body-lamb
   (equal (lambda-body (lamb args body)) body))

 (defthm lamb-reduction
   (equal (apply$ (lamb vars body) args)
          (ev$ body (pairlis$ vars args)))))

(defun xlamb (args body)
  (declare (xargs :guard t))
  (list 'lambda args body))

(defattach lamb xlamb)
