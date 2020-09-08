; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore (some years before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)

(defun listify-untranslated-expand-hint (arg)

; This function should be similar to translate-expand-hint1.  It
; recognizes the three special cases in which a user can provide an
; object to the :expand hint and have that object treated as a
; singleton list of objects, as illustrated by these three examples:

;  :EXPAND :LAMBDAS
;  :EXPAND (append a b)
;  :EXPAND ((lambda (x y) (append x y)) a b)

  (cond
   ((eq arg :lambdas) (list arg))
   ((and (consp arg)
         (symbolp (car arg))
         (not (eq (car arg) :lambdas)))
    (list arg))
   ((and (consp arg)
         (consp (car arg))
         (eq (caar arg) 'lambda))
    (list arg))
   (t arg)))

(defun listify-untranslated-hands-off (arg)
  (cond ((and arg (symbolp arg))
         (list arg))
        ((and (consp arg) (eq (car arg) 'lambda))
         (list arg))
        (t arg)))

(defun listify-untranslated-use (arg wrld)
  (cond ((atom arg) (list arg))
        ((or (eq (car arg) :instance)
             (eq (car arg) :functional-instance)
             (eq (car arg) :theorem)
             (runep arg wrld))
         (list arg))
        (t arg)))

(defun true-list-of-non-empty-true-listsp (x)
  (cond ((atom x) (equal x nil))
        (t (and (consp (car x))
                (true-listp (car x))
                (true-list-of-non-empty-true-listsp (cdr x))))))

(defun remove-assoc-equals (key alist)
  (cond ((endp alist) nil)
        ((equal key (caar alist))
         (remove-assoc-equals key (cdr alist)))
        (t (cons (car alist)
                 (remove-assoc-equals key (cdr alist))))))

(defun merge-restrict-hints (alist1 alist2)

; We assume both alists are true-lists of non-empty true-lists, e.g.,
; of the form ((x1 s1 ... sk) ...).  That will be sufficient to ensure
; our guards.  We guarantee that each xi and each si is in our final
; answer.  Thus, if either alist would fail to translate because an xi
; is not a rune or event name or an si is not a proper substitution,
; the merged answer will fail too.

; As of ACL2 Version 3.1, it was legal to provide a :RESTRICT hint
; with two bindings of a rune or name.  Only the first one was
; relevant though because we access the translated restrictions with
; assoc on the rune.  Thus, when we find a binding in both alists, we
; remove all subsequent occurrences of it from both alists.

  (cond
   ((endp alist1) alist2)
   ((assoc-equal (car (car alist1)) alist2)

; This "rune or name" is bound in both alists.  So we'll union
; together the substitutions associated with it in both places and
; delete all other bindings of the rune (or name) from both alists.

    (cons (cons (car (car alist1))
                (union-equal (cdr (car alist1))
                             (cdr (assoc-equal (car (car alist1)) alist2))))
          (merge-restrict-hints (remove-assoc-equals
                                 (car (car alist1))
                                 (cdr alist1))
                                (remove-assoc-equals
                                 (car (car alist1))
                                 alist2))))
   (t (cons (car alist1)
            (merge-restrict-hints (cdr alist1) alist2)))))


(defun mergeable-theory-expressionp (arg)

; The only mergeable theory expressions are (ENABLE ...), (DISABLE
; ...), and (E/D ... ...).

  (and (consp arg)
       (true-listp (cdr arg))
       (cond ((eq (car arg) 'enable) t)
             ((eq (car arg) 'disable) t)
             ((eq (car arg) 'e/d)
              (and (equal (len arg) 3)
                   (true-listp (cadr arg))
                   (true-listp (caddr arg))))
             (t nil))))

(defun merge-mergeable-theory-expressions (val1 val2)
  (case (car val2)
    (ENABLE
     `(union-theories ,val1 (quote ,(cdr val2))))
    (DISABLE
     `(set-difference-theories ,val1 (quote ,(cdr val2))))
    (t ; E/D
     `(set-difference-theories
       (union-theories ,val1 (quote ,(cadr val2)))
       (quote ,(caddr val2))))))

(defun merge-hint (keyword-alist key val2 wrld)

; In CLTL, when keyword arguments are supplied and a key is
; duplicated, it is the leftmost binding that matters.  Thus, in CLTL
; (foo :ABC 1 :DEF NIL :ABC 2), the :ABC argument has value 1.  So
; merging the values of duplicate keywords is quite unconventional!
; That said, we do our best or generate an appropriate :ERROR hint.
; As suggested by the order of the arguments, we think of key val as
; being appended to the right end of the keyword-alist.  Thus the
; value of key in keyword-alist, if any, is to the left of the new
; occurrence of key.  For example, we interpret :in-theory a
; :in-theory (disable b c d) as (set-difference-theories a '(b c d)).
; Note that if the two :in-theory values were swapped we would get a
; different theory.  (In fact, we don't know how to merge theories at
; all, except when the second was produced by ENABLE, DISABLE, and
; E/D, which are technically defined relative to the current theory.
; Our interpretation of a sequence of :in-theory hints is that they
; successively redefine current-theory.)

  (cond
   ((endp keyword-alist)
    (list key val2))
   ((eq (car keyword-alist) key)
    (let ((val1 (cadr keyword-alist)))

; In almost every case we will generate a new alist by replacing key
; and val1 by key and a merged value created from val1 and val2.  But
; occasionally we wish to signal an error.  We do that by replacing
; key and val1 by :ERROR and an appropriate message.

      (case key
        (:ERROR

; We merge error hints by producing a message that will print both of
; them.

         (let ((str "This hint produced several errors:~ ~*0~%")
               (directive "~%~%~@*"))
           (cond
            ((and (consp val1)
                  (equal (car val1) str)
                  (equal (len (cdr val1)) 5)
                  (equal (nth 0 (cdr val1)) directive)
                  (equal (nth 1 (cdr val1)) directive)
                  (equal (nth 2 (cdr val1)) directive)
                  (equal (nth 3 (cdr val1)) directive))

; In this case, val1 is already a merged hint and we just add val2 to
; the list we'll print.  The purpose of the cond below is to ensure
; that val2 can be printed by a ~@ directive: if val2 is appropriate
; for ~@ we just use val2, otherwise we turn val2 into a ~@ message
; that prints the old val2 with ~X.

             (list*
              :ERROR
              (msg str
                   (list directive directive directive directive
                         (append (nth 4 (cdr val1))
                                 (list
                                  (cond
                                   ((and (consp val2)
                                         (stringp (car val2))
                                         (eqlable-alistp (cdr val2)))
                                    val2)
                                   (t (msg "~X01" val2 nil)))))))
              (cddr keyword-alist)))
            (t

; In this case, val1 is some single error message and start collecting
; a list of them.  The cond idiom below is explained in the comment
; above.

             (list*
              :ERROR
              (msg str
                   (list directive directive directive directive
                         (list
                          (cond
                           ((and (consp val1)
                                 (stringp (car val1))
                                 (eqlable-alistp (cdr val1)))
                            val1)
                           (t (msg "~X01" val1 nil)))
                          (cond
                           ((and (consp val2)
                                 (stringp (car val2))
                                 (eqlable-alistp (cdr val2)))
                            val2)
                           (t (msg "~X01" val2 nil))))))
              (cddr keyword-alist))))))

        (:NO-OP

; The value provided with a :NO-OP hint is irrelevant and so the merged value
; will be T, arbitrarily.

         (list* :NO-OP T (cddr keyword-alist)))
        (:EXPAND

; The value provided with an :EXPAND hint is generally a list of terms
; and the obvious way to merge them is to union the two lists
; together.  But some special cases are supported, allowing the user
; to provide an object that is understood as a singleton list
; containing that object, e.g., :expand (append a b) is a short-hand
; for :expand ((append a b)), and so we have to recognize these cases
; and make sure we are dealing with lists before we union.

         (list*
          :EXPAND
          (union-equal
           (listify-untranslated-expand-hint val1)
           (listify-untranslated-expand-hint val2))
          (cddr keyword-alist)))

        (:RESTRICT

; The value provided with a :RESTRICT hint must be an association list
; pairing runes (or event names) with substitutions.  For convenience
; in this comment, we'll call all the keys "runes."  The obvious merge
; is to union together the substitutions provided for runes bound in
; each alist and to concatenate remaining bindings.

; However, we don't know that val1 and val2 will in fact pass
; translation!  They might be anything generated by some buggy
; computed hint.  We must not provoke a hard error while trying to
; create the merged valued.  Ideally, if either vali would fail
; translation we want to insure that the merged value will fail
; translation too.  A vali would fail if (a) not a true-list or (b)
; some element is not a rune (or name) followed by a true-list of
; substitutions.  Thus, if either vali is not a true-list of non-empty
; true-lists we will return that val.  This will guarantee we get one
; of the errors we would have gotten in that case.  If both are
; true-lists of non-empty true-lists, then we'll do the more
; sophisticated merge, preserving all the "runes" and "substitutions"
; so that if one of them fails its test our answer will fail too.

         (list*
          :RESTRICT
          (cond ((not (true-list-of-non-empty-true-listsp val1))
                 val1)
                ((not (true-list-of-non-empty-true-listsp val2))
                 val2)
                (t (merge-restrict-hints val1 val2)))
          (cddr keyword-alist)))
        (:DO-NOT

; The value provided :DO-NOT is a form that when evaluated produces a
; list of processes to avoid.  If told to avoid A and B and also told
; to avoid B and C, the obvious sense of merge is to avoid A, B, and
; C.  So we union together the values.  But we don't have the values!
; We have the forms.  We have to make sure that the form we generate
; will evaluate both and cause an error if either of them is
; illegal and then otherwise produce a list of all the elements.

         (list*
          :DO-NOT
          `(let ((lst1 ,val1)
                 (lst2 ,val2))
             (cond
              ((not (true-listp lst1))
               lst1)
              ((not (true-listp lst2))
               lst2)
              (t (union-equal lst1 lst2))))
          (cddr keyword-alist)))
        (:DO-NOT-INDUCT

; The value provided :DO-NOT-INDUCT hint is nil, t, or a name.  Nil
; has no effect on the theorem prover's normal behavior and so is
; virtually never used.

         (list*
          :DO-NOT-INDUCT
          (cond

; If either value is a non-symbol, the corresponding hint would
; provoke an error on translation, so we return that same non-symbol
; to provoke an error on the translation of our merged answer.

           ((not (symbolp val1)) val1)
           ((not (symbolp val2)) val2)

; If either value is nil, the other clearly is the one we mean, since
; nil is the default behavior anyway.

           ((null val1) val2)
           ((null val2) val1)

; If either is non-t, then we are to give a bye to the inductive
; subgoals and then fail, and that behavior overrides the only
; behavior that could be specified by the other one, namely, simply to
; fail.  But if a

           ((not (eq val1 t)) val1)
           ((not (eq val2 t)) val2)

; Otherwise, both are t and we just use that as the merged value.

           (t t))
          (cddr keyword-alist)))
        (:HANDS-OFF

; The value of a :HANDS-OFF hint is generally a list of terms to
; avoid.  But we treat :HANDS-OFF (append a b) as we would :hands-off
; ((append a b)).  The obvious way to merge two such lists is to union
; them.

         (list*
          :HANDS-OFF
          (union-equal (listify-untranslated-hands-off val1)
                       (listify-untranslated-hands-off val2))
          (cddr keyword-alist)))
        (:USE
         (list*
          :USE
          (cond
; We provoke a translation error if either val is nil, since that
; would provoke a translation error.

           ((null val1) val1)
           ((null val2) val2)
           (t (union-equal (listify-untranslated-use val1 wrld)
                           (listify-untranslated-use val2 wrld))))
          (cddr keyword-alist)))
        (:OR
         (list*
          :OR
          (cond
           ((not (true-listp val1)) val1)
           ((not (true-listp val2)) val2)
           (t (union-equal val1 val2)))
          (cddr keyword-alist)))
        (:BY

; The value of a :BY hint is nil, a new name, an old name, or an lmi.
; The first two mean the indicated subgoal will be given a "bye" and
; the proof with fail.  The last two mean the indicated subgoal must
; be subsumed by the (instance of) named formula.  So classify val1
; into one of three cases: it is nil (or a new name), it is an lmi (or
; an old name), or it is an error (none of the above).  Similarly
; classify val2.  So consider the cases.  (i) if either is error,
; return that one; (ii) if they are in different classifications, then
; one is nil and the other is an lmi and we merge to the lmi so the
; proof will succeed; (iii) if both are ``nil'', choose either (but we
; prefer a user-supplied name over nil itself); (iv) if both are lmis,
; then we choose either.

         (list*
          :BY
          (let ((case1 (cond ((or (and val1
                                       (symbolp val1)
                                       (formula val1 t wrld))
                                  (consp val1))
                              'lmi)
                             ((or (null val1)
                                  (and (symbolp val1)
                                       (not (keywordp val1))
                                       (not (equal *main-lisp-package-name*
                                                   (symbol-package-name val1)))
                                       (new-namep val1 wrld)))
                              nil)
                             (t 'error)))
                (case2 (cond ((or (and val2
                                       (symbolp val2)
                                       (formula val2 t wrld))
                                  (consp val2))
                              'lmi)
                             ((or (null val2)
                                  (and (symbolp val2)
                                       (not (keywordp val2))
                                       (not (equal *main-lisp-package-name*
                                                   (symbol-package-name val2)))
                                       (new-namep val2 wrld)))
                              nil)
                             (t 'error))))
            (cond
             ((eq case1 'error) val1)
             ((eq case2 'error) val2)
             ((not (eq case1 case2))
              (if (eq case1 'lmi) val1 val2))
             ((eq case1 nil)
              (if (null val1) val2 val1))
             (t val1)))
          (cddr keyword-alist)))
        (:CASES

; The value provided to a :CASES hint is a true-list of terms.  The
; obvious merge is the union.  If either is not a true-list, it will
; provoke a translation error.

         (list*
          :CASES
          (cond ((not (true-listp val1)) val1)
                ((not (true-listp val2)) val2)
                (t (union-equal val1 val2)))
          (cddr keyword-alist)))
        (:IN-THEORY

; The value provided to an :IN-THEORY hint can be an arbitrary
; theory-producing form and in general we do not know how to merge
; them!  However, we can handle a few special (and very common) cases.

         (cond ((mergeable-theory-expressionp val2)
                (list*
                 :IN-THEORY
                 (merge-mergeable-theory-expressions val1 val2)
                 (cddr keyword-alist)))
               (t (list*
                   :ERROR
                   (msg "We do not know how to merge the :IN-THEORY ~
                         expression ~x02 with the :IN-THEORY expression ~
                         ~x12.  Sorry!"
                        val1
                        val2
                        nil)
                   (cddr keyword-alist)))))
        (:NONLINEARP

; The value provided to a :NONLINEARP hint is either t or nil.
; Otherwise, a translation error is provoked.  Suppose a hint tells
; you to use nonlinear arithmetic (t) and not to use nonlinear
; arithmetic (nil).  What do you do?  These are unmergable and we
; provoke an error.

         (cond
          ((not (or (eq val1 t) (eq val1 nil)))
           (list* :NONLINEARP val1 (cddr keyword-alist)))
          ((not (or (eq val2 t) (eq val2 nil)))
           (list* :NONLINEARP val2 (cddr keyword-alist)))
          ((eq val1 val2)
           (list* :NONLINEARP val1 (cddr keyword-alist)))
          (t
           (list* :ERROR
                  (msg "It is impossible to merge :NONLINEARP T with ~
                        :NONLINEARP NIL!")
                  (cddr keyword-alist)))))
        (:INDUCT

; The value provided to an :INDUCT hint is nil or t (meaning go
; straight to induction and choose automatically based on the clause)
; or is a term (meaning go straight to induction and choose based on
; the term).  If the value is not a term, it provokes a translation
; error.  The merge of t (or nil) with a term is the term.  The merge
; of two terms is a term containing both, which will lead to a merged
; suggested induction.

         (list* :INDUCT
                (cond

; If either is t or nil, choose the other, which will suggest the
; same induction or provoke the same error.

                 ((or (null val1) (eq val1 t)) val2)
                 ((or (null val2) (eq val2 t)) val1)

; If both are supposed to be terms, we return a term containing both.
                 (t `(cons ,val1 ,val2)))
                (cddr keyword-alist)))
        (:BDD

; The value provided to a :BDD hint is a keyword alist with keys drawn
; from :VARS, :LITERAL, :PROVE, and :BDD-CONSTRUCTORS.  We do not attempt
; to merge such hints unless they are identical.

         (cond
          ((equal val1 val2)
           (list* :BDD val1 (cddr keyword-alist)))
          (t
           (list* :ERROR
                  (msg "It is impossible to merge the two :BDD ~
                        hints:~%~Y02~%and~%~Y12."
                       val1
                       val2
                       nil)
                  (cddr keyword-alist)))))
        (otherwise
         (list* :ERROR
                (msg "The merge-hints book does not know how to ~
                      deal with ~x0 hints!  Sorry."
                     key)
                (cddr keyword-alist))))))
   (t (list* (car keyword-alist)
             (cadr keyword-alist)
             (merge-hint (cddr keyword-alist) key val2 wrld)))))

(defun merge-hints (new-keyword-alist old-keyword-alist wrld)
  (cond
   ((endp old-keyword-alist)
    new-keyword-alist)
   (t (merge-hints (merge-hint new-keyword-alist
                               (car old-keyword-alist)
                               (cadr old-keyword-alist)
                               wrld)
                   (cddr old-keyword-alist)
                   wrld))))

(defmacro add-merge-hint ()
  '(add-custom-keyword-hint
    :merge
    (value
     (merge-hints nil
                  (splice-keyword-alist :merge nil keyword-alist)
                  world))))

; Finally, just a few tests.

(logic)

(local (include-book "std/testing/must-fail" :dir :system))
(local (include-book "std/testing/must-succeed" :dir :system))

(local
 (encapsulate
  ()

  (add-merge-hint)

; This proof should fail but the hint should appear.

  (must-fail
   (er-progn
    (set-inhibit-output-lst '(proof-tree))
    (thm (equal x y)
         :hints
         (("Goal"
           :merge t
           :use car-cons
           :in-theory (enable car-cons)
           :use (:instance cdr-cons (x a)(y b))
           :in-theory (disable cdr-cons)
           )))))

; This proof should fail before the proof starts

  (must-fail
   (er-progn
    (prog2$
     t ; (trace$ prove) ; wrong signature for trace$ after v3-3
     (set-inhibit-output-lst '(proof-tree)))
    (thm (equal x y)
         :hints
         (("Goal"
           :merge t
           :use car-consx
           :in-theory (enable car-cons)
           :use (:instance cdr-cons (x a)(y b))
           :in-theory (disable cdr-cons)
           )))))))
