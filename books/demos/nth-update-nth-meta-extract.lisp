; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book provides a macro, make-nth-update-nth-meta-stobj, that illustrates
; the use of meta-extract hypotheses in :meta rules.  This macro takes a stobj
; name as an argument and creates a theorem that automatically simplifies terms
; of the form (f (update-g val st)), where f is a stobj accessor and update-g
; is a stobj updater, without expanding their definitions.

; This example is discussed in Section 2.1.2 of the 2017 ACL2 Workshop paper,
; "Meta-extract: Using Existing Facts in Meta-reasoning",
; by Matt Kaufmann and Sol Swords.

(in-package "ACL2")

(defun fn-nth-index (reader formula)

; The given formula is intended to be (meta-extract-formula fn state) for
; suitable fn.

  (declare (xargs :guard t))
  (case-match formula
    (('equal (!reader x)
             ('nth ('quote index) x))
     (and (symbolp x)
          x
          (natp index)
          index))
    (& nil)))

(defun fn-update-nth-index (writer formula)

; Formula is (meta-extract-formula fn state) for suitable fn.

  (declare (xargs :guard t))
  (case-match formula
    (('equal (!writer val x)
             ('update-nth ('quote index) val x))
     (and (symbolp val)
          val
          (symbolp x)
          x
          (not (eq val x))
          (natp index)
          index))
    (& nil)))

(defun nth-update-nth-meta-fn-new-term (term state)

; This function either returns a new term that is provably equal to the input
; term, or it returns nil.  The intention is to return a new term when the
; input term is of the form (r (w val x)), where r and w are functions defined
; to be calls of nth and update-nth, respectively, on explicit natural number
; indices: (r x) = (nth 'i x) and (w v x) = (update-nth 'j v x).  Subroutines
; fn-nth-index and fn-update-nth-index return the indices i and j for such
; calls of r and w, respectively.

  (declare (xargs :stobjs state))
  (case-match term
    ((reader (writer val x))
     (and (not (eq reader 'quote))
          (not (eq writer 'quote))
          (let* ((reader-formula (and (symbolp reader)
                                      (meta-extract-formula reader state)))
                 (i-rd (fn-nth-index reader reader-formula)))
            (and
             i-rd ; the body of reader is (nth 'i-rd ...)
             (let* ((writer-formula (and (symbolp writer)
                                         (meta-extract-formula writer state)))
                    (i-wr (fn-update-nth-index writer writer-formula)))
               (and
                i-wr ; the body of writer is (update-nth 'i-wr ...)
                (if (eql i-rd i-wr)
                    val
                  (list reader x))))))))
    (& nil)))

(defun nth-update-nth-meta-fn (term mfc state)

; This is our metafunction.  It returns the input term unchanged unless it is
; of the form (r (w val x)), where r and w are functions defined to be calls of
; nth and update-nth, respectively, on explicit natural number indices: (r x) =
; (nth 'i x) and (w v x) = (update-nth 'j v x).

  (declare (xargs :stobjs state)
           (ignore mfc))
  (or (nth-update-nth-meta-fn-new-term term state)
      term))

(defevaluator nth-update-nth-ev nth-update-nth-ev-lst
  ((nth n x)
   (update-nth n val x)
   (equal x y)))

(defun meta-extract-alist-rec (formals actuals a)

; This function returns an alist that binds each formal to the value of the
; corresponding actual in the given alist, a.  See meta-extract-alist for
; documentation.

  (cond ((endp formals) nil)
        (t (acons (car formals)
                  (nth-update-nth-ev (car actuals) a)
                  (meta-extract-alist-rec (cdr formals) (cdr actuals) a)))))

(defun meta-extract-alist (term a state)

; The given term is of interest when it has the form (f t1 ... tn), with
; formals (v1 ... vn).  We are also give an alist, a, in which to evaluate that
; call.  We thus return an alist suitable for evaluating (f v1 ... vn), which
; associates each formal vi with the value of actual ti in alist a.

  (declare (xargs :stobjs state :verify-guards nil))
  (let* ((fn (car term))
         (actuals (cdr term))
         (formula (meta-extract-formula fn state)) ; (equal (fn ...) ...)
         (formals (cdr (cadr formula))))
    (meta-extract-alist-rec formals actuals a)))

; Next we wrap an example in a giant local encapsulate.
; It serves as a guide to the macro we develop below.
(local
 (encapsulate
   ()

   (defstobj st
     fld1 fld2 fld3 fld4 fld5 fld6 fld7 fld8 fld9 fld10
     fld11 fld12 fld13 fld14 fld15 fld16 fld17 fld18 fld19 fld20)

   (assert-event
    (equal (nth-update-nth-meta-fn '(fld1 (update-fld2 'abc st))
                                   nil
                                   state)
           '(fld1 st)))

   (assert-event
    (equal (nth-update-nth-meta-fn '(fld2 (update-fld2 'abc st))
                                   nil
                                   state)
           ''abc))

   (defthm nth-update-nth-meta-rule-st
     (implies (and (nth-update-nth-ev ; (f (update-g val st))
                    (meta-extract-global-fact (list :formula (car term)) state)
                    (meta-extract-alist term a state))
                   (nth-update-nth-ev ; (update-g val st)
                    (meta-extract-global-fact (list :formula (car (cadr term)))
                                              state)
                    (meta-extract-alist (cadr term) a state))
                   (nth-update-nth-ev ; (f st) -- note st is (caddr (cadr term))
                    (meta-extract-global-fact (list :formula (car term)) state)
                    (meta-extract-alist (list (car term)
                                              (caddr (cadr term)))
                                        a state)))
              (equal (nth-update-nth-ev term a)
                     (nth-update-nth-ev (nth-update-nth-meta-fn term mfc state) a)))
     :hints (("Goal" :in-theory (enable nth-update-nth-ev-constraint-0)))
     :rule-classes ((:meta :trigger-fns
                           (fld1 fld2 fld3 fld4 fld5 fld6 fld7 fld8 fld9 fld10
                                 fld11 fld12 fld13 fld14 fld15
                                 fld16 fld17 fld18 fld19 fld20))))

   (in-theory
    (disable fld1 fld2 fld3 fld4 fld5
             fld6 fld7 fld8 fld9 fld10
             fld11 fld12 fld13 fld14 fld15
             fld16 fld17 fld18 fld19 fld20
             update-fld1 update-fld2 update-fld3 update-fld4 update-fld5
             update-fld6 update-fld7 update-fld8 update-fld9 update-fld10
             update-fld11 update-fld12 update-fld13 update-fld14 update-fld15
             update-fld16 update-fld17 update-fld18 update-fld19 update-fld20))

   (defthm test1
     (equal (fld3 (update-fld1
                   1
                   (update-fld2
                    2
                    (update-fld3
                     3
                     (update-fld4
                      4
                      (update-fld3
                       5
                       (update-fld6 6 st)))))))
            3))

   )) ; end of local encapsulate

; Now we repeat the lemma above, but this time with a more generic name and
; with empty :rule-classes.  Our macro will use it automatically

(defthm nth-update-nth-meta-level

; A term modified by our metafunction has the form (f (update-g val st)).

  (implies (and (nth-update-nth-ev ; (f (update-g val st))
                 (meta-extract-global-fact (list :formula (car term)) state)
                 (meta-extract-alist term a state))
                (nth-update-nth-ev ; (update-g val st)
                 (meta-extract-global-fact (list :formula (car (cadr term)))
                                           state)
                 (meta-extract-alist (cadr term) a state))
                (nth-update-nth-ev ; (f st) -- note st is (caddr (cadr term))
                 (meta-extract-global-fact (list :formula (car term)) state)
                 (meta-extract-alist (list (car term)
                                           (caddr (cadr term)))
                                     a state)))
   (equal (nth-update-nth-ev term a)
          (nth-update-nth-ev (nth-update-nth-meta-fn term mfc state) a)))
  :hints (("Goal" :in-theory (enable nth-update-nth-ev-constraint-0)))
  :rule-classes nil)

; Next we develop the function stobj-accessors-and-updaters, which returns a
; list of all stobj accessors and updaters for a given stobj.

(defun stobj-accessor-or-updater-p (symbol wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (and (symbolp symbol)
       (function-symbolp symbol wrld)
       (let ((body (getpropc symbol 'unnormalized-body nil wrld)))
         (and (nvariablep body)
              (member-eq (ffn-symb body)
                         '(nth update-nth))))))

(defun stobj-accessors-and-updaters-rec (lst wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (cond ((atom lst) nil)
        ((stobj-accessor-or-updater-p (car lst) wrld)
         (cons (car lst)
               (stobj-accessors-and-updaters-rec (cdr lst) wrld)))
        (t (stobj-accessors-and-updaters-rec (cdr lst) wrld))))

(defun stobj-accessors-and-updaters (s wrld)

; Return a list of all stobj accessors and updaters for a given stobj, s.

  (declare (xargs :guard (and (symbolp s)
                              (plist-worldp wrld))))
  (let ((prop (getpropc s 'stobj nil wrld)))
    (cond ((not (weak-stobj-property-p prop)) ; i.e., (null prop)
           (er hard? 'stobj-accessors-and-updaters
               "The symbol ~x0 is expected to be a stobj, but it is not."
               s))
          (t (stobj-accessors-and-updaters-rec
              (access stobj-property prop :names)
              wrld)))))

(defmacro make-nth-update-nth-meta-stobj (stobj-name)

; This macro takes the name of a stobj and does two things: it disables all of
; the stobj's accessors and updaters, and it proves a metatheorem that
; simplifies every term of the form (f (update-g val stobj-name)), where f and
; update-g are an accessor and updater, respectively, for the given stobj name.

  `(make-event
    (let ((fns (and (symbolp ',stobj-name)
                    (stobj-accessors-and-updaters ',stobj-name (w state))))
          (theorem-name
           (packn (list 'nth-update-nth-meta-rule- ',stobj-name))))
      (cond
       ((null fns)
        (er soft 'make-nth-update-nth-meta-stobj
            "It appears that ~x0 is not the name of a stobj."
            ',stobj-name))
       (t
        (value
         `(progn
            (in-theory (disable ,@fns))
            (defthm ,theorem-name
              (implies
               (and (nth-update-nth-ev
                     (meta-extract-global-fact (list :formula (car term))
                                               state)
                     (meta-extract-alist term a state))
                    (nth-update-nth-ev
                     (meta-extract-global-fact (list :formula
                                                     (car (cadr term)))
                                               state)
                     (meta-extract-alist (cadr term) a state))
                    (nth-update-nth-ev
                     (meta-extract-global-fact (list :formula (car term))
                                               state)
                     (meta-extract-alist (list (car term)
                                               (caddr (cadr term)))
                                         a state)))
               (equal (nth-update-nth-ev term a)
                      (nth-update-nth-ev
                       (nth-update-nth-meta-fn term mfc state) a)))
              :hints (("Goal" :by nth-update-nth-meta-level))
              :rule-classes ((:meta :trigger-fns ,fns))))))))))

; Finally, we test our macro.

(local
 (encapsulate
   ()

   (defstobj st$
     fld$1 fld$2 fld$3 fld$4 fld$5 fld$6 fld$7 fld$8 fld$9 fld$10)

   (make-nth-update-nth-meta-stobj st$)

   (defthm test2
     (equal (fld$3 (update-fld$1
                    1
                    (update-fld$2
                     2
                     (update-fld$3
                      3
                      (update-fld$4
                       4
                       (update-fld$3
                        5
                        (update-fld$6 6 st$)))))))
            3))
   )) ; end of local encapsulate
