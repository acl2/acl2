#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "defdoc")

(defun event-sequence (args)
  (if args `(encapsulate
		()
	      ,@args)
    `(progn)))

;; ===================================================================
;;
;; \#if preprocessor macro
;;
;; ===================================================================

(defmacro \#if (p &rest args)
  `(make-event
    (event-sequence (if ,p ',args nil))))

(def::doc \#if

  :section \#if

  :one-liner "A C-preprocessor-like macro for conditional events"

  :details (docstring
"
  \\#if is a C-preprocessor-like macro that allows a sequence of 
embedded event forms to be made conditional on state.

  (\\#if (equal (@ acl2-version) \"ACL2 Version 3.3\")

    (defun test1 (x) x)
    (defthm test-equal
      (equal (test x) x))

   )

  The first argument to \\#if is a predicate that is evaluated
in the current state.  If the predicate evaluates to true, the
remaining forms are submitted to ACL2.  If not, the remaining
forms are skipped.  \\if events can be nested.

  "(docref"\\#if-else")"
  "(docref"\\#cond")"

"))

;; ===================================================================

(local
 (\#if (@ acl2-version) (defun test1 (x) x)))

(local
 (\#if (not (@ acl2-version)) (defun test2 (x) x)))

;; ===================================================================
;;
;; \#if-else preprocessor macro
;;
;; ===================================================================

(defmacro \#if-else (p e1 e2)
  `(make-event
    (event-sequence (if ,p '(,e1) '(,e2)))))

(def::doc \#if-else

  :section \#if-else

  :one-liner "A C-preprocessor-like macro for alternate conditional events"

  :details (docstring
"
  \\#if-else is a C-preprocessor-like macro that alternates
between two different embedded event forms depending on the
result of evaluating the condition.

  (\#if-else (equal (@ acl2-version) \"ACL2 Version 3.3\")

    (defun test1 (x) (1- x))

    (defun test1 (x) (1+ x))

   )

  The first argument to \\#if-else is a predicate that is evaluated
in the current state.  If the predicate evaluates to true, the second
argument to if-else will be submitted to ACL2.  If the predicate
evaluates to false, the third argument will be submitted. \\#if-else 
events can be nested.

  "(docref"\\#if")"
  "(docref"\\#cond")"

"))

;; ===================================================================

(defun cond-to-if (cond)
  (if (consp cond)
      `(if ,(caar cond) '(,(cadar cond))
	 ,(cond-to-if (cdr cond)))
    nil))

(defun make-cond-event (cond-form)
  `(make-event
    (event-sequence ,(cond-to-if cond-form))))

;; ===================================================================
;;
;; \#cond preprocessor macro
;;
;; ===================================================================

(defmacro \#cond (&rest args)
  (make-cond-event args))

(def::doc \#cond

  :section \#cond

  :one-liner "A C-preprocessor-like macro for alternate conditional events"

  :details (docstring
"
  \\#cond is a C-preprocessor-like macro that selects zero
or one event among a possible sequence of events based upon
the result of evaluating the condition associated with the
event.

  (\\#cond
   ((@ test3) (defun test3 (x) x))
   ((@ test4) (defun test4 (x) x))
   ((@ test5) (defun test5 (x) x))
  )

  The \\#cond macro accepts a sequence of terms in cond form.
Each predicate of the cond form is evaluated in sequence.  If a
predicate evaluates to true, the term associated with that 
predicate will be submitted to ACL2.  If no predicate evalutes
to true, the event is a no-op.

  "(docref"\\#if")"
  "(docref"\\#if-else")"

"))

;; ===================================================================

(local
 (\#cond
  ((equal (@ acl2-version) "1") (defun test3 (x) x))
  ((equal (@ acl2-version) "2") (defun test4 (x) x))
  (t                            (defun test5 (x) x))
  ))
