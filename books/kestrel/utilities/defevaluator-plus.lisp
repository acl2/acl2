; A nicer interface to defevaluator
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in defevaluator-plus-tests.lisp

(include-book "pack") ; reduce?
(include-book "make-function-calls-on-formals")

;; A nicer interface to defevaluator.  Improvements include:
;; 1. looks up the arities of the functions in the world.
;; 2. auto-generates the name of the -list function that will be mutually recursive with the term evaluator.
;; 3. always uses the :namedp t option to defevaluator, for nicer constraint names
;; 4. automatically generates various theorems
;; 5. generates improved versions of some constraints (currently, just one)

(defun defevaluator+-fn (name fns state)
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp fns))
                  :stobjs state))
  (let* ((list-name (add-suffix-to-fn name "-LIST")))
    `(progn
       ;; The main defevaluator call generated:
       (defevaluator ,name ,list-name
         ,(make-function-calls-on-formals fns (w state))
         :namedp t)

       ;; Extra theorems:

       (defthm ,(add-suffix-to-fn list-name "-OF-APPEND")
         (equal (,list-name (append terms1 terms2) a)
                (append (,list-name terms1 a)
                        (,list-name terms2 a)))
         :hints (("Goal" :in-theory (enable append))))

       (defthm ,(pack$ 'len-of- list-name)
         (equal (len (,list-name terms a))
                (len terms))
         :hints (("Goal" :in-theory (enable append (:I len)))))

       (defthm ,(add-suffix-to-fn list-name "-OF-TRUE-LIST_FIX")
         (equal (,list-name (true-list-fix terms) a)
                (,list-name terms a))
         :hints (("Goal" :in-theory (enable append (:I len)))))

       ;; Improved constraint(s):

       (defthm ,(pack$ name '-of-lambda-better)
         (implies (consp (car x)) ;; no need to assume (consp x) since it's implied by this
                  (equal (,name x a)
                         (,name (caddr (car x))
                                (pairlis$ (cadr (car x))
                                          (,list-name (cdr x) a))))))

       ;; Ours is better:
       (in-theory (disable ,(pack$ name '-of-lambda)))
       )))

;; Example call (defevaluator+ math-and-if-ev binary-+ binary-* if).
;; Takes the name of the evaluator to create, followed by the names of all the
;; functions it should "know" about.
(defmacro defevaluator+ (name &rest fns)
  `(make-event (defevaluator+-fn ',name ',fns state)))
