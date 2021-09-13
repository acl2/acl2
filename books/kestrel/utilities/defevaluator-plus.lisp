; A nicer interface to defevaluator
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pack") ; reduce?

;; A nicer interface to defevaluator.  Improvements include:
;; 1. looks up the arities of the functions in the world.
;; 2. auto-generates the name of the -list function that will be mutually recursive with the term evaluator.
;; 3. always uses the :namedp t option to defevaluator
;; 4. automatically generates various theorems

(defun make-function-call-on-formals (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  `(,fn ,@(formals fn wrld)))

(defun make-function-calls-on-formals (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (cons (make-function-call-on-formals (first fns) wrld)
          (make-function-calls-on-formals (rest fns) wrld))))

(defun defevaluator+-fn (name fns state)
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp fns))
                  :stobjs state))
  (let* ((list-name (add-suffix-to-fn name "-LIST")))
    `(progn
       (defevaluator ,name ,list-name
         ,(make-function-calls-on-formals fns (w state))
         :namedp t)

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
         :hints (("Goal" :in-theory (enable append (:I len))))))))

(defmacro defevaluator+ (name &rest fns)
  `(make-event (defevaluator+-fn ',name ',fns state)))
