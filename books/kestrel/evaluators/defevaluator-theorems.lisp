; A tool to prove theorems about evaluators
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Assumes defevaluator-plus has been run (for now -- perhaps move the theorems
;; from that to this, or call this from that?)

(defun defevaluator-theorems-fn (eval-name eval-list-name)
  (declare (xargs :guard (and (symbolp eval-name)
                              (symbolp eval-list-name))
                  ;;                  :stobjs state
                  ))
  `(progn
     ;; Needed to state the theorems below:
     (include-book "kestrel/terms-light/free-vars-in-term" :dir :system)

     (encapsulate ()

       (local (include-book "kestrel/lists-light/union-equal" :dir :system))

       (defthm-flag-free-vars-in-term
         ;; Adding a pair to the alist has no effect if the key is not one of the free vars in the term.
         (defthm ,(add-suffix-to-fn eval-name "-OF-CONS-IRREL")
           (implies (and (not (member-equal (car pair) (free-vars-in-term term)))
                         (pseudo-termp term))
                    (equal (,eval-name term (cons pair a))
                           (,eval-name term a)))
           :flag free-vars-in-term)
         (defthm ,(add-suffix-to-fn eval-list-name "-OF-CONS-IRREL")
           (implies (and (not (member-equal (car pair) (free-vars-in-terms terms)))
                         (pseudo-term-listp terms))
                    (equal (,eval-list-name terms (cons pair a))
                           (,eval-list-name terms a)))
           :flag free-vars-in-terms)
         :hints (("Goal" :in-theory (e/d (,(add-suffix-to-fn eval-name "-OF-FNCALL-ARGS")
                                          free-vars-in-terms)
                                         (,(add-suffix-to-fn eval-name "-OF-FNCALL-ARGS-BACK"))))))

       (defthm-flag-free-vars-in-term
         ;; Binding a var to the value it already has in the alist has no effect
         (defthm ,(add-suffix-to-fn eval-name "-OF-CONS-IRREL2")
           (implies (and (equal val (cdr (assoc-equal var a))) ; so binding var to val has no effect
                         (pseudo-termp term))
                    (equal (,eval-name term (cons (cons var val) a))
                           (,eval-name term a)))
           :flag free-vars-in-term)
         (defthm ,(add-suffix-to-fn eval-list-name "-OF-CONS-IRREL2")
           (implies (and (equal val (cdr (assoc-equal var a))) ; so binding var to val has no effect
                         (pseudo-term-listp terms))
                    (equal (,eval-list-name terms (cons (cons var val) a))
                           (,eval-list-name terms a)))
           :flag free-vars-in-terms)
         :hints (("Goal" :in-theory (e/d (,(add-suffix-to-fn eval-name "-OF-FNCALL-ARGS"))
                                         (,(add-suffix-to-fn eval-name "-OF-FNCALL-ARGS-BACK")))))))))

;; For now, this assumes that defevaluator+ has been called to create the evaluator.
(defmacro defevaluator-theorems (eval-name eval-list-name)
  (defevaluator-theorems-fn eval-name eval-list-name))
