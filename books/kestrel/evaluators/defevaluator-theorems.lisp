; A tool to prove theorems about evaluators
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/pack" :dir :system)

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
     (include-book "kestrel/alists-light/map-lookup-equal" :dir :system)
     (include-book "kestrel/alists-light/alists-equiv-on" :dir :system)

     (encapsulate ()

       (local (include-book "kestrel/lists-light/union-equal" :dir :system))

       (defthm ,(add-suffix-to-fn eval-list-name "-IFF")
         (iff (,eval-list-name terms alist)
              (consp terms)))

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
                                         (,(add-suffix-to-fn eval-name "-OF-FNCALL-ARGS-BACK"))))))

       (defthm ,(add-suffix-to-fn eval-list-name "-WHEN-SYMBOL-LISTP")
         (implies (and (symbol-listp vars)
                       (not (member-equal nil vars)) ;evaluating nil just gives nil;
                       )
                  (equal (,eval-list-name vars a)
                         (map-lookup-equal vars a)))
         :hints (("Goal" :in-theory (enable
                                     map-lookup-equal
                                     (:i len)
                                     lookup-equal)
                  :induct (len vars))))

       ;; Pushes the evaluation into the alist.
       ;;term may often be a var
       (defthmd ,(add-suffix-to-fn eval-name "-OF-CDR-OF-ASSOC-EQUAL")
         (equal (,eval-name (cdr (assoc-equal term alist)) a)
                ;; evaluates all the terms in the alist wrt A and then looks up the term:
                (cdr (assoc-equal term (pairlis$ (strip-cars alist)
                                                 (,eval-list-name (strip-cdrs alist)
                                                                  a)))))
         :hints (("Goal" :in-theory (enable pairlis$ assoc-equal))))

       ;; The evaluator gives the same result if the alist is changed to one that is
       ;; equivalent for the free vars of the term.
       (defthm-flag-free-vars-in-term
         (defthm ,(pack$ 'equal-of- eval-name '-and- eval-name '-when-alists-equiv-on)
           (implies (and (alists-equiv-on (free-vars-in-term term) alist1 alist2)
                         (pseudo-termp term))
                    (equal (equal (,eval-name term alist1)
                                  (,eval-name term alist2))
                           t))
           :flag free-vars-in-term)
         (defthm ,(pack$ 'equal-of- eval-list-name '-and- eval-list-name '-when-alists-equiv-on)
           (implies (and (alists-equiv-on (free-vars-in-terms terms) alist1 alist2)
                         (pseudo-term-listp terms))
                    (equal (equal (,eval-list-name terms alist1)
                                  (,eval-list-name terms alist2))
                           t))
           :flag free-vars-in-terms)
         :hints (("Goal" :expand (pseudo-termp term)
                  :in-theory (e/d (free-vars-in-terms
                                   ,(add-suffix-to-fn eval-name "-OF-FNCALL-ARGS"))
                                  (,(add-suffix-to-fn eval-name "-OF-FNCALL-ARGS-BACK")))))))))

;; For now, this assumes that defevaluator+ has been called to create the evaluator.
(defmacro defevaluator-theorems (eval-name eval-list-name)
  (defevaluator-theorems-fn eval-name eval-list-name))
