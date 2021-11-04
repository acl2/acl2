; A variant of make-flag that may be more robust
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(include-book "misc/install-not-normalized" :dir :system)
(include-book "kestrel/clause-processors/simplify-after-using-conjunction" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-list-listp" :dir :system))

(local (in-theory (disable disjoin)))

(defun my-make-flag-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (let* ((clause (first (sublis-var-and-simplify-clause-processor clause))) ; deals with the flag var?
         (clause (first (flatten-literals-clause-processor clause))) ; is this needed?
         ;; todo: maybe call simplify-after-using-conjunction-clause-processor here:
         (clause (first (push-o-p-clause-processor clause)))
         (clauses (simple-subsumption-clause-processor clause))  ;todo: doesn't yet deal with the o-p claims because they appear not as conjuncts
         )
    clauses))

;todo: add :well-formedness proof
(defthm my-make-flag-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (my-make-flag-eval (conjoin-clauses (my-make-flag-clause-processor clause)) a))
           (my-make-flag-eval (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal" :in-theory (e/d ( ;sublis-var-and-simplify-clause-processor
                                   simple-subsumption-clause-processor
                                   FLATTEN-LITERALS-CLAUSE-PROCESSOR
                                   SUBLIS-VAR-AND-SIMPLIFY-CLAUSE-PROCESSOR
                                   PUSH-O-P-CLAUSE-PROCESSOR
                                   )
                                  (DISJOIN-LST)))))


;dup
(defun make-doublets (xs ys)
  (declare (xargs :guard (and (true-listp xs)
                              (true-listp ys))))
  (if (endp xs)
      nil
    (cons (list (first xs) (first ys))
          (make-doublets (rest xs) (rest ys)))))

(verify-termination flag::get-formals)
;(verify-guards flag::get-formals) ;todo: have make-flag just call FORMALS

(defun replace-non-members-with-nil (items items-to-keep)
  (declare (xargs :guard (and (symbol-listp items)
                              (symbol-listp items-to-keep))))
  (if (endp items)
      nil
    (let ((item (first items)))
      (cons (if (member-eq item items-to-keep)
                item
              nil)
            (replace-non-members-with-nil (rest items) items-to-keep)))))

(defun termination-theorem-subst-for-my-make-flag (clique-fns merged-formals flag-function-name wrld)
  (declare (xargs :guard (and (symbol-listp clique-fns)
                              (symbol-listp merged-formals))
                  :verify-guards nil ; because this calls flag::get-formals
                  ))
  (if (endp clique-fns)
      nil
    (let* ((fn (first clique-fns))
           (fn-formals (flag::get-formals fn wrld)))
      (cons
       ;; replaces fn by the equivalent call of the flag function:
       ;; example: (pseudo-termp (lambda (x) (flag-pseudo-termp 'pseudo-termp x nil)))
       `(,fn (lambda ,fn-formals (,flag-function-name ',fn ,@(replace-non-members-with-nil merged-formals fn-formals))))
       (termination-theorem-subst-for-my-make-flag (rest clique-fns) merged-formals flag-function-name wrld)))))

(defund map-install-not-normalized-name (names)
  (declare (xargs :guard (symbol-listp names)))
  (if (endp names)
      nil
    (cons (install-not-normalized-name (first names))
          (map-install-not-normalized-name (rest names)))))

(defun my-make-flag-fn (flag-function-name fn body ruler-extenders wrld)
  (declare (xargs :guard (and (symbolp flag-function-name) ; may be :auto
                              (symbolp fn)
                              )
                  :mode :program))
  (let* ((flag-function-name (if (eq :auto flag-function-name)
                                 ;; create the flag function name from the function name:
                                 (packn (list 'flag- fn)) ;(intern-in-package-of-symbol (concatenate 'string "FLAG-" (symbol-name fn)) fn)
                               flag-function-name))
         ;; This stuff is based on what make-flag does:
         (clique-fns (flag::get-clique-members fn wrld))
         (alist (pairlis$ clique-fns clique-fns))
         (merged-formals (flag::merge-formals alist wrld))
         (termination-theorem-subst (termination-theorem-subst-for-my-make-flag clique-fns merged-formals flag-function-name wrld)))
    `(encapsulate ()
       ;; Install not-normalized bodies, so we can always prove functions are equal to their bodies:
       (local (install-not-normalized ,fn))

       (make-flag ,flag-function-name ;; this is optional for make-flag
                ,fn
                :body ,(if (eq body :auto)
                           (make-doublets clique-fns
                                          (map-install-not-normalized-name clique-fns))
                         body)
                ,@(if (eq :auto ruler-extenders)
                      nil
                    `(:ruler-extenders ,ruler-extenders))
                ;; If the termination theorem mentions the fn or its clique
                ;; members, we need to change it to mention the equivalent call
                ;; of the flag function:
                :hints (("Goal" :use (:instance (:termination-theorem ,fn ,termination-theorem-subst))
                         ;; :in-theory nil ;;too restrictive
                         :in-theory (theory 'minimal-theory) ;;still too restrictive?
                         )
                        ;; todo: consider also handling o-p of if
                        ("goal'" :clause-processor (my-make-flag-clause-processor clause)))))))

;; This is a wrapper around make-flag that attempts to be more robust.  It uses
;; the :termination-theorem of the given function in the :hints supplied to
;; make-flag (to ensure that the proof works without hints).  CAVEAT: Such a
;; proof may be *much* slower than the direct proof done by make-flag.  TODO:
;; Consider how to speed up measure proofs that use existing
;; :termination-theorems.  Matt K suggests using `(:instructions
;; ((:prove-termination ..))) as in
;; kestrel-acl2/transformations/simplify-defun-impl.lisp, but make-flag does
;; not currently accept :instructions.  Once we figure out how to make
;; the proof both fast and robust, consider improving make-flag itself.
(defmacro my-make-flag (fn &key
                           (body ':auto) ;; the :body arg to pass to make-flag
                           (flag-function-name ':auto) ;; to override the default name of the flag-function
                           (ruler-extenders ':auto)
                           )
  `(make-event (my-make-flag-fn ',flag-function-name ',fn ',body ',ruler-extenders (w state))))
