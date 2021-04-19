; Copyright (C) 2014, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book was originally created by David Rager (April, 2012) to serve as a
; place to verify the termination and guards of ACL2 system functions.  This
; book is included in system/top.lisp; either might usefully be included when
; reasoning about system functions.

; Note that calling verify-termination also verifies the guards of any function
; that has a guard specified.  In the event that there is no guard specified,
; then one must also call verify-guards to verify that the implicit guard of
; "t" is strong enough.  See :doc verify-termination for further details.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The following section was written by Matt Kaufmann.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination collect-by-position) ; and guards

; Copied exactly (11/18/2015) from ACL2 source file axioms.lisp, towards guard
; verification for make-lambda-application:
(local
 (encapsulate
  ()

; We wish to prove symbol-listp-all-vars1, below, so that we can verify the
; guards on all-vars1.  But it is in a mutually recursive clique.  Our strategy
; is simple: (1) define the flagged version of the clique, (2) prove that it is
; equal to the given pair of official functions, (3) prove that it has the
; desired property and (4) then obtain the desired property of the official
; function by instantiation of the theorem proved in step 3, using the theorem
; proved in step 2 to rewrite the flagged flagged calls in that instance to the
; official ones.

; Note: It would probably be better to make all-vars1/all-vars1-lst local,
; since it's really not of any interest outside the guard verification of
; all-vars1.  However, since we are passing through this file more than once,
; that does not seem to be an option.

  (local
   (defun all-vars1/all-vars1-lst (flg lst ans)
     (if (eq flg 'all-vars1)
         (cond ((variablep lst) (add-to-set-eq lst ans))
               ((fquotep lst) ans)
               (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst) ans)))
         (cond ((endp lst) ans)
               (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst)
                                           (all-vars1/all-vars1-lst 'all-vars1 (car lst) ans)))))))

  (local
   (defthm step-1-lemma
     (equal (all-vars1/all-vars1-lst flg lst ans)
            (if (equal flg 'all-vars1) (all-vars1 lst ans) (all-vars1-lst lst ans)))))

  (local
   (defthm step-2-lemma
     (implies (and (symbol-listp ans)
                   (if (equal flg 'all-vars1)
                       (pseudo-termp lst)
                       (pseudo-term-listp lst)))
              (symbol-listp (all-vars1/all-vars1-lst flg lst ans)))))

  (defthm symbol-listp-all-vars1
    (implies (and (symbol-listp ans)
                  (pseudo-termp lst))
             (symbol-listp (all-vars1 lst ans)))
    :hints (("Goal" :use (:instance step-2-lemma (flg 'all-vars1)))))))

(verify-termination make-lambda-application)
(verify-termination >=-len) ; and guards
(verify-termination all->=-len) ; and guards
(verify-termination strip-cadrs) ; and guards
(verify-termination strip-caddrs) ; and guards
(verify-termination alist-to-doublets) ; and guards
(verify-termination ffnnamep) ; and guards
(verify-termination world-evisceration-alist) ; and guards
(verify-termination abbrev-evisc-tuple) ; and guards
(verify-termination override-hints) ; and guards
(verify-termination stobjp) ; and guards
(verify-termination newline) ; and guards
(verify-termination lambda-subtermp) ; and guards
(verify-termination ens) ; and guards
(local (defthm car-assoc-equal-cdr-type
         (implies (alistp x)
                  (or (consp (assoc-equal-cdr key x))
                      (equal (assoc-equal-cdr key x) nil)))
         :rule-classes :type-prescription))
(verify-termination runep) ; and guards
(verify-termination clean-brr-stack1) ; and guards
(verify-termination clean-brr-stack) ; and guards
(verify-termination deref-macro-name) ; and guards
(verify-termination write-for-read) ; and guards
(verify-termination fnume) ; and guards
(verify-termination translate-abbrev-rune) ; and guards
(verify-termination logical-namep) ; and guards
(verify-termination er-cmp-fn) ; and guards
(verify-termination string-prefixp-1) ; and guards
(verify-termination string-prefixp) ; and guards
(verify-termination relativize-book-path) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The following section was written by Matt Kaufmann.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination enabled-structure-p) ; and guards

(verify-termination enabled-numep) ; and guards

; Start guard proof for enabled-runep

(defthm enabled-runep-guard-helper-1
  (implies (and (assoc-equal-cdr r x)
                (nat-alistp x))
           (or (natp (car (assoc-equal-cdr r x)))
               (equal (car (assoc-equal-cdr r x)) nil)))
  :rule-classes :type-prescription)

(verify-termination enabled-runep) ; and guards

(verify-termination disabledp-fn-lst) ; and guards

; Start guard proof for disabledp-fn

(defthm symbolp-deref-macro-name
  (implies (and (symbolp name)
                (symbol-alistp macro-aliases)
                (r-symbol-alistp macro-aliases))
           (symbolp (deref-macro-name name macro-aliases))))

(verify-termination ; and guards
  (disabledp-fn (declare (xargs :guard-hints
                                (("Goal"
                                  :in-theory (disable deref-macro-name)
                                  :do-not-induct t))))))

; And now a slew of easy ones:

(verify-termination def-body) ; and guards
(verify-termination access-command-tuple-number) ; and guards
(verify-termination collect-non-x) ; and guards
(verify-termination
  (silent-error (declare (xargs :verify-guards t)))) ; and guards
(verify-termination saved-output-token-p) ; and guards
(verify-termination push-io-record) ; and guards
(verify-termination scan-to-cltl-command) ; and guards
