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
(verify-termination alist-to-doublets) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The following section was written by David L. Rager.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination plausible-dclsp1)
(verify-termination plausible-dclsp)

(verify-termination fetch-dcl-fields2)
(verify-termination fetch-dcl-fields1)
(verify-termination fetch-dcl-fields)
(verify-termination fetch-dcl-field)

(verify-termination strip-keyword-list)

(verify-termination strip-dcls1)
(verify-termination strip-dcls)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
