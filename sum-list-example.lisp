; ACL2 Version 6.0 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2012, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; This file illustrates Version 1.8 as of Nov 2, 1994.  We start in
; the default :logic mode with guard checking on, i.e. ,the prompt
; is ACL2 !>.

(defun sum-list (x)
  (declare (xargs :guard (integer-listp x) :verify-guards nil))
  (cond ((endp x) 0)
        (t (+ (car x) (sum-list (cdr x))))))

; Note that we disable guard verification above.  We can now evaluate
; calls of this function.  

(sum-list '(1 2 3 4))   ; this call succeeds.

(sum-list '(1 2 abc 3 4 . xyz))  ; this one fails because of a guard violation.

; It is surprising, perhaps, to note that the violation is on the guard of
; endp, not the guard of sum-list.  Because we have not yet verified the guards
; of sum-list we only have a logical definition.  But because endp has had its
; guards verified, we can run either the Common Lisp or the logical version of
; it and with guard checking on we are running the Common Lisp one.
; So we switch to no guard checking...

:set-guard-checking nil

(sum-list '(1 2 abc 3 4 . xyz))  ; Now this call succeeds.

; We prove an important theorem about sum-list.  Note that we do not have
; to restrict it with any hypotheses.

(defthm sum-list-append
  (equal (sum-list (append a b))
         (+ (sum-list a) (sum-list b))))

; Ok, we now move on to the task of showing these results hold in Common Lisp.

(verify-guards sum-list)  ; this is just like it was in Version 1.7

:comp sum-list            ; this compiles both the Common Lisp version of
                          ; sum-list and the logical (Nqthm-like ``*1*'') 
                          ; version
; Now we exit the loop and install a trace on the Common Lisp program 
; sum-list, and then reenter the loop.

:q
(trace sum-list)
(lp)

; Recall that guard checking is still off.  The following call violates the
; guards of sum-list, but since guard checking is off, we get the logical
; answer.  It is done without running the Common Lisp version of sum-list.
; That is, no trace output is evident.

(sum-list '(1 2 abc 3 4))  ; succeeds (but runs the compiled *1* function)

; But the following call prints a lot of trace output.  Because the
; guard is satisfied and we can run sum-list directly in Common Lisp.

(sum-list '(1 2 3 4))      ; succeeds (running compiled sum-list)

; Next we turn our attention to verifying that sum-list-append
; holds in Common Lisp.  If we try

(verify-guards sum-list-append)

; it fails.  Among other things, the guard for append is violated since we know
; nothing about a.  We need a version of the theorem with some hypotheses
; restricting the variables.  We state the theorem with IF so that the
; hypotheses govern the conclusion.  (At the moment in Version 1.8 IMPLIES is a
; function, not a macro, and hence in (IMPLIES p q), q is not governed by p.)

(defthm common-lisp-version-of-sum-list-append
  (if (and (integer-listp a)
           (integer-listp b))
      (= (sum-list (append a b))
         (+ (sum-list a) (sum-list b)))
      t)
  :rule-classes nil)

; The theorem above is trivially proved, because its conclusion is true
; without the hypotheses.  But we can now verify that its guards hold.

(verify-guards common-lisp-version-of-sum-list-append)

; So that expression will all evaluate to non-nil without error in
; Common Lisp (except for resource errors).

