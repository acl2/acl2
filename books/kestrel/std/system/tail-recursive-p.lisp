; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "irecursivep")
(include-book "ubody-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tail-recursive-p ((fn (and (symbolp fn)
                                   (= 1 (len (irecursivep fn wrld)))))
                          (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries)
  :short "Check if a singly recursive function is tail-recursive."
  :long
  (xdoc::topstring
   (xdoc::p
    "A singly recursive function is tail-recursive if
     each of its recursive calls are the last action taken by the function
     on that execution path.
     We recursively examine the body of the function
     to see whether that is the case.")
   (xdoc::p
    "Variables and quoted constants cannot contain recursive calls
     and thus pass the check.
     Calls of @(tsee if) are non-strict, and thus they are treated specially:
     they pass the check if
     their `then' and `else' branches individually pass the check
     (since just one of these branches is executed each time)
     and their test has no recursive calls
     (because after the test a branch has to be evaluated,
     so evaluating the test is never the function's last action).")
   (xdoc::p
    "Calls of other named functions pass the check
     if the arguments do not contain recursive calls.
     This applies both when the called function is @('fn')
     (in which case it is a tail-recursive call),
     and when the called function is not @('fn')
     (in which case it is not a recursive call).")
   (xdoc::p
    "Calls of lambda expressions pass the check
     if the arguments do not contain recursive calls
     and the body of the lambda expression passes the check.
     The body of the lambda expression is the last thing
     to be evaluated in the call."))
  (tail-recursive-p-aux fn (ubody+ fn wrld))

  :prepwork
  ((define tail-recursive-p-aux ((fn symbolp) (term pseudo-termp))
     :returns (yes/no booleanp)
     (b* (((when (variablep term)) t)
          ((when (fquotep term)) t)
          ((when (eq (ffn-symb term) 'if))
           (and (not (ffnnamep fn (fargn term 1)))
                (tail-recursive-p-aux fn (fargn term 2))
                (tail-recursive-p-aux fn (fargn term 3))))
          ((when (ffnnamep-lst fn (fargs term))) nil)
          ((when (symbolp (ffn-symb term))) t))
       (tail-recursive-p-aux fn (lambda-body (ffn-symb term)))))))
