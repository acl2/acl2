; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "tools/rewrite-dollar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-solution-acl2-rewriter$ ((matrix pseudo-termp)
                                           (?f symbolp)
                                           (x1...xn symbol-listp)
                                           (method-rules symbol-listp)
                                           ctx
                                           state)
  :returns (mv erp
               (result "A tuple @('(rewritten-term f-body used-rules)')
                        satisfying
                        @('(typed-tuplep pseudo-termp
                                         pseudo-termp
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Attempt to generate a solution,
          i.e. to solve @('old') for @('?f') using the ACL2 rewriter."
  (b* (((er (list term used))
        (rewrite$ matrix :ctx ctx :in-theory `(enable ,@method-rules)))
       ((when (and (nvariablep term)
                   (not (fquotep term))
                   (eq (ffn-symb term) 'equal)
                   (= (len (fargs term)) 2)
                   (equal (fargn term 1) (fcons-term ?f x1...xn))))
        (value (list term (fargn term 2) used)))
       ((when (equal term *t*))
        (value (list term *nil* used))))
    (er-soft+ ctx t nil
              "The ACL2 rewriter has rewritten the term ~X10 to ~X20, ~
               which does not determine a solution for ~x3 ~
               according to the user documentation. ~
               This transformation may be extended in the future ~
               to determine solutions in more cases than now."
              nil matrix term ?f)))
