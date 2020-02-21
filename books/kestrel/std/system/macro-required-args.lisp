; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-required-args ((mac symbolp) (wrld plist-worldp))
  :returns (required-args "A @(tsee symbol-listp).")
  :verify-guards nil
  :parents (std/system/macro-queries)
  :short "Required arguments of a macro, in order."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments of a macro form a list that
     optionally starts with @('&whole') followed by another symbol,
     continues with zero or more symbols that do not start with @('&')
     (which are the required arguments)
     and possibly ends with
     a symbol starting with @('&') followed by more things.")
   (xdoc::p
    "After removing @('&whole') and the symbol following it
     (if the list of arguments starts with @('&whole')),
     we collect all the arguments until
     either the end of the list is reached
     or a symbol starting with @('&') is encountered.")
   (xdoc::p
    "See @(tsee macro-required-args+) for
     an enhanced variant of this utility."))
  (b* ((all-args (macro-args mac wrld)))
    (if (endp all-args)
        nil
      (if (eq (car all-args) '&whole)
          (macro-required-args-aux (cddr all-args))
        (macro-required-args-aux all-args))))

  :prepwork
  ((define macro-required-args-aux ((args true-listp))
     :returns (required-args) ; SYMBOL-LISTP
     :verify-guards nil
     (if (endp args)
         nil
       (b* ((arg (car args)))
         (if (lambda-keywordp arg)
             nil
           (cons arg
                 (macro-required-args-aux (cdr args)))))))))
