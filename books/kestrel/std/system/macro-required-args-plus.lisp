; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "macro-args-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-required-args+ ((mac symbolp) (wrld plist-worldp))
  :returns (required-args symbol-listp)
  :parents (std/system/macro-queries)
  :short "Enhanced variant of @(tsee macro-required-args)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee macro-required-args),
    but it is guard-verified
    and includes run-time checks (which should always succeed)
    that allows us to prove the return type theorem and to verify guards
    without strengthening the guard on @('wrld').
    Furthermore, this utility causes an error (via @(tsee macro-args+))
    if called on a symbol that does not name a macro.")
  (b* ((all-args (macro-args+ mac wrld)))
    (if (endp all-args)
        nil
      (if (eq (car all-args) '&whole)
          (macro-required-args+-aux mac (cddr all-args))
        (macro-required-args+-aux mac all-args))))

  :prepwork
  ((define macro-required-args+-aux ((mac symbolp) (args true-listp))
     :returns (required-args symbol-listp)
     (if (endp args)
         nil
       (b* ((arg (car args)))
         (if (lambda-keywordp arg)
             nil
           (if (symbolp arg)
               (cons arg (macro-required-args+-aux mac (cdr args)))
             (raise "Internal error: ~
                     the required macro argument ~x0 of ~x1 is not a symbol."
                    arg mac))))))))
