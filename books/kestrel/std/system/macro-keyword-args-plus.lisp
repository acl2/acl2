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

(define macro-keyword-args+ ((mac symbolp) (wrld plist-worldp))
  :returns (keyword-args symbol-alistp)
  :parents (std/system/macro-queries)
  :short "Enhanced variant of @(tsee macro-keyword-args)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee macro-keyword-args),
    but it is guard-verified
    and includes run-time checks (which should always succeed)
    that allow us to prove the return type theorem and to verify the guards
    without strengthening the guard on @('wrld').
    Furthermore, this utility causes an error (via @(tsee macro-args+))
    if called on a symbol that does not name a macro.")
  (b* ((all-args (macro-args+ mac wrld))
       (args-after-&key (cdr (member-eq '&key all-args)))
       (keyword-args (macro-keyword-args+-aux mac args-after-&key)))
    keyword-args)

  :prepwork

  ((define macro-keyword-args+-aux ((mac symbolp) (args true-listp))
     :returns (keyword-args symbol-alistp)
     :verify-guards :after-returns
     (b* (((when (endp args)) nil)
          (arg (car args))
          ((when (lambda-keywordp arg)) nil)
          ((when (symbolp arg))
           (acons arg nil (macro-keyword-args+-aux mac (cdr args))))
          ((unless (and (consp arg)
                        (symbolp (first arg))
                        (consp (cdr arg))
                        (consp (second arg))
                        (eq (car (second arg)) 'quote)
                        (consp (cdr (second arg)))))
           (raise "Internal error: ~
                   the keyword macro argument ~x0 of ~x1 ~
                   does not have the expected form."
                  arg mac)))
       (acons (first arg)
              (unquote (second arg))
              (macro-keyword-args+-aux mac (cdr args)))))

   (local
    (defthm verify-guards-lemma-1
      (implies (true-listp x)
               (true-listp (member-equal a x)))))

   (local
    (defthm verify-guards-lemma-2
      (implies (true-listp x)
               (true-listp (cdr x)))))))
