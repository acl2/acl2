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

(define macro-keyword-args ((mac symbolp) (wrld plist-worldp))
  :returns (keyword-args "A @(tsee symbol-alistp).")
  :verify-guards nil
  :parents (std/system/macro-queries)
  :short "Keyword arguments of a macro, in order, with their default values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting from the full argument list of the macro,
     first we find @('&key') in the list;
     if not found, we return @('nil') (i.e. no keyword arguments).
     Otherwise, we scan and collect information from the remaining arguments,
     until we reach either the end of the macro argument list
     or a symbol starting with @('&...').")
   (xdoc::p
    "Keyword arguments have one of the forms
     @('name'), @('(name \'default)'), @('(name \'default predicate)'),
     where @('name') is the argument name (a symbol)
     @('default') its default value (quoted),
     and @('predicate') is another symbol.
     When we find a keyword argument,
     we put name and default value as a pair into an alist.")
   (xdoc::p
    "See @(tsee macro-keyword-args) for
     an enhanced variant of this utility."))
  (b* ((all-args (macro-args mac wrld))
       (args-after-&key (cdr (member-eq '&key all-args)))
       (keyword-args (macro-keyword-args-aux args-after-&key)))
    keyword-args)

  :prepwork
  ((define macro-keyword-args-aux ((args true-listp))
     :returns keyword-args ; SYMBOL-ALISTP
     :verify-guards nil
     (b* (((when (endp args)) nil)
          (arg (car args))
          ((when (lambda-keywordp arg)) nil)
          (name (if (atom arg) arg (first arg)))
          (default (if (atom arg) nil (unquote (second arg)))))
       (acons name default (macro-keyword-args-aux (cdr args)))))))
