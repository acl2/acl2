; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/decimal" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist dec-digit-char-listp (x)
  :parents (decimal)
  :short "Recognize lists of decimal digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee dec-digit-char-list*p),
     this requires true list (i.e. @('nil')-terminated.")
   (xdoc::p
    "Since there are functions in @(see std/strings)
     that operate on @(tsee dec-digit-char-list*p),
     we provide a bridge theorem between the two recognizers."))
  (dec-digit-char-p x)
  :true-listp t
  :elementp-of-nil nil
  ///

  (defthm dec-digit-char-list*p-when-dec-digit-char-listp
    (implies (dec-digit-char-listp x)
             (dec-digit-char-list*p x))
    :hints (("Goal"
             :induct t
             :in-theory (enable str::dec-digit-char-list*p)))))
