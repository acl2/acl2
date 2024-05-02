; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/binary" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist bin-digit-char-listp (x)
  :parents (binary)
  :short "Recognize lists of binary digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee bin-digit-char-list*p),
     this requires true list (i.e. @('nil')-terminated.")
   (xdoc::p
    "Since there are functions in @(see std/strings)
     that operate on @(tsee bin-digit-char-list*p),
     we provide a bridge theorem between the two recognizers."))
  (bin-digit-char-p x)
  :true-listp t
  :elementp-of-nil nil
  ///

  (defthm bin-digit-char-list*p-when-bin-digit-char-listp
    (implies (bin-digit-char-listp x)
             (bin-digit-char-list*p x))
    :hints (("Goal"
             :induct t
             :in-theory (enable str::bin-digit-char-list*p)))))
