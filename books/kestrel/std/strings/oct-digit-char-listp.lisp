; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/octal" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist oct-digit-char-listp (x)
  :parents (octal)
  :short "Recognize lists of octal digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee oct-digit-char-list*p),
     this requires true list (i.e. @('nil')-terminated.")
   (xdoc::p
    "Since there are functions in @(see std/strings)
     that operate on @(tsee oct-digit-char-list*p),
     we provide a bridge theorem between the two recognizers,
     which we can use to satisfy the guards of those functions."))
  (oct-digit-char-p x)
  :true-listp t
  :elementp-of-nil nil
  ///

  (defthm oct-digit-char-list*p-when-oct-digit-char-listp
    (implies (oct-digit-char-listp x)
             (oct-digit-char-list*p x))
    :hints (("Goal"
             :induct t
             :in-theory (enable oct-digit-char-list*p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection oct-digit-char-listp-results
  :parents (oct-digit-char-listp)
  :short "Theorems about results of @(see std/strings) functions
          that return lists of octal digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Those @(see std/strings) are accompanied by
     theorems that they return @(tsee oct-digit-char-list*p),
     but they in fact return true lists,
     so here we add theorems that they return @(tsee oct-digit-char-listp)."))

  (std::defrule oct-digit-char-listp-of-basic-nat-to-oct-chars
    (oct-digit-char-listp (basic-nat-to-oct-chars nat))
    :induct t
    :enable (basic-nat-to-oct-chars
             oct-digit-char-listp
             digit-to-char
             ifix)
    :prep-books ((include-book "ihs/logops-lemmas" :dir :system)
                 (include-book "arithmetic-3/top" :dir :system)))

  (std::defrule oct-digit-char-listp-of-nat-to-oct-chars-aux
    (implies (oct-digit-char-listp acc)
             (oct-digit-char-listp (nat-to-oct-chars-aux nat acc)))
    :enable nat-to-oct-chars-aux)

  (std::defrule oct-digit-char-listp-of-nat-to-oct-chars
    (oct-digit-char-listp (nat-to-oct-chars nat))
    :enable nat-to-oct-chars))
