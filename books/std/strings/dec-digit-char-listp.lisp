; Standard Strings Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/decimal" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration :hooks nil)

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
     we provide a bridge theorem between the two recognizers,
     which we can use to satisfy the guards of those functions.")
   (xdoc::p
    "We also provide a (disabled) theorem to backchain without limit
     from @(tsee character-listp) to this recognizer,
     because the one for @(tsee dec-digit-char-list*p)
     has a backchain limit that doesn't work with some proofs."))
  (dec-digit-char-p x)
  :true-listp t
  :elementp-of-nil nil
  ///

  (defthm dec-digit-char-list*p-when-dec-digit-char-listp
    (implies (dec-digit-char-listp x)
             (dec-digit-char-list*p x))
    :hints (("Goal"
             :induct t
             :in-theory (enable dec-digit-char-list*p))))

  (defthmd character-listp-when-dec-digit-char-listp
    (implies (dec-digit-char-listp x)
             (character-listp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dec-digit-char-listp-results
  :parents (dec-digit-char-listp)
  :short "Theorems about results of @(see std/strings) functions
          that return lists of decimal digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Those @(see std/strings) are accompanied by
     theorems that they return @(tsee dec-digit-char-list*p),
     but they in fact return true lists,
     so here we add theorems that they return @(tsee dec-digit-char-listp)."))

  (std::defrule dec-digit-char-listp-of-basic-nat-to-dec-chars
    (dec-digit-char-listp (basic-nat-to-dec-chars nat))
    :induct t
    :enable (basic-nat-to-dec-chars
             dec-digit-char-listp
             digit-to-char))

  (std::defrule dec-digit-char-listp-of-nat-to-dec-chars-aux
    (implies (dec-digit-char-listp acc)
             (dec-digit-char-listp (nat-to-dec-chars-aux nat acc)))
    :enable nat-to-dec-chars-aux)

  (std::defrule dec-digit-char-listp-of-nat-to-dec-chars
    (dec-digit-char-listp (nat-to-dec-chars nat))
    :enable nat-to-dec-chars))
