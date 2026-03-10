; Standard Strings Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/binary" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration :hooks nil)

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
     we provide a bridge theorem between the two recognizers,
     which we can use to satisfy the guards of those functions.")
   (xdoc::p
    "We also provide a (disabled) theorem to backchain without limit
     from @(tsee character-listp) to this recognizer."))
  (bin-digit-char-p x)
  :true-listp t
  :elementp-of-nil nil
  ///

  (defthm bin-digit-char-list*p-when-bin-digit-char-listp
    (implies (bin-digit-char-listp x)
             (bin-digit-char-list*p x))
    :hints (("Goal"
             :induct t
             :in-theory (enable bin-digit-char-list*p))))

  (defthmd character-listp-when-bin-digit-char-listp
    (implies (bin-digit-char-listp x)
             (character-listp x))
    :hints (("Goal" :induct t :in-theory (enable character-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bin-digit-char-listp-results
  :parents (bin-digit-char-listp)
  :short "Theorems about results of @(see std/strings) functions
          that return lists of binary digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Those @(see std/strings) are accompanied by
     theorems that they return @(tsee bin-digit-char-list*p),
     but they in fact return true lists,
     so here we add theorems that they return @(tsee bin-digit-char-listp)."))

  (acl2::defrule bin-digit-char-listp-of-basic-nat-to-bin-chars
    (bin-digit-char-listp (basic-nat-to-bin-chars nat))
    :induct t
    :enable (basic-nat-to-bin-chars
             bin-digit-char-listp
             digit-to-char))

  (acl2::defrule bin-digit-char-listp-of-nat-to-bin-chars-aux
    (implies (bin-digit-char-listp acc)
             (bin-digit-char-listp (nat-to-bin-chars-aux nat acc)))
    :enable nat-to-bin-chars-aux)

  (acl2::defrule bin-digit-char-listp-of-nat-to-bin-chars
    (bin-digit-char-listp (nat-to-bin-chars nat))
    :enable nat-to-bin-chars))
