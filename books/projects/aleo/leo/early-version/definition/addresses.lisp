; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/lcletter-digit-chars" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/bitcoin/bech32" :dir :system)
(in-theory (enable unsigned-byte-p)) ; bech32 uses bv which disables unsigned-byte-p

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ addresses
  :parents (abstract-syntax)
  :short "Leo addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Leo, an address consists of 63 ASCII characters:
     the five characters `@('aleo1')',
     followed by 58 lowercase letters and digits.")
   (xdoc::p
    "The address should conform to Bech32 or Bech32m; see subtopic."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define address-chars-p ((chars character-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of characters forms a Leo address."
  (b* ((chars (str::character-list-fix chars)))
    (and (= (len chars) 63)
         (equal (take 5 chars) (str::explode "aleo1"))
         (str::lcletter/digit-charlist-p (nthcdr 5 chars))))
  :prepwork
  ((local (include-book "std/typed-lists/character-listp" :dir :system)))
  ///
  (assert-event (= (+ 5 58) 63)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define address-string-p ((string stringp))
  :returns (yes/no booleanp)
  :short "Check if a string forms a Leo address."
  (address-chars-p (str::explode string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod address
  :short "Fixtype of Leo addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "We wrap the string into a one-component product type
     for better encapsulation and abstraction."))
  ((name
    string
    :reqfix
    (if (address-string-p name)
        name
      "aleo1oooooooooooooooooooooooooooooooooooooooooooooooooooooooooo")))
  :require (address-string-p name)
  :tag :address
  :pred addressp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Also check Bech32 / Bech32m validity using address-valid-p.

(fty::deflist address-list
  :short "Fixtype of lists of Leo addresses."
  :elt-type address
  :true-listp t
  :elementp-of-nil nil
  :pred address-listp)

(define address-valid-p ((address addressp))
  :returns (y/n booleanp)
  (let ((addr-string (address->name address)))
    (and ;; Aleo-specific address syntax spec:
         (address-string-p addr-string)
         ;; Bech-32/-32m checksum check:
         (bitcoin::valid-bech32-or-bech32m addr-string))))

(define all-addresses-valid? ((addresses address-listp))
  :returns (y/n booleanp)
  (if (endp addresses)
      t
    (and (address-valid-p (first addresses))
         (all-addresses-valid? (rest addresses)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Make sure all addresses in an AST are valid.
; Note it can take any argument.

(define find-addresses (ast-node)
  :returns (addresses address-listp)
  (b* (((unless (consp ast-node))
        nil)
       ((when (reserrp ast-node))
        nil)
       ((when (addressp ast-node))
        (list ast-node))
       (first-item (car ast-node))
       (first-item-addresses (find-addresses first-item))
       (rest-items (cdr ast-node))
       (rest-item-addresses (find-addresses rest-items)))
    (append first-item-addresses rest-item-addresses)))

(define ast-addresses-valid? (AST)
  :returns (y/n booleanp)
  (all-addresses-valid? (find-addresses AST)))
