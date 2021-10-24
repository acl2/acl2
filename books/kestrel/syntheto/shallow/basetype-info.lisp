; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Utilities for dealing with ACL2 base type names, recognizer predicates,
;; fixers, and equivalence functions.

;; ACL2 base type names are the irregular verbs of FTY.
;; See the table here:
;; https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=FTY____BASETYPES
;; One additional complication not covered in the table is that the
;; symbol-package-name of these symbols is sometimes the "ACL2" package,
;; but sometimes the "COMMON-LISP" package.  So you must be careful not to
;; make assumptions about the home package.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/util/defines" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; base type name information

(defconst *nonstandard-base-type-names*
  #!acl2 '(int true any bool))

(defconst *standard-base-type-names*
  #!acl2 '(bit nat rational acl2-number true-list string symbol pos
               character maybe-nat maybe-pos maybe-bit maybe-integer))

(define base-type-name-p ((sym symbolp))
  (or (member sym *nonstandard-base-type-names*)
      (member sym *standard-base-type-names*)))

;; Map strings to base type names
;; Unfortunately, this is how you use loop$ to make a defconst value.
(make-event `(defconst *base-type-name-strings*
               ',(loop$ for sym in (append *nonstandard-base-type-names*
                                           *standard-base-type-names*)
                        collect (symbol-name sym))))

(define base-type-name-string-p ((str stringp))
  (member-equal str *base-type-name-strings*))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; base type to recognizer predicate

;; Determine predicate from type name by simply appending "p" in most cases.
;; This is a hack for expediency.
;; There must be a more flexible way based on querying the world but that
;; might need us to make variants of the fty::def.. functions.

;; It maps base type names to recognizers from the table
;; in xdoc basetypes.
;; Only the nonstandard names are listed here.
;; All the other base types simply have "p" appended.
;; All the user-defined types will have "-p" appended.
(define nonstandard-base-type-to-pred ((base-type symbolp))
  :returns (pred symbolp)
  (cond ((eq base-type 'acl2::int) 'acl2::integerp)
        ((eq base-type 'acl2::true) 'acl2::true-p)
        ((eq base-type 'acl2::any) 'acl2::any-p)
        ((eq base-type 'acl2::bool) 'acl2::booleanp)
        (t (er hard? 'top-level
               "nonstandard-base-type-to-pred called on an invalid base type"))))

;; Most of the base type recognizers have "P" appended to the type name.
(define base-type-name-to-pred ((type-name symbolp))
  :returns (pred symbolp)
  (if (member type-name *nonstandard-base-type-names*)
      (nonstandard-base-type-to-pred type-name)
    (if (member type-name *standard-base-type-names*)
        (add-suffix-to-fn type-name "P")
        ;; Note: the preceding call is equivalent here to
        ;;(intern (string-append (symbol-name type-name) "P") "ACL2")
      (er hard? 'top-level "Unknown base type name ~x0" type-name))))

(define base-type-name-string-to-pred ((type-name-string stringp))
  :returns (pred symbolp)
  (if (base-type-name-string-p type-name-string)
      (base-type-name-to-pred (intern type-name-string "ACL2"))
    (er hard? 'top-level "Unknown base type name ~x0" type-name-string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; base type to fixing function

;; All the base type fixing function names are in the ACL2 package
;; except for COMMON-LISP::IDENTITY
;; They are imported into the SYNTHETO package at package definition time.

;; Instead of separating the base type names into regular/irregular
;; categories, just list them all.

(defconst *base-type-name-to-fixing-function-alist*
  #!acl2
  '((bit . bfix)
    (nat . nfix)
    (int . ifix)
    (rational . rfix)
    (acl2-number . fix)
    (true-list . list-fix)
    (string . str-fix)
    (true . true-fix)
    (symbol . symbol-fix)
    (pos . pos-fix)
    (character . char-fix)
    (any . identity)
    (bool . bool-fix)
    (maybe-nat . maybe-natp-fix)
    (maybe-pos . maybe-posp-fix)
    (maybe-bit . maybe-bit-fix)
    (maybe-integer . maybe-integerp-fix)))

(define base-type-name-to-fix ((type-name symbolp))
  :returns (fixer symbolp)
  (let ((pair (assoc-eq type-name *base-type-name-to-fixing-function-alist*)))
    (if pair
        (cdr pair)
      (er hard? 'top-level "unknown base type name ~x0" type-name))))

(define base-type-name-string-to-fix ((type-name-string stringp))
  :returns (fixer symbolp)
  (if (base-type-name-string-p type-name-string)
      (base-type-name-to-fix (intern type-name-string "ACL2"))
    (er hard? 'top-level "Unknown base type name ~x0" type-name-string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; base type to equiv function

(defconst *base-type-name-to-equiv-function-alist*
  #!acl2
  '((bit . bit-equiv)
    (nat . nat-equiv)
    (int . int-equiv)
    (rational . rational-equiv)
    (acl2-number . number-equiv)
    (true-list . list-equiv)
    (string . streqv)
    (true . true-equiv)
    (symbol . symbol-equiv)
    (pos . pos-equiv)
    (character . chareqv)
    (any . equal)
    (bool . iff)
    (maybe-nat . maybe-nat-equiv)
    (maybe-pos . maybe-pos-equiv)
    (maybe-bit . maybe-bit-equiv)
    (maybe-integer . maybe-integer-equiv)))

(define base-type-name-to-equiv ((type-name symbolp))
  :returns (equiv symbolp)
  (let ((pair (assoc-eq type-name *base-type-name-to-equiv-function-alist*)))
    (if pair
        (cdr pair)
      (er hard? 'top-level "unknown base type name ~x0" type-name))))

(define base-type-name-string-to-equiv ((type-name-string stringp))
  :returns (equiv symbolp)
  (if (base-type-name-string-p type-name-string)
      (base-type-name-to-equiv (intern type-name-string "ACL2"))
    (er hard? 'top-level "Unknown base type name ~x0" type-name-string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
