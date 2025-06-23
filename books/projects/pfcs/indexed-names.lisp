; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-trees")

(include-book "std/strings/cat-base" :dir :system)
(include-book "std/strings/decimal" :dir :system)

(local (include-book "kestrel/fty/strings-decimal-fty" :dir :system))
(local (include-book "kestrel/utilities/lists/append-theorems" :dir :system))
(local (include-book "std/lists/no-duplicatesp" :dir :system))
(local (include-book "std/strings/explode-implode-equalities" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ indexed-names
  :parents (pfcs)
  :short "Indexed names for PFCS families."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some PFCS gadgets are actually parameterized families,
     with varying numbers of variables and/or constraints.
     In order to formalize these gadgets,
     we need to generate names (of relations and variables)
     that are parameterized, generally over numbers.")
   (xdoc::p
    "To this end, this file introduces a notion of indexed names,
     i.e. names consisting of a base (a prefix)
     and a numeric index, separated from the base with an underscore.")
   (xdoc::p
    "We introduce constructors for these indexed names,
     and we prove properties of them,
     useful in proofs about parameterized gadgets.")
   (xdoc::p
    "All of this is really more general than PFCS,
     so it could be moved to a more central place at some point.")
   (xdoc::p
    "An earlier version of the PFCS library used strings as names directly,
     i.e. not strings wrapped in the fixtype @(tsee name).
     Recently we introduced the fixtype @(tsee name)
     in order to have more structured representations of names than strings.
     Thus, we plan to rework the indexed names formalized here
     to take advantage of that generality;
     but for now we just use names as strings."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iname ((base stringp) (i natp))
  :returns (name namep)
  :short "Create an indexed name, from a base and an index."
  (name-simple (str::cat base "_" (str::nat-to-dec-string i)))

  ///

  (fty::deffixequiv iname
    :args ((i natp)))

  (defruled iname-not-equal-to-base
    (implies (stringp base)
             (not (equal (iname base i) (name-simple base))))
    :enable (string-append-lst
             string-append
             str::equal-of-implode-left-to-equal-of-explode-right
             acl2::equal-of-append-and-left)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iname-list ((base stringp) (n natp))
  :returns (names name-listp)
  :short "Create a list of indexed names,
          with the same base and indices from 0 to @('n-1')."
  (rev (iname-list-rev base n))

  :prepwork
  ((define iname-list-rev ((base stringp) (n natp))
     :returns (names-rev name-listp)
     (b* (((when (zp n)) nil)
          (n-1 (1- n))
          (name (iname base n-1))
          (names (iname-list-rev base n-1)))
       (cons name names))

     ///

     (defret len-of-iname-list-rev
       (equal (len names-rev)
              (nfix n))
       :hints (("Goal"
                :induct t
                :in-theory (enable iname-list-rev nfix fix len))))

     (defret consp-of-iname-list-rev
       (equal (consp names-rev)
              (> (nfix n) 0))
       :hints (("Goal" :induct t :in-theory (enable nfix))))

     (defruled base-not-member-of-iname-list-rev
       (implies (stringp base)
                (not (member-equal (name-simple base) (iname-list-rev base n))))
       :induct t
       :enable (iname-list-rev
                iname-not-equal-to-base))))

  ///

  (defret len-of-iname-list
    (equal (len names)
           (nfix n)))

  (defret consp-of-iname-list
    (equal (consp names)
           (> (nfix n) 0)))

  (in-theory (disable consp-of-iname-list
                      consp-of-iname-list-rev))

  (defruled base-not-member-of-iname-list
    (implies (stringp base)
             (not (member-equal (name-simple base) (iname-list base n))))
    :use base-not-member-of-iname-list-rev
    :enable iname-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We prove that INAME-LIST, defined above,
; returns a list of names without duplicates.
; This is intuitively obvious, since the numeric indices are all different.
; But to prove it formally, it takes a little bit of work.
; The idea is to define a mapping from the names to just their indices,
; show that the list of numbers is increasing,
; show that therefore the list of numbers has no duplicates,
; and from that show that the list of names has no duplicates,
; because if it had duplicates,
; the mapping would map it to a list of numbers with duplicates,
; but that was proved not to be the case.
; Most of the following functions and theorems are local to this file,
; because we only need to export the final theorem,
; which we first prove as a local event
; and then we redundantly non-locally re-state it, with XDOC documentation.
; The local functions do not need to be guard-verified;
; they are mere vehicles for proving the final theorem,
; which is the only thing that must be trusted to say the right thing
; (which is easy to assess).

; Given a base, map an indexed name to its number.

(local
 (defund iname-to-num (iname base)
   (str::dec-digit-chars-value
    (nthcdr (1+ (length base))
            (str::explode (name-simple->string iname))))))

; Lift INAME-TO-NUM to lists.

(local
 (defund iname-list-to-num-list (inames base)
   (cond ((atom inames) nil)
         (t (cons (iname-to-num (car inames) base)
                  (iname-list-to-num-list (cdr inames) base))))))

; A property about lists, which could be moved to a list library.

(defrulel nthcdr-of-append-and-len-first
  (equal (nthcdr (len a) (append a b))
         b)
  :induct t
  :enable (nthcdr append len fix))

; The function INAME-TO-NUM returns the index,
; when applied to an indexed name.
; It is left inverse of INAME.

(defrulel iname-to-num-of-iname
  (implies (stringp base)
           (equal (iname-to-num (iname base i) base)
                  (nfix i)))
  :enable (iname-to-num
           iname
           string-append-lst
           string-append
           length)
  :use (:instance nthcdr-of-append-and-len-first
                  (a (append (acl2::explode base) '(#\_)))
                  (b (acl2::explode (str::nat-to-dec-string i))))
  :disable nthcdr-of-append-and-len-first)

; Construct the list (n-1 ... 1 0).
; This consists of the indices in reverse,
; because the recursive auxiliary function INAME-LIST-REV
; builds the names in reverse order,
; and so we need to match that order to prove properties of INAME-LIST-REV,
; needed to prove properties of INAME-LIST.

(local
 (defun list-to-0 (n)
   (if (zp n)
       nil
     (cons (1- n) (list-to-0 (1- n))))))

; The list (n-1 ... 1 0) does not contain any number >= n.

(defruledl not-member-equal-of-list-to-0-when-larger
  (implies (>= m n)
           (not (member-equal m (list-to-0 n))))
  :induct t
  :enable (list-to-0
           member-equal))

; The list (n-1 ... 1 0) has no duplicates.

(defrulel no-duplicatesp-equal-of-list-to-0
  (no-duplicatesp-equal (list-to-0 n))
  :induct t
  :enable (list-to-0
           no-duplicatesp-equal
           not-member-equal-of-list-to-0-when-larger))

; Extracting the indices from the names returned by INAME-LIST-REV
; returns (n-1 ... 1 0).

(defrulel iname-list-to-num-list-of-iname-list-rev
  (implies (stringp base)
           (equal (iname-list-to-num-list (iname-list-rev base n) base)
                  (list-to-0 n)))
  :induct t
  :enable (iname-list-to-num-list
           iname-list-rev
           list-to-0
           nfix))

; If a name is in a list of names,
; then its index is in the list of indices of the names.
; This is used, below, to show the absence of duplicate names:
; the definition of NO-DUPLICATESP-EQUAL involves
; checking that the CAR is not a member of the CDR,
; and in this theorem here NAME and NAMES play the role of CAR and CDR.

(defruledl member-equal-of-iname-to-num-and-iname-list-to-num-list
  (implies (member-equal name names)
           (member-equal (iname-to-num name base)
                         (iname-list-to-num-list names base)))
  :induct t
  :enable (iname-list-to-num-list member-equal))

; If the indices extracted from a list of names have no duplicates,
; neither do the names.
; This could be proved more in general about lists,
; using a stub for the mapping.

(defruledl no-duplicatesp-equal-of-iname-list-to-num-list
  (implies (no-duplicatesp-equal (iname-list-to-num-list names base))
           (no-duplicatesp-equal names))
  :induct t
  :enable (no-duplicatesp-equal
           iname-list-to-num-list
           member-equal-of-iname-to-num-and-iname-list-to-num-list))

; Using the above fact,
; and the left inversion of INAME-LIST-TO-NUM-LIST and INAME-LIST-REV,
; we show that INAME-LIST-REV returns no duplicates.

(defruledl no-duplicatesp-equal-of-iname-list-rev
  (implies (stringp base)
           (no-duplicatesp-equal (iname-list-rev base n)))
  :use (:instance no-duplicatesp-equal-of-iname-list-to-num-list
                  (names (iname-list-rev base n)))
  :enable iname-list-to-num-list-of-iname-list-rev)

; This is the final theorem, saying that INAME-LIST returns no duplicates.

(defrulel no-duplicatesp-equal-of-iname-list
  (implies (stringp base)
           (no-duplicatesp-equal (iname-list base n)))
  :enable iname-list)

; Note that some of the local theorems above did not need to be enabled,
; in the proofs that presumably used them.
; They must have been used by the tau system.

(defrule no-duplicatesp-equal-of-iname-list
  :parents (iname-list)
  :short "The names returned by @(tsee iname-list) are all distinct,
          because the indices are all distinct."
  (implies (stringp base)
           (no-duplicatesp-equal (iname-list base n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled iname-injective-on-index
  :parents (iname)
  :short "The function @(tsee iname) is injective over the index."
  (implies (stringp base)
           (equal (equal (iname base i)
                         (iname base j))
                  (equal (nfix i)
                         (nfix j))))
  :use (only-if-part if-part)

  :prep-lemmas

  ((defruled only-if-part
     (implies (stringp base)
              (implies (equal (iname base i)
                              (iname base j))
                       (equal (nfix i)
                              (nfix j))))
     :use ((:instance iname-to-num-of-iname (i i))
           (:instance iname-to-num-of-iname (i j)))
     :disable iname-to-num-of-iname)

   (defruled if-part
     (implies (stringp base)
              (implies (equal (nfix i)
                              (nfix j))
                       (equal (iname base i)
                              (iname base j))))
     :use (:instance lemma (i (nfix i)) (j (nfix j)))
     :prep-lemmas
     ((defruled lemma
        (implies (and (stringp base)
                      (equal i j))
                 (equal (iname base i)
                        (iname base j))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled member-equal-of-iname-and-iname-list
  :parents (iname-list)
  :short "An indexed name is a list of indexed names with the same base
          iff the index is less than the number of indexed names in the list."
  (implies (stringp base)
           (iff (member-equal (iname base i) (iname-list base n))
                (< (nfix i) (nfix n))))
  :enable (iname-list
           member-equal-of-iname-and-iname-list-rev)
  :prep-lemmas
  ((defruled member-equal-of-iname-and-iname-list-rev
     (implies (stringp base)
              (iff (member-equal (iname base i) (iname-list-rev base n))
                   (< (nfix i) (nfix n))))
     :induct t
     :enable (iname-list-rev
              member-equal
              iname-injective-on-index
              nfix))))
