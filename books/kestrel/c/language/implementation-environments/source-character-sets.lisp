; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "basic-characters")

(include-book "kestrel/fty/any-nat-map" :dir :system)
(include-book "kestrel/fty/true-list-set" :dir :system)
(include-book "kestrel/utilities/strings/char-code-set" :dir :system)
(include-book "std/omaps/injectivep" :dir :system)
(include-book "std/omaps/inverse" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ source-character-sets
  :parents (character-sets)
  :short "Source character sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see character-sets) first.")
   (xdoc::p
    "Here we formalize the possible choices of source character sets
     [C17:5.2.1] [C23:5.3.1].")
   (xdoc::p
    "Each choice of source character set is characterized by
     a set of basic and extended characters (which may be any ACL2 values)
     and an injective map from that set to natural numbers.
     The map serves two purposes:
     it provides a unique code for each character,
     enabling the use of the ABNF notation for describing syntax,
     given that ABNF requires natural numbers as terminals;
     it identifies the subset of basic characters, in the following manner.
     Although [C17] and [C23] do not require ASCII or a superset of it,
     the basic characters have a natural correspondence with ASCII characters.
     We require the map to include, among its values,
     all the ASCII codes that correspond to the basic characters:
     the map's inverse image of these ASCII codes is
     the set of basic characters,
     and the rest of the keys of the map form
     the set of extended characters.
     Although ABNF is agnostic with respect to ASCII or not,
     ABNF string notations denote ASCII codes,
     and thus having the map associate ASCII codes to the basic characters
     enables us to denote them via ABNF string notations.")
   (xdoc::p
    "Both [C17:5.2.1/1] and [C23:5.3.1] mention
     a collating sequence (i.e. an ordering)
     for both source and execution character sets.
     However, close examination reveals that
     this is only needed for the execution character set,
     not for the source character set.
     [C17:5.2.1/3] and [C23:5.3.1]
     talk about values of the source and execution character sets,
     and how the values of the digit characters must be sequential;
     however, the values of source characters are never really used.
     The mapping from multi-byte characters to the source character sets
     is implementation-defined [C17:5.1.1.2/1] [C23:5.2.1.2],
     so we do not need to model it in any explicit way
     (which is where the source character values could come into play).")
   (xdoc::p
    "To completely characterize a source character set
     we also need to model the representation of new-line characters.
     [C17:5.2.1/3] and [C23:5.3.1] say that the standard
     treats them as if there were a single new-line character.
     However, we know that, in practical C implementations,
     there may be multiple ways to represent new-line characters,
     and some of these representations may take multiple characters.
     For instance, macOS and Linux use line feed,
     while Windows uses carriage return followed by line feed;
     but a C implementation may accept all of them,
     regardless of the underlying operating system.
     This is not in conflict with [C17] and [C23], which say `as if',
     leaving the door open for multiple multi-character representations.
     So our model of the source character set also includes
     a non-empty set of non-empty lists of characters,
     which are new-line character representations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod source-charset
  :short "Fixtype of source character sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the map described in @(see source-character-sets)
     is defined exactly over the set of characters,
     we just need the map to represent
     both the set of characters (i.e. the keys of the map)
     and their associations to natural numbers.")
   (xdoc::p
    "This fixtype does not capture the constraints on the map,
     which depend on the C standard.
     These constraints are captured in a separate predicate."))
  ((chars-with-codes any-nat-map)
   (end-of-lines true-list-set))
  :pred source-charsetp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define source-charset-has-basic-chars-p ((chars-with-codes any-nat-mapp)
                                          (std standardp))
  :returns (yes/no booleanp)
  :short "Check if (the character-to-code map of) a source character set
          includes the basic characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The values of the map must include
     the ASCII codes of the basic characters."))
  (set::subset (acl2::char-code-set (ascii-basic-source-chars std))
               (omap::values (any-nat-mfix chars-with-codes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define source-charset-end-of-lines-wfp ((end-of-lines true-list-setp)
                                         (chars-with-codes any-nat-mapp))
  :returns (yes/no booleanp)
  :short "Check if the end-of-line representations in a source character set
          are all well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the new-line representations must be non-empty
     and consist of characters in the map.
     For flexibility, we do not require the characters to be extended ones.
     Perhaps vertical tab and form feed might be regarded as
     new-line character representations in some C implementations.
     We do not even require the lists to be free of duplicates.
     We do not prohibit any representation from being a prefix of another one,
     e.g. to allow both carriage return alone and it followed by line feed;
     generally, in a list of source characters,
     we will take the longest possible sequence
     to denote each single new-line character."))
  (or (set::emptyp (true-list-set-fix end-of-lines))
      (b* ((chars (true-list-fix (set::head end-of-lines))))
        (and (consp chars)
             (set::subset (set::mergesort chars)
                          (omap::keys (any-nat-mfix chars-with-codes)))
             (source-charset-end-of-lines-wfp (set::tail end-of-lines)
                                              chars-with-codes))))
  :prepwork ((local (in-theory (enable acl2::emptyp-of-true-list-set-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define source-charset-wfp ((charset source-charsetp) (std standardp))
  :returns (yes/no booleanp)
  :short "Check the constraints on a source character set."
  :long
  (xdoc::topstring
   (xdoc::p
    "The map must be injective and include the basic characters;
     the list of end-of-line representations must be non-empty
     and consist of well-formed representations."))
  (b* (((source-charset charset)))
    (and (omap::injectivep charset.chars-with-codes)
         (source-charset-has-basic-chars-p charset.chars-with-codes std)
         (not (set::emptyp charset.end-of-lines))
         (source-charset-end-of-lines-wfp charset.end-of-lines
                                          charset.chars-with-codes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define source-chars ((charset source-charsetp))
  :returns (chars set::setp)
  :short "Set of source characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the keys of the map from characters to their codes."))
  (omap::keys (source-charset->chars-with-codes charset)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define source-char-code (schar (charset source-charsetp))
  :guard (set::in schar (source-chars charset))
  :returns (code natp)
  :short "Code of a source character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the natural number associated to the character."))
  (lnfix (omap::lookup schar (source-charset->chars-with-codes charset)))
  :guard-hints (("Goal" :in-theory (enable source-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define basic-source-char ((bchar characterp)
                           (charset source-charsetp)
                           (std standardp))
  :guard (and (set::in bchar (ascii-basic-source-chars std))
              (source-charset-wfp charset std))
  :returns source-char
  :short "Basic source character corresponding to an ACL2 character."
  :long
  (xdoc::topstring
   (xdoc::p
    "We invert the map from source characters to their codes,
     which is an injective map according to the well-formedness condition,
     and we find the source character associated to
     the ASCII code of the ACL2 character."))
  (declare (ignore std))
  (omap::lookup (char-code bchar)
                (omap::inverse (source-charset->chars-with-codes charset)))
  :guard-hints
  (("Goal" :in-theory (enable* source-charset-wfp
                               source-charset-has-basic-chars-p
                               acl2::code-in-char-code-set-when-char-in-char-set
                               set::expensive-rules)))

  ///

  (defruled basic-source-char-in-source-chars
    (implies (and (source-charset-wfp charset std)
                  (set::in bchar (ascii-basic-source-chars std)))
             (set::in (basic-source-char bchar charset std)
                      (source-chars charset)))
    :enable (source-chars
             source-charset-wfp
             source-charset-has-basic-chars-p
             acl2::code-in-char-code-set-when-char-in-char-set
             set::expensive-rules
             omap::lookup-inverse-in-keys-when-in-values-and-injective))

  (defruled source-char-code-of-basic-source-char
    (implies (and (source-charset-wfp charset std)
                  (set::in bchar (ascii-basic-source-chars std)))
             (equal (source-char-code (basic-source-char bchar charset std)
                                      charset)
                    (char-code bchar)))
    :enable (source-char-code
             basic-source-char
             source-charset-wfp
             source-charset-has-basic-chars-p
             acl2::code-in-char-code-set-when-char-in-char-set
             omap::lookup-of-lookup-of-inverse
             set::subset-in)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define source-charset-basic+lf ((std standardp))
  :returns (charset source-charsetp)
  :short "The source character set defined by
          the basic characters plus
          LF as the only extended character and the only line ending."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the ACL2 ASCII characters
     that correspond to the basic source characters,
     together with LF so that it can represent the line ending."))
  (b* ((chars-with-codes
        (source-charset-basic+lf-loop
         (set::insert #\Newline (ascii-basic-source-chars std))))
       (end-of-lines (set::insert (list #\Newline) nil)))
    (make-source-charset :chars-with-codes chars-with-codes
                         :end-of-lines end-of-lines))

  :prepwork
  ((define source-charset-basic+lf-loop ((chars character-setp))
     :returns (map any-nat-mapp)
     :parents nil
     (b* (((when (set::emptyp (character-sfix chars))) nil)
          (char (set::head chars)))
       (omap::update char
                     (char-code char)
                     (source-charset-basic+lf-loop (set::tail chars))))
     :prepwork ((local (in-theory (enable acl2::emptyp-of-character-sfix))))
     :verify-guards :after-returns

     ///

     (defret keys-of-source-charset-basic+lf-loop
       (equal (omap::keys map)
              (character-sfix chars))
       :hints (("Goal"
                :induct t
                :in-theory (enable set::emptyp
                                   character-sfix))))

     (defret values-of-source-charset-basic+lf-loop
       (equal (omap::values map)
              (acl2::char-code-set chars))
       :hints (("Goal"
                :induct t
                :in-theory (enable acl2::char-code-set
                                   omap::assoc-to-in-of-keys))))

     (defret injectivep-of-source-charset-basic+lf-loop
       (omap::injectivep map)
       :hints (("Goal"
                :induct t
                :in-theory
                (enable acl2::not-in-char-code-set-when-not-in-char-set))))))

  ///

  (defrule source-charset-wfp-of-source-charset-basic+lf
    (source-charset-wfp (source-charset-basic+lf std) std)
    :enable (source-charset-wfp
             source-charset-has-basic-chars-p
             source-charset-end-of-lines-wfp
             acl2::char-code-set-monotone
             set::in
             set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define source-charset-ascii ()
  :returns (charset source-charsetp)
  :short "The source character set defined by
          ASCII and three kinds of line endings (LF, CR, and CR LF)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the 128 ASCII characters,
     for which we use the ACL2 characters with the respective codes."))
  (b* ((chars-with-codes (source-charset-ascii-loop 0))
       (end-of-lines (set::mergesort (list (list #\Newline)
                                           (list #\Return)
                                           (list #\Return #\Newline)))))
    (make-source-charset :chars-with-codes chars-with-codes
                         :end-of-lines end-of-lines))

  :prepwork
  ((define source-charset-ascii-loop ((code natp))
     :returns (map any-nat-mapp)
     :parents nil
     (if (>= (lnfix code) 128)
         nil
       (omap::update (code-char code)
                     (lnfix code)
                     (source-charset-ascii-loop (1+ (lnfix code)))))
     :measure (nfix (- 128 (nfix code)))
     :hints (("Goal" :in-theory (enable nfix)))
     :verify-guards :after-returns
     :hooks ((:fix :hints (("Goal" :in-theory (enable nfix)))))))

  ///

  (defrule source-charset-wfp-of-source-charset-ascii
    (source-charset-wfp (source-charset-ascii) std)
    :enable (source-charset-wfp
             source-charset-has-basic-chars-p
             ascii-basic-source-chars
             acl2::char-code-set)))
