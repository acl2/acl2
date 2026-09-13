; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "basic-characters")
(include-book "source-character-sets")
(include-book "execution-character-sets")

(include-book "kestrel/fty/map" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ character-sets
  :parents (implementation-environments)
  :short "Source and execution character sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are described in [C17:5.2.1] and [C23:5.3.1].")
   (xdoc::p
    "The members of these sets are more abstract entities
     than the values of the character types [C17:6.2.5/15] [C23:6.2.5].
     The assignment of values to the members of the execution character set
     is implementation-defined [C17:5.2.1/1] [C23:5.3.1],
     subject to some constraints.
     The source and execution character sets may be different from each other,
     subject to certain constraints and correspondences.")
   (xdoc::p
    "We formalize the possible choices of
     source and execution character sets.
     This will become part of the "
    (xdoc::seetopic "implementation-environments" "implementation environment")
    "."))
  :order-subtopics (basic-characters
                    source-character-sets
                    execution-character-sets
                    t)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod charset
  :parents (character-sets)
  :short "Fixtype of character sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "A character set is defined by
     a source character set,
     an execution character set,
     and a mapping from source to execution characters.
     The mapping from source to execution characters is needed
     to determine the values of character constants and string literals
     [C17:5.2.1/2] [C23:5.3.1]."))
  ((source source-charset)
   (exec exec-charset)
   (source-exec-map omap::map))
  :pred charsetp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk basic-source-exec-map-wfp ((source-exec-map omap::mapp)
                                      (source-charset source-charsetp)
                                      (exec-charset exec-charsetp)
                                      (std standardp)
                                      (uchar-format uchar-formatp))
  :guard (and (source-charset-wfp source-charset std)
              (exec-charset-wfp exec-charset std uchar-format)
              (equal (omap::keys source-exec-map)
                     (source-chars source-charset)))
  :returns (yes/no booleanp)
  :short "Check that the map from source to execution characters maps
          basic source characters to corresponding basic execution characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "For every ACL2 character that represents a basic source character,
     we retrieve the corresponding source and execution characters,
     and we check that the map associates them.")
   (xdoc::p
    "[C17] and [C23] do not seem to require this explicitly,
     but it seems an obvious structural constraint."))
  (forall (bchar)
          (implies (set::in bchar (ascii-basic-source-chars std))
                   (b* ((sbchar (basic-source-char bchar
                                                   source-charset
                                                   std))
                        (ebchar (basic-exec-char bchar
                                                 exec-charset
                                                 std
                                                 uchar-format)))
                     (equal (omap::lookup sbchar source-exec-map)
                            ebchar))))
  :guard-hints (("Goal" :in-theory (enable ascii-basic-exec-chars
                                           omap::assoc-to-in-of-keys
                                           basic-source-char-in-source-chars)))
  ///
  (fty::deffixequiv-sk basic-source-exec-map-wfp
    :args ((source-exec-map omap::mapp)
           (source-charset source-charsetp)
           (exec-charset exec-charsetp)
           (std standardp)
           (uchar-format uchar-formatp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define source-exec-map-wfp ((source-exec-map omap::mapp)
                             (source-charset source-charsetp)
                             (exec-charset exec-charsetp)
                             (std standardp)
                             (uchar-format uchar-formatp))
  :guard (and (source-charset-wfp source-charset std)
              (exec-charset-wfp exec-charset std uchar-format))
  :returns (yes/no booleanp)
  :short "Check the constraints on the map from source to execution characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The constraints are expressed with respect to
     the source and execution character sets.")
   (xdoc::p
    "The map must be defined exactly on the source characters.
     This makes it possible to map every character
     appearing in a character constant or string literal
     to some execution character.
     The grammar rules
     for character constants [C17:6.4.4.4/1] [C23:6.4.5.5]
     and for string literals [C17:6.4.5/1] [C23:6.4.6]
     actually exclude backslash and new-line from both
     (while single quote is allowed in string literals,
     and double quote is allowed in character constants),
     so we could restrict the map to all the source characters
     except for backslash and new-line characters,
     but for simplicity we do not make that restriction.
     In typical C implementations,
     source and execution character sets would be both Unicode,
     so the mapping is an identity.
     But if the need arises, we could relax the constraints on
     the mapping from source to execution characters.")
   (xdoc::p
    "The map must return execution characters.
     We do not require surjectivity,
     since execution characters may be also denoted via escapes
     in character constants and string literals.")
   (xdoc::p
    "We require basic source characters to be mapped to
     the corresponding basic execution characters,
     which we check via a separate predicate."))
  (and (equal (omap::keys source-exec-map)
              (source-chars source-charset))
       (set::subset (omap::values source-exec-map)
                    (exec-chars exec-charset))
       (basic-source-exec-map-wfp source-exec-map
                                  source-charset
                                  exec-charset
                                  std
                                  uchar-format)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define charset-wfp ((charset charsetp)
                     (std standardp)
                     (uchar-format uchar-formatp))
  :returns (yes/no booleanp)
  :short "Check that a character set is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The source and execution character sets
     must be individually well-formed,
     and the mapping between them must be well-formed."))
  (b* (((charset charset)))
    (and (source-charset-wfp charset.source std)
         (exec-charset-wfp charset.exec std uchar-format)
         (source-exec-map-wfp charset.source-exec-map
                              charset.source
                              charset.exec
                              std
                              uchar-format))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define charset-source-chars ((charset charsetp))
  :returns (chars set::setp)
  :short "Set of source characters."
  (source-chars (charset->source charset)))

;;;;;;;;;;;;;;;;;;;;

(define charset-exec-chars ((charset charsetp))
  :returns (chars set::setp)
  :short "Set of execution characters."
  (exec-chars (charset->exec charset)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define charset-source-char-code (schar (charset charsetp))
  :guard (set::in schar (charset-source-chars charset))
  :returns (code natp)
  :short "Code of a source character."
  (source-char-code schar (charset->source charset))
  :guard-hints (("Goal" :in-theory (enable charset-source-chars))))

;;;;;;;;;;;;;;;;;;;;

(define charset-exec-char-value (echar (charset charsetp))
  :guard (set::in echar (charset-exec-chars charset))
  :returns (val natp)
  :short "Value of an execution character."
  (exec-char-value echar (charset->exec charset))
  :guard-hints (("Goal" :in-theory (enable charset-exec-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define charset-basic-source-char ((bchar characterp)
                                   (charset charsetp)
                                   (std standardp)
                                   (uchar-format uchar-formatp))
  :guard (and (set::in bchar (ascii-basic-source-chars std))
              (charset-wfp charset std uchar-format))
  :returns source-char
  :short "Basic source character corresponding to an ACL2 character."
  (declare (ignore uchar-format))
  (basic-source-char bchar (charset->source charset) std)
  :guard-hints (("Goal" :in-theory (enable charset-wfp)))

  ///

  (defruled charset-basic-source-char-in-charset-source-chars
    (implies (and (charset-wfp charset std uchar-format)
                  (set::in bchar (ascii-basic-source-chars std)))
             (set::in (charset-basic-source-char bchar charset std uchar-format)
                      (charset-source-chars charset)))
    :enable (charset-basic-source-char
             charset-source-chars
             charset-wfp
             basic-source-char-in-source-chars)))

;;;;;;;;;;;;;;;;;;;;

(define charset-basic-exec-char ((bchar characterp)
                                 (charset charsetp)
                                 (std standardp)
                                 (uchar-format uchar-formatp))
  :guard (and (set::in bchar (ascii-basic-exec-chars std))
              (charset-wfp charset std uchar-format))
  :returns exec-char
  :short "Basic execution character corresponding to an ACL2 character."
  (basic-exec-char bchar (charset->exec charset) std uchar-format)
  :guard-hints (("Goal" :in-theory (enable charset-wfp)))

  ///

  (defruled charset-basic-exec-char-in-charset-exec-chars
    (implies (and (charset-wfp charset std uchar-format)
                  (set::in bchar (ascii-basic-exec-chars std)))
             (set::in (charset-basic-exec-char bchar charset std uchar-format)
                      (charset-exec-chars charset)))
    :enable (charset-basic-exec-char
             charset-exec-chars
             charset-wfp
             basic-exec-char-in-exec-chars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define charset-source-to-exec (source-char
                                (charset charsetp)
                                (std standardp)
                                (uchar-format uchar-formatp))
  :guard (and (charset-wfp charset std uchar-format)
              (set::in source-char (charset-source-chars charset)))
  :returns exec-char
  :short "Map a source character to an execution character."
  (declare (ignore std uchar-format))
  (omap::lookup source-char (charset->source-exec-map charset))
  :guard-hints (("Goal" :in-theory (enable charset-wfp
                                           source-exec-map-wfp
                                           charset-source-chars)))

  ///

  (defrule charset-source-to-exec-in-charset-exec-chars
    (implies (and (charset-wfp charset std uchar-format)
                  (set::in source-char (charset-source-chars charset)))
             (set::in (charset-source-to-exec
                       source-char charset std uchar-format)
                      (charset-exec-chars charset)))
    :enable (charset-wfp
             source-exec-map-wfp
             charset-source-chars
             charset-exec-chars
             set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define charset-basic+lf ((std standardp))
  :returns (charset charsetp)
  :short "The character set consisting of
          the basic source characters plus LF
          and the basic execution characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "We combine @(tsee source-charset-basic+lf)
     with @(tsee exec-charset-basic).
     Since both character sets use ACL2 characters directly,
     the mapping from source to execution characters is the identity."))
  (b* ((source (source-charset-basic+lf std))
       (exec (exec-charset-basic std))
       (source-exec-map (omap::identity (source-chars source))))
    (make-charset :source source
                  :exec exec
                  :source-exec-map source-exec-map))

  ///

  (defrulel ascii-basic-source-chars-subset-source-chars-lemma
    (set::subset (ascii-basic-source-chars std)
                 (source-chars (source-charset-basic+lf std)))
    :enable (source-chars
             source-charset-basic+lf
             acl2::any-nat-mapp-when-character-nat-mapp
             set::expensive-rules))

  (defrulel source-chars-subset-exec-chars-lemma
    (set::subset (source-chars (source-charset-basic+lf std))
                 (exec-chars (exec-charset-basic std)))
    :enable (source-chars
             source-charset-basic+lf
             exec-chars
             exec-charset-basic
             ascii-basic-exec-chars
             acl2::any-nat-mapp-when-character-nat-mapp
             set::expensive-rules))

  (defrulel source-exec-map-wfp-lemma
    (source-exec-map-wfp
     (omap::identity (source-chars (source-charset-basic+lf std)))
     (source-charset-basic+lf std)
     (exec-charset-basic std)
     std
     uchar-format)
    :enable (source-exec-map-wfp
             basic-source-exec-map-wfp
             omap::values-is-keys-when-identityp
             omap::lookup-when-identityp
             basic-source-char-of-source-charset-basic+lf
             basic-exec-char-of-exec-charset-basic
             ascii-basic-source-chars-subset-source-chars-lemma
             ascii-basic-source-chars-subset-ascii-basic-exec-chars
             set::subset-in
             set::expensive-rules))

  (defrule charset-wfp-of-charset-basic+lf
    (charset-wfp (charset-basic+lf std) std uchar-format)
    :enable (charset-wfp
             charset-basic+lf)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define charset-ascii ((std standardp) (end-of-lines true-list-setp))
  :guard (and (not (set::emptyp end-of-lines))
              (source-charset-end-of-lines-wfp end-of-lines
                                               (source-charset-ascii-loop 0)))
  :returns (charset charsetp)
  :short "The character set defined by
          ASCII and a specified set of source line endings."
  :long
  (xdoc::topstring
   (xdoc::p
    "We combine @(tsee source-charset-ascii) with @(tsee exec-charset-ascii).
     Both character sets use the same 128 ACL2 ASCII characters,
     so the mapping from source to execution characters is the identity.")
   (xdoc::p
    "The @('std') parameter determines the basic execution characters,
     and @('end-of-lines') specifies the exact source new-line representations
     as sequences of ACL2 ASCII characters."))
  (b* ((source (source-charset-ascii end-of-lines))
       (exec (exec-charset-ascii std))
       (source-exec-map (omap::identity (source-chars source))))
    (make-charset :source source
                  :exec exec
                  :source-exec-map source-exec-map))

  ///

  (defruled source-chars-equal-exec-chars-ascii-lemma
    (equal (source-chars (source-charset-ascii end-of-lines))
           (exec-chars (exec-charset-ascii std)))
    :enable (source-chars
             source-charset-ascii
             exec-chars
             exec-charset-ascii))

  (defrulel basic-source-exec-map-ascii-lemma
    (implies
     (set::in bchar (ascii-basic-source-chars std))
     (equal
      (omap::lookup
       (basic-source-char bchar (source-charset-ascii end-of-lines) std)
       (omap::identity (source-chars (source-charset-ascii end-of-lines))))
      (basic-exec-char bchar (exec-charset-ascii std) std uchar-format)))
    :enable (source-chars
             source-charset-ascii
             exec-charset-ascii
             basic-source-char
             basic-exec-char
             ascii-basic-source-chars
             ascii-basic-exec-chars
             member-equal
             set::in))

  (defrulel source-exec-map-ascii-wfp-lemma
    (source-exec-map-wfp
     (omap::identity (source-chars (source-charset-ascii end-of-lines)))
     (source-charset-ascii end-of-lines)
     (exec-charset-ascii std)
     std
     uchar-format)
    :use source-chars-equal-exec-chars-ascii-lemma
    :enable (source-exec-map-wfp
             basic-source-exec-map-wfp
             omap::values-is-keys-when-identityp))

  (defrule charset-wfp-of-charset-ascii
    (implies
     (and (not (set::emptyp (true-list-set-fix end-of-lines)))
          (source-charset-end-of-lines-wfp end-of-lines
                                           (source-charset-ascii-loop 0)))
     (charset-wfp (charset-ascii std end-of-lines) std uchar-format))
    :enable (charset-wfp
             charset-ascii)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define charset-unicode ((std standardp) (end-of-lines true-list-setp))
  :guard (and (not (set::emptyp end-of-lines))
              (source-charset-end-of-lines-wfp end-of-lines
                                               (unicode-code-map)))
  :returns (charset charsetp)
  :short "The character set defined by
          Unicode and a specified set of source line endings."
  :long
  (xdoc::topstring
   (xdoc::p
    "We combine @(tsee source-charset-unicode) with @(tsee exec-charset-unicode).
     Both character sets use the Unicode scalar values as characters,
     so the mapping from source to execution characters is the identity.")
   (xdoc::p
    "The @('std') parameter determines the basic execution characters,
     and @('end-of-lines') specifies the exact source new-line representations
     as sequences of Unicode scalar values."))
  (b* ((source (source-charset-unicode end-of-lines))
       (exec (exec-charset-unicode std))
       (source-exec-map (unicode-code-map)))
    (make-charset :source source
                  :exec exec
                  :source-exec-map source-exec-map))

  ///

  (in-theory (disable (:e charset-unicode)))

  (defruled source-chars-equal-exec-chars-unicode-lemma
    (equal (source-chars (source-charset-unicode end-of-lines))
           (exec-chars (exec-charset-unicode std)))
    :enable (source-chars-of-source-charset-unicode
             exec-chars-of-exec-charset-unicode))

  (defrulel source-exec-map-unicode-wfp-lemma
    (source-exec-map-wfp
     (unicode-code-map)
     (source-charset-unicode end-of-lines)
     (exec-charset-unicode std)
     std
     uchar-format)
    :enable (source-exec-map-wfp
             basic-source-exec-map-wfp
             source-chars-of-source-charset-unicode
             exec-chars-of-exec-charset-unicode
             basic-source-char-of-source-charset-unicode
             basic-exec-char-of-exec-charset-unicode
             ascii-basic-source-chars-subset-ascii-basic-exec-chars
             set::subset-in))

  (defrule charset-wfp-of-charset-unicode
    (implies
     (and (not (set::emptyp (true-list-set-fix end-of-lines)))
          (source-charset-end-of-lines-wfp end-of-lines (unicode-code-map)))
     (charset-wfp (charset-unicode std end-of-lines) std uchar-format))
    :enable (charset-wfp charset-unicode)))
