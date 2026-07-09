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
