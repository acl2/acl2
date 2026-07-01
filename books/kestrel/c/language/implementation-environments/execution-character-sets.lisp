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
(include-book "uchar-formats")

(include-book "kestrel/fty/any-nat-map" :dir :system)
(include-book "kestrel/fty/character-any-map" :dir :system)
(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/omaps/injectivep" :dir :system)

(local (include-book "kestrel/arithmetic-light/types" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ execution-character-sets
  :parents (character-sets)
  :short "Execution character sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see character-sets) and @(see source-character-sets) first.")
   (xdoc::p
    "Here we formalize the possible choices of execution character sets
     [C17:5.2.1] [C23:5.3.1].")
   (xdoc::p
    "Each choice of execution character set is characterized by
     a set of basic and extended characters (which may be any ACL2 values),
     an injective map from that set to the natural numbers,
     and an injective map
     from the set of ASCII characters that correspond to basic characters
     to the set of execution characters.
     The first two parts are similar to source characters,
     but the natural numbers that the execution characters map to
     are their numeric values, instead of codes used as ABNF terminals.
     The third part does not have a counterpart in source character sets,
     where the freedom to pick the mapping from characters to natural numbers
     allows us to use that mapping to identify the basic source characters
     based on the ASCII codes that they map to;
     in the execution character set,
     the numeric values of the basic characters
     may or may not coincide with the ASCII codes
     (although normally they do),
     and so we need an explicit mapping for that.")
   (xdoc::p
    "Unlike source characters,
     the ordering (i.e. collating sequence) matters for execution characters.
     It is directly determined by the numeric values.
     We require that digits are in increasing numeric value
     [C17:5.2.1/3] [C23:5.3.1].")
   (xdoc::p
    "Unlike source characters,
     for execution characters we do not need to indicate
     the possible ways in which new-line characters are encoded.")
   (xdoc::p
    "We require the values of the execution basic characters
     to fit in a byte [C17:5.2.1.2/1] [C23:5.3.2].")
   (xdoc::p
    "Here we do not model anything about shift states
     [C17:5.2.1.2/1] [C23:5.3.2].
     These have to do with encoding,
     and so they seem to belong somewhere else."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod exec-charset
  :short "Fixtype of execution character sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the map from characters to naturals
     is defined exactly over the set of characters,
     we just need the map to represent
     both the set of characters (i.e. the keys of the map)
     and their association to natural numbers.")
   (xdoc::p
    "We have a separate map from ACL2 characters to execution characters,
     which we constrain in separate predicates."))
  ((chars-with-values any-nat-map)
   (basic-chars character-any-map))
  :pred exec-charsetp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-charset-has-basic-chars-p ((chars-with-values any-nat-mapp)
                                        (basic-chars character-any-mapp)
                                        (std standardp))
  :returns (yes/no booleanp)
  :short "Check if (the character-to-value map of) an execution character set
          includes the basic characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys of the ACL2-characters-to-execution-characters map
     must be exactly the ASCII basic execution characters,
     and the values of the map must be a subset of
     the keys of the character-to-value map."))
  (and (equal (omap::keys (character-any-mfix basic-chars))
              (ascii-basic-exec-chars std))
       (set::subset (omap::values (character-any-mfix basic-chars))
                    (omap::keys (any-nat-mfix chars-with-values)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk exec-charset-basic-chars-byte-p ((chars-with-values any-nat-mapp)
                                            (basic-chars character-any-mapp)
                                            (uchar-format uchar-formatp))
  :guard (set::subset (omap::values basic-chars)
                      (omap::keys chars-with-values))
  :returns (yes/no booleanp)
  :short "Check if the value of each basic character
          of an execution character set
          fits in a byte."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C, a byte is defined by the number of bits of @('unsigned char')."))
  (forall (val)
          (implies (set::in val
                            (omap::lookup* (omap::values
                                            (character-any-mfix basic-chars))
                                           (any-nat-mfix chars-with-values)))
                   (<= val (uchar-format->max uchar-format))))
  :guard-hints (("Goal"
                 :in-theory (enable omap::in*-alt-def
                                    acl2::nat-setp-of-values-when-any-nat-mapp
                                    acl2::rationalp-when-natp)
                 :use (:instance acl2::nat-setp-of-subset-when-superset
                                 (a (omap::lookup*
                                     (omap::values
                                      (character-any-mfix basic-chars))
                                     (any-nat-mfix chars-with-values)))
                                 (b (omap::values
                                     (any-nat-mfix chars-with-values))))))
  ///
  (fty::deffixequiv-sk exec-charset-basic-chars-byte-p
    :args ((chars-with-values any-nat-mapp)
           (basic-chars character-any-mapp)
           (uchar-format uchar-formatp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk exec-charset-digits-in-order-p ((chars-with-values any-nat-mapp)
                                           (basic-chars character-any-mapp))
  :guard (and (set::subset '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                           (omap::keys basic-chars))
              (set::subset (omap::values basic-chars)
                           (omap::keys chars-with-values)))
  :returns (yes/no booleanp)
  :short "Check if the values of the digits are ordered."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each digit from 1 to 9, its value must be
     the value of digit 0 plus
     the difference between the two digits:
     the value of digit 1 must be one more than the value of digit 0;
     the value of digit 2 must be two more than the value of digit 0;
     and so on.
     We need to map the ACL2 character to the execution character,
     and then map the execution character to its value.
     We calculate the difference between digits via
     the ASCII codes of the ACL2 characters."))
  (forall (ch)
          (b* ((chars-with-values (any-nat-mfix chars-with-values))
               (basic-chars (character-any-mfix basic-chars)))
            (implies (set::in ch '(#\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
                     (equal (omap::lookup (omap::lookup ch basic-chars)
                                          chars-with-values)
                            (+ (omap::lookup (omap::lookup #\0 basic-chars)
                                             chars-with-values)
                               (- (char-code ch) (char-code #\0)))))))
  :guard-hints (("Goal" :in-theory (enable* omap::assoc-to-in-of-keys
                                            acl2::acl2-numberp-when-natp
                                            set::expensive-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-charset-wfp ((charset exec-charsetp)
                          (std standardp)
                          (uchar-format uchar-formatp))
  :returns (yes/no booleanp)
  :short "Check the constraints on an execution character set."
  :long
  (xdoc::topstring
   (xdoc::p
    "The map from characters to values must be injective.
     The character set must include the basic characters,
     whose values must all fit in a byte.
     The digit values must be in order."))
  (b* (((exec-charset charset)))
    (and (omap::injectivep charset.chars-with-values)
         (exec-charset-has-basic-chars-p charset.chars-with-values
                                         charset.basic-chars
                                         std)
         (exec-charset-basic-chars-byte-p charset.chars-with-values
                                          charset.basic-chars
                                          uchar-format)
         (exec-charset-digits-in-order-p charset.chars-with-values
                                         charset.basic-chars)))
  :guard-hints (("Goal" :in-theory (enable exec-charset-has-basic-chars-p
                                           digits-in-ascii-basic-exec-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-chars ((charset exec-charsetp))
  :returns (chars set::setp)
  :short "Set of execution characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the keys of the map from characters to their values."))
  (omap::keys (exec-charset->chars-with-values charset)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-char-value (echar (charset exec-charsetp))
  :guard (set::in echar (exec-chars charset))
  :returns (val natp)
  :short "Value of an execution character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the natural number associated to the map."))
  (lnfix (omap::lookup echar (exec-charset->chars-with-values charset)))
  :guard-hints (("Goal" :in-theory (enable exec-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define basic-exec-char ((bchar characterp)
                         (charset exec-charsetp)
                         (std standardp)
                         (uchar-format uchar-formatp))
  :guard (and (set::in bchar (ascii-basic-exec-chars std))
              (exec-charset-wfp charset std uchar-format))
  :returns exec-char
  :short "Basic execution character corresponding to
          an ACL2 character denoting a basic execution character."
  (declare (ignore std uchar-format))
  (omap::lookup (acl2::char-fix bchar) (exec-charset->basic-chars charset))
  :guard-hints (("Goal" :in-theory (enable exec-charset-wfp
                                           exec-charset-has-basic-chars-p)))

  ///

  (defruled basic-exec-char-in-exec-chars
    (implies (and (exec-charset-wfp charset std uchar-format)
                  (set::in bchar (ascii-basic-exec-chars std)))
             (set::in (basic-exec-char bchar charset std uchar-format)
                      (exec-chars charset)))
    :enable (exec-chars
             exec-charset-wfp
             exec-charset-has-basic-chars-p
             set::expensive-rules)))
