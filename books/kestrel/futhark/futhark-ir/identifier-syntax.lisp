; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "lexical-syntax")
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifier-syntax
  :parents (concrete-syntax parsing-and-printing)
  :short "Token-level word and name syntax for Futhark IR text."
  :long
  (xdoc::topstring
   (xdoc::p
    "Remora has a surface-language @('identifier') rule plus a post-parsing
     keyword-exclusion side condition.  The Futhark IR text handled here is
     different: the grammar uses a broad @('word') token not only for names,
     but also for primitive type atoms, array sizes such as @('2i64'), and
     typed literals such as @('1i32').")
   (xdoc::p
    "This book therefore separates token-level words from name-like words.
     @(tsee ir-word-tokenp) recognizes the broad tokens accepted by
     the IR lexer.  @(tsee ir-name-tokenp) additionally rejects the
     current reserved words and literal-looking words, and is suitable for
     function and variable names.")
   (xdoc::p
    "ACL2 strings used by the public parser and AST are byte strings.  The
     parser decodes UTF-8 bytes to Unicode code points before parsing, and
     syntax abstraction UTF-8-encodes code points back into ACL2 strings for
     storage, following the Remora front end's convention.")
   (xdoc::p
    "The executable non-ASCII identifier predicate intentionally
     over-approximates Futhark's Haskell @('Data.Char.isAlpha') /
     @('isAlphaNum') checks: it accepts non-ASCII non-whitespace scalar
     values.  This is the same practical shape as Remora's ACL2 parser and
     covers the Remora-emitted IR names we have seen."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *ir-keywords*
  '("name_source"
    "types"
    "fun"
    "entry"
    "let"
    "in"
    "apply"
    "map"
    "true"
    "false"))

(define ir-keywordp ((tok stringp))
  :returns (yes/no booleanp)
  :short "Check if a token is a reserved word in the supported IR subset."
  (if (member-equal (str-fix tok) *ir-keywords*) t nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ir-name-start-codepointp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a code point may start a Futhark IR name."
  (b* ((nat (nfix nat)))
    (or (ascii-letter-codepointp nat)
        (non-ascii-non-whitespace-codepointp nat)
        (eql nat #x21)   ; !
        (eql nat #x25)   ; %
        (eql nat #x26)   ; &
        (eql nat #x2A)   ; *
        (eql nat #x2B)   ; +
        (eql nat #x2D)   ; -
        (eql nat #x2E)   ; .
        (eql nat #x2F)   ; /
        (eql nat #x3C)   ; <
        (eql nat #x3D)   ; =
        (eql nat #x3E)   ; >
        (eql nat #x5E)   ; ^
        (eql nat #x5F)   ; _
        (eql nat #x7C)))) ; |

(define ir-name-codepoint-listp ((nats nat-listp))
  :returns (yes/no booleanp)
  (and (consp nats)
       (ir-name-start-codepointp (car nats))
       (ir-word-codepoint-listp (cdr nats))))

(define ir-name-tokenp ((tok stringp))
  :returns (yes/no booleanp)
  :short "Check if a word token is suitable as a function or variable name."
  (b* ((tok (str-fix tok))
       (nats (string=>codepoints tok)))
    (and (ir-name-codepoint-listp nats)
         (not (equal tok "->"))
         (not (ir-keywordp tok))
         (not (ir-literal-tokenp tok)))))
