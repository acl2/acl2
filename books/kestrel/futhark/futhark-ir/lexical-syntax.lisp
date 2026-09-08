; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "../codepoint-utilities")
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexical-syntax
  :parents (concrete-syntax parsing-and-printing)
  :short "Token-level lexical syntax for Futhark IR text."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Futhark IR grammar uses a broad @('word') token for several roles:
     names, primitive type atoms, array sizes such as @('2i64'), and typed
     literals such as @('1i32').  This book collects predicates for those
     broad tokens and for unescaped string-literal characters.")
   (xdoc::p
    "Identifier-specific restrictions, such as keyword exclusion and the
     first-character rule for names, are in @(see identifier-syntax)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ir-word-char-codepointp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a code point may occur in a lexer word token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This mirrors the continuation side of Futhark's @('pName') parser for
     ASCII characters and admits Remora-style non-ASCII scalar identifier
     characters.  The arrow token @('->') is reserved separately by
     @(tsee ir-word-tokenp)."))
  (b* ((nat (nfix nat)))
    (or (ascii-letter-codepointp nat)
        (ascii-digit-codepointp nat)
        (non-ascii-non-whitespace-codepointp nat)
        (eql nat #x21)   ; !
        (eql nat #x25)   ; %
        (eql nat #x26)   ; &
        (eql nat #x27)   ; '
        (eql nat #x2A)   ; *
        (eql nat #x2B)   ; +
        (eql nat #x2D)   ; -
        (eql nat #x2E)   ; .
        (eql nat #x2F)   ; /
        (eql nat #x3C)
        (eql nat #x3D)
        (eql nat #x3E)
        (eql nat #x5E)   ; ^
        (eql nat #x5F)   ; _
        (eql nat #x7C)))) ; |

(define ir-word-codepoint-listp ((nats nat-listp))
  :returns (yes/no booleanp)
  :short "Check if every code point in a list may occur in an IR word token."
  (if (endp nats)
      t
    (and (ir-word-char-codepointp (car nats))
         (ir-word-codepoint-listp (cdr nats)))))

(define ir-string-char-codepointp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a code point may appear unescaped in an IR string literal."
  (b* ((nat (nfix nat)))
    (and (unicode-scalar-codepointp nat)
         (<= #x20 nat)
         (not (eql nat #x22))   ; double quote
         (not (eql nat #x5C))))) ; backslash

(define ir-word-tokenp ((tok stringp))
  :returns (yes/no booleanp)
  :short "Check if a lexer token is a broad Futhark IR word."
  (b* ((tok (str-fix tok))
       (nats (string=>codepoints tok)))
    (and (consp nats)
         (not (equal tok "->"))
         (ir-word-codepoint-listp nats))))

(define ir-literal-tokenp ((tok stringp))
  :returns (yes/no booleanp)
  :short "Check if a word token looks like a Futhark IR literal."
  (b* ((tok (str-fix tok))
       (nats (string=>codepoints tok)))
    (or (equal tok "true")
        (equal tok "false")
        (and (consp nats)
             (or (ascii-digit-codepointp (nfix (car nats)))
                 (and (eql (car nats) #x2D)
                      (consp (cdr nats))
                      (ascii-digit-codepointp
                       (nfix (cadr nats)))))))))
