; C++ Syntax Extension for ACL2 Kestrel C Library
;
; This file sets up the CPP package for the C++ extension books.
; It mirrors the pattern used by kestrel/c/transformation/ (C2C package).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Include the portcullis chain that defines the C$ package.
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/c/portcullis" :dir :system)
(include-book "kestrel/c/syntax/portcullis" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

; Import the C$ abstract syntax symbols constant.
(include-book "kestrel/c/syntax/abstract-syntax-symbols" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "CPP"
  (append
   ;; Standard library symbols (all except 'block' which conflicts).
   (set-difference-eq *std-pkg-symbols*
                      '(block
                        type
                        typep))
   ;; All C$ abstract syntax symbols (identifiers, expressions, statements,
   ;; declarations, translation units, etc.).
   c$::*abstract-syntax-symbols*
   ;; C$ parser state stobj and key accessors.
   ;; By importing C$::PARSTATE we can use 'parstate' as the stobj name in CPP.
   '(c$::parstate
     c$::parstatep
     c$::parstate-fix
     c$::parstate->keywords
     c$::parstate->size
     c$::parstate->bytes
     c$::parsize)
   ;; C$ token utilities.
   '(c$::token-case
     c$::token-keywordp
     c$::token-punctuatorp
     c$::token-ident->ident
     c$::token-keyword->keyword
     c$::token-punctuator->punctuator
     c$::token-option-some->val
     c$::token-optionp
     c$::tokenp
     c$::irr-token)
   ;; C$ lexer/parser API.
   '(c$::read-token
     c$::unread-token
     c$::unread-tokens)
   ;; C$ span and position utilities.
   ;; Note: c$::position conflicts with the 'position' symbol from
   ;; *std-pkg-symbols*, so we omit it (use c$::position directly in CPP code).
   '(c$::spanp
     c$::span
     c$::span-fix
     c$::make-span
     c$::span->start
     c$::span->end
     c$::irr-span
     c$::positionp
     c$::position-fix
     c$::make-position)
   ;; C$ error message utility.
   '(c$::reterr-msg)
   ;; General utilities available in CPP without qualification.
   '(bool
     defirrelevant
     defxdoc+
     enable*
     er-soft+
     erp
     impossible
     nat
     pos
     pos-fix
     reterr
     retok
     std::defret)))
