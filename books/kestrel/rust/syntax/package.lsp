; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/rust/portcullis" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The "RUST$" package is for the tool-oriented Rust syntax:
; lexer, token trees, parser, abstract syntax for tools, printer.
; The "$" suffix follows the convention proposed in the C library
; (see :DOC C$::SYNTAX-FOR-TOOLS).
; The "RUST" package (see ../package.lsp) is for the language formalization.

(defpkg "RUST$" (append
                 (set-difference-eq *std-pkg-symbols*
                                    '(block
                                      break
                                      error
                                      loop
                                      newline
                                      position
                                      pprint-newline
                                      read-byte
                                      read-char
                                      type
                                      typep
                                      union
                                      unread-char
                                      value
                                      values))
                 '(any
                   assert!-stobj
                   bool
                   bool-fix
                   bytep
                   byte-list
                   byte-listp
                   byte-list-fix
                   char-fix
                   character-list
                   define-sk
                   defirrelevant
                   defmacro+
                   defxdoc+
                   enable*
                   prefixp
                   string=>nats
                   er-soft+
                   erp
                   impossible
                   keyword-listp
                   keyword-value-list-to-alist
                   lifix
                   lnfix
                   lposfix
                   make-event-terse
                   maybe-msgp
                   msg$
                   nat
                   nat-list
                   nat-list-fix
                   nat-option
                   nat-optionp
                   nat-option-fix
                   nat-list-measure
                   nats=>string
                   packn-pos
                   pos
                   pos-fix
                   pos-option
                   pos-optionp
                   pseudo-event-formp
                   pseudo-event-form-listp
                   reterr
                   retmsg$
                   retok
                   fty::reserr
                   fty::reserrp
                   fty::reserrf
                   fty::reserrf-push
                   fty::reserr-optionp
                   string-optionp
                   table-alist+
                   unsigned-byte-listp
                   std::defret-mutual
                   str::bin-digit-char
                   str::bin-digit-char-p
                   str::bin-digit-char-list
                   str::bin-digit-char-listp
                   str::dec-digit-char
                   str::dec-digit-char-p
                   str::dec-digit-char-list
                   str::dec-digit-char-listp
                   str::hex-digit-char
                   str::hex-digit-char-p
                   str::hex-digit-char-list
                   str::hex-digit-char-listp
                   str::oct-digit-char
                   str::oct-digit-char-p
                   str::oct-digit-char-list
                   str::oct-digit-char-listp
                   str::str-fix
                   str::string-list
                   str::string-list-fix)))
