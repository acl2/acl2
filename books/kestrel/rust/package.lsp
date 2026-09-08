; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The "RUST" package is for the formalization of (subsets of) Rust:
; abstract syntax with static and dynamic semantics, through MIR
; and its interpreter.
; The "RUST$" package (see syntax/package.lsp) is for the tool-oriented
; syntax (lexer, parser, printer); the two-package convention follows
; the C library (see :DOC C$::SYNTAX-FOR-TOOLS).

(defpkg "RUST" (append
                (set-difference-eq *std-pkg-symbols*
                                   '(block
                                     break
                                     error
                                     loop
                                     pi
                                     type
                                     typep
                                     union
                                     value
                                     values))
                '(any
                  bool
                  char-fix
                  cw-event
                  define-sk
                  defirrelevant
                  defmacro+
                  defxdoc+
                  enable*
                  erp
                  impossible
                  keyword-listp
                  lifix
                  lnfix
                  lposfix
                  make-event-terse
                  maybe-msgp
                  msg$
                  nat
                  nat-list
                  nat-list-fix
                  nat-optionp
                  packn-pos
                  pos
                  pos-fix
                  pseudo-event-formp
                  pseudo-event-form-listp
                  reterr
                  retmsg$
                  retok
                  string-optionp
                  table-alist+)))
