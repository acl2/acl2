; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/fty/boolean-result" :dir :system)
(include-book "tokenizer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (concrete-syntax)
  :short "An executable parser of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple parser for Yul code.
     The main entry point is @('parse-yul')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-symbol ((symbol stringp) (tokens abnf::tree-listp))
  :returns (mv (ok? boolean-resultp) (tokens-after-symbol abnf::tree-listp))
  :short "Parses the named @('symbol')."
  :long
  (xdoc::topstring
   (xdoc::p
    "In this context, @('symbol') is a nonterminal in the ABNF grammar for Yul,
     and its alternatives are terminal symbols.
     See @('abnf-grammar-new.txt').")
   (xdoc::p
     "Parsing a symbol as a concrete syntax tree means we look for a nonleaf tree
      where the rulename is @('\"symbol\"')
      and the leafterm has the bytes of the terminal symbol."))
  (if (and (mbt (stringp symbol)) (mbt (abnf::tree-listp tokens)))
  (b* (((when (endp tokens))
        (mv (err (string-append "ran out of tokens when trying to parse symbol: " symbol))
            tokens))
       (putative-symbol-tree (first tokens))
       ((unless (and (abnf::tree-case putative-symbol-tree :nonleaf)
                     (equal (abnf::tree-nonleaf->rulename? putative-symbol-tree)
                            (abnf::rulename "symbol"))))
        (mv (err (string-append "token does not look like symbol: " symbol))
            tokens))
       (branches (abnf::tree-nonleaf->branches putative-symbol-tree))
       ((unless (and (listp branches)
                     (equal (len branches) 1)
                     (listp (car branches))
                     (equal (len (car branches)) 1)
                     (abnf::treep (caar branches))
                     (abnf::tree-case (caar branches) :leafterm)))
        (mv (err (string-append "symbol token seems to have the wrong structure for symbol:"
                                symbol))
            tokens))
       (leafterm-nats (abnf::tree-leafterm->get (caar branches)))
       ((unless (acl2::unsigned-byte-listp 8 leafterm-nats))
        (mv (err "unexpected type of leafterm nats")
            tokens))
       (terminal-symbol (acl2::nats=>string leafterm-nats))
       ((unless (equal symbol terminal-symbol))
        (mv (err (concatenate 'string "expected symbol: " symbol ", but received symbol: " terminal-symbol))
            tokens)))
    (mv t (cdr tokens)))
  ;; can't get here, but return something for logic reasons
  (mv t nil)
  ))
