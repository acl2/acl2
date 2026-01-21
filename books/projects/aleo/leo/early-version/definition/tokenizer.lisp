; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "projects/abnf/tree-utilities" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tokenizer
  :parents (lexing-and-parsing)
  :short "Turn lexemes into tokens."
  ;; Maybe move some xdoc from filter-and-lower-tokens to here.
  :order-subtopics t
  :default-parent t)

;; Taken from filter-tokens in lexing-and-parsing.lisp
;; But changed to return the subtrees of the tokens,
;; so the top level trees will have rulenames
;; "keyword", "identifier", "atomic-literal", "numeral", or "symbol".

(define filter-and-lower-tokens ((trees abnf::tree-listp))
  :returns (token-trees abnf::tree-list-resultp
                        :hints
                        (("Goal"
                          :in-theory
                          (enable
                           abnf::treep-when-tree-resultp-and-not-reserrp
                           abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
  :short "Token filtering."
  :long
  (xdoc::topstring
   (xdoc::p
    "As formalized in @(tsee lexp),
     lexing organizes a Unicode character sequence into a sequence of lexemes.
     Comments and whitespace are discarded for parsing,
     which only applies to tokens.
     This process of discarding comments and whitespace
     is formalized via this function,
     which goes through a sequence of CSTs
     and only retains the ones for tokens.")
   (xdoc::p
    "We ignore any CST that is not a lexeme,
     but this never happens for a list of lexeme CSTs.
     We could strengthen the guard of this function
     to require lexeme CSTs."))
  (b* (((when (endp trees)) nil)
       (lexeme-tree (car trees))
       (token-tree? (abnf::check-tree-nonleaf-1-1 lexeme-tree "lexeme"))
       ;; Top level should consist solely of well-formed lexemes.
       ((when (reserrp token-tree?))
        ;; maybe should print an error message
        (reserrf (cons :tokenizing-failed token-tree?)))
       (subtoken-tree? (abnf::check-tree-nonleaf-1-1 token-tree? "token"))
       (rest-token-trees (filter-and-lower-tokens (cdr trees)))
       ((when (reserrp rest-token-trees))
        rest-token-trees))
    ;; When the lexeme is not a well-formed token, just discard it.
    ;; Potentially we could do more checking here and return a reserr if
    ;; the token is not well-formed or if it is something other than token,
    ;; comment or whitespace.
    (if (reserrp subtoken-tree?)
        rest-token-trees
      (cons subtoken-tree? rest-token-trees)))
  :hooks (:fix))
