; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "token-trees")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ token-tree-operations
  :parents (token-trees)
  :short "Operations on token trees."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines token-tree-wf
  :short "Well-formedness of token trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "Delimiter tokens must not appear at leaves:
     they are represented structurally, by delimited groups.
     The token-tree builder in the lexing layer
     will be proved to produce only well-formed trees."))

  (define token-tree-wfp ((tree token-treep))
    :returns (yes/no booleanp)
    :measure (token-tree-count tree)
    (token-tree-case
     tree
     :leaf (b* ((token (token+span->token tree.token)))
             (and (not (token-case token :open-delim))
                  (not (token-case token :close-delim))))
     :delimited (token-tree-list-wfp tree.trees)))

  (define token-tree-list-wfp ((trees token-tree-listp))
    :returns (yes/no booleanp)
    :measure (token-tree-list-count trees)
    (or (endp trees)
        (and (token-tree-wfp (car trees))
             (token-tree-list-wfp (cdr trees)))))

  ///

  (fty::deffixequiv-mutual token-tree-wf))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines token-tree-to-tokens
  :short "Flatten token trees back to token sequences."
  :long
  (xdoc::topstring
   (xdoc::p
    "A delimited group contributes
     its opening delimiter token,
     the tokens of its subtrees,
     and its closing delimiter token,
     reconstructed with their stored spans.
     This is the specification anchor
     for the token-tree builder in the lexing layer:
     building trees from a token sequence and flattening them
     must yield the original sequence."))

  (define token-tree->tokens ((tree token-treep))
    :returns (tokens token+span-listp)
    :measure (token-tree-count tree)
    (token-tree-case
     tree
     :leaf (list (token+span-fix tree.token))
     :delimited (append (list (make-token+span
                               :token (token-open-delim tree.delim)
                               :span tree.open-span))
                        (token-tree-list->tokens tree.trees)
                        (list (make-token+span
                               :token (token-close-delim tree.delim)
                               :span tree.close-span)))))

  (define token-tree-list->tokens ((trees token-tree-listp))
    :returns (tokens token+span-listp)
    :measure (token-tree-list-count trees)
    (if (endp trees)
        nil
      (append (token-tree->tokens (car trees))
              (token-tree-list->tokens (cdr trees)))))

  ///

  (fty::deffixequiv-mutual token-tree-to-tokens))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Basic checks: the token trees of "fn main() {}",
; well-formedness, and flattening.

(assert-event
 (b* ((fn-tok (make-token+span :token (token-keyword "fn")
                               :span (irr-span)))
      (main-tok (make-token+span :token (token-ident "main" nil)
                                 :span (irr-span)))
      (trees (list (token-tree-leaf fn-tok)
                   (token-tree-leaf main-tok)
                   (make-token-tree-delimited :delim (delim-paren)
                                              :open-span (irr-span)
                                              :trees nil
                                              :close-span (irr-span))
                   (make-token-tree-delimited :delim (delim-brace)
                                              :open-span (irr-span)
                                              :trees nil
                                              :close-span (irr-span)))))
   (and (token-tree-listp trees)
        (token-tree-list-wfp trees)
        (equal (len (token-tree-list->tokens trees)) 6))))

(assert-event ; a delimiter token at a leaf is not well-formed
 (not (token-tree-wfp
       (token-tree-leaf (make-token+span
                         :token (token-open-delim (delim-paren))
                         :span (irr-span))))))
