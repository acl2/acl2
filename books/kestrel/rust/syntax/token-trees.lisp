; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "tokens")

(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ token-trees
  :parents (syntax-for-tools)
  :short "Rust token trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "A token tree is either a single token
     or a group of token trees
     enclosed in matched delimiters
     ["
    (xdoc::ahref "https://doc.rust-lang.org/1.87.0/reference/macros.html"
                 "Reference: Macros")
    "].
     Token trees are the level at which macros operate:
     a macro invocation's argument is a token tree sequence,
     left unparsed until macro expansion,
     and @('macro_rules!') matchers and transcribers
     are defined over token trees.
     Accordingly, the lexing layer produces token trees
     (by matching delimiters in the token sequence),
     and the parser consumes them.")
   (xdoc::p
    "Delimiter tokens themselves do not appear as leaves:
     a matched pair becomes a delimited group,
     whose fixtype stores the delimiter kind
     and the spans of the opening and closing delimiter tokens,
     so that the original token sequence
     is exactly recoverable (see @(tsee token-tree->tokens)).
     Leaves store tokens with their spans.
     The absence of delimiter tokens at leaves
     is a well-formedness condition (see @(tsee token-tree-wfp)),
     not built into the fixtype."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes token-trees
  :short "Fixtypes of token trees and lists thereof."

  (fty::deftagsum token-tree
    :short "Fixtype of token trees."
    :long
    (xdoc::topstring
     (xdoc::p
      "A leaf is a token (with span);
       a delimited group is a delimiter kind,
       the spans of the opening and closing delimiter tokens,
       and the token trees between them."))
    (:leaf ((token token+span)))
    (:delimited ((delim delim)
                 (open-span span)
                 (trees token-tree-list)
                 (close-span span)))
    :pred token-treep
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist token-tree-list
    :short "Fixtype of lists of token trees."
    :elt-type token-tree
    :true-listp t
    :elementp-of-nil nil
    :pred token-tree-listp
    :measure (two-nats-measure (acl2-count x) 1)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-token-tree
  :short "An irrelevant token tree."
  :type token-treep
  :body (token-tree-leaf (irr-token+span)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Basic structural check: the token trees of "fn main() {}".
; (Operations on token trees, with their own tests,
; are in token-tree-operations.lisp.)

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
   (token-tree-listp trees)))
