; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "lexer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tokenizer
  :parents (concrete-syntax)
  :short "An executable tokenizer of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple tokenizer for Yul code.  The tokenizer simply lexes and
     then discards comments and whitespace.")
   (xdoc::p
    "The primary API for tokenizing is
     @(see tokenize-yul) and @(see tokenize-yul-bytes)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Predicate on top level CST (concrete syntax tree) structure.

(define is-tree-rulename? ((tree abnf::treep) (rulename-string stringp))
  :returns (yes/no booleanp)
  :short "True if tree is nonleaf for rule @('rulename-string')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Does not details of the internal structure."))
  (and (abnf::treep tree)
       (abnf::tree-case tree :nonleaf)
       (equal (abnf::tree-nonleaf->rulename? tree) (abnf::rulename rulename-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Filtering out non-token lexemes and reducing the levels of tree structure.

;; These next two definitions are essentially the same but
;; I want to have different error messages.
;; But they could be replaced by something like:
;;   (define check-and-deref-tree-of-rule-with-single-subtree ((tree abnf::treep) (rule abnf::rulenamep)) ..)

;; lexeme = token / comment / whitespace
(define check-and-deref-tree-lexeme? ((tree abnf::treep))
  :returns (subtree abnf::tree-resultp)
  :short "Check if the ABNF tree is a nonleaf for rule \"lexeme\",
          extracting its component tree (token, comment, or whitespace) if successful.
          If not successful, returns a reserrp."
  (b* (((unless (abnf::tree-case tree :nonleaf))
        (reserrf "should be lexeme tree, but is not a nonleaf"))
       (rulename? (abnf::tree-nonleaf->rulename? tree))
       ((unless (equal rulename? (abnf::rulename "lexeme")))
        (reserrf "tree should have rulename lexeme, but does not"))
       (branches (abnf::tree-nonleaf->branches tree))
       ;; Branches is a concatenation of repetitions.
       ;; Here, the concatenation should have exactly one item.
       ((unless (equal (len branches) 1))
        (reserrf "lexeme tree branches should have exactly one list"))
       (repetition (car branches))
       ;; Repetition is a list of subtrees.
       ;; Here, the repetition should have exactly one item
       ;; (which is the token, comment or whitespace subtree
       ;; but we don't check that here).
       ((unless (equal (len repetition) 1))
        (reserrf "lexeme repetition should have exactly one subtree"))
       ;; This should never happen, but check to make sure
       ;; item returned is a tree.
       ((unless (abnf::treep (car repetition)))
        (reserrf "lexeme repetition item should be an ABNF tree")))
    (car repetition)))

;; token = keyword / literal / identifier / symbol
(define check-and-deref-tree-token? ((tree abnf::treep))
  :returns (subtree abnf::tree-resultp)
  :short "Check if the ABNF tree is a nonleaf for rule \"token\",
          extracting its component tree (keyword, literal, identifier, or symbol) if successful.
          If it is not successful, returns a reserrp."
  (b* (((unless (abnf::tree-case tree :nonleaf))
        (reserrf "should be token tree, but is not a nonleaf"))
       (rulename? (abnf::tree-nonleaf->rulename? tree))
       ((unless (equal rulename? (abnf::rulename "token")))
        (reserrf "tree should have rulename token, but does not"))
       (branches (abnf::tree-nonleaf->branches tree))
       ;; Branches is a concatenation of repetitions.
       ;; Here, the concatenation should have exactly one item.
       ((unless (equal (len branches) 1))
        (reserrf "token tree branches should have exactly one list"))
       (repetition (car branches))
       ;; Repetition is a list of subtrees.
       ;; Here, the repetition should have exactly one item
       ;; (which is the keyword, literal, identifier, or symbol)
       ;; but we don't check that here).
       ((unless (equal (len repetition) 1))
        (reserrf "token repetition should have exactly one subtree"))
       ;; This should never happen, but check to make sure
       ;; item returned is a tree.
       ((unless (abnf::treep (car repetition)))
        (reserrf "token repetition item should be an ABNF tree")))
    (car repetition)))

(define filter-and-reduce-lexeme-tree-to-subtoken-trees ((trees abnf::tree-listp))
  :returns (subtoken-trees abnf::tree-list-resultp)
  :short "Sees through lexeme and token rules to return a list of keyword, literal, identifier, and symbol trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "Discards without error trees other than \"token\" under \"lexeme\".
     However, if the structure under lexeme or token is incorrect, returns reserrp."))
  ;; We need a separate check of the guard for logic mode to work
  (if (mbt (abnf::tree-listp trees)) ; otherwise just returns nil
      (b* (((when (endp trees)) nil)
            (first-tree (car trees))
            (rest-trees (cdr trees))
            (first-tree-under-lexeme (check-and-deref-tree-lexeme? first-tree))
            ((when (reserrp first-tree-under-lexeme))
             (reserrf "bad structure under lexeme"))
            (processed-rest-trees (filter-and-reduce-lexeme-tree-to-subtoken-trees rest-trees))
            ((when (reserrp processed-rest-trees))
             (reserrf "bad structure under lexeme"))
            ;; this can't happen, but it is helpful for the return type proof
            ((unless (abnf::tree-listp processed-rest-trees))
             (reserrf "type error that should not happen"))
            ;; if it is not a token, it is a whitespace or comment, so just return the rest
            ((unless (is-tree-rulename? first-tree-under-lexeme "token"))
             processed-rest-trees)
            (first-tree-under-token (check-and-deref-tree-token? first-tree-under-lexeme))
            ((when (reserrp first-tree-under-token))
             (reserrf "bad structure under token"))
            ;; this can't happen, but is helpful for the return type proof
            ((unless (abnf::treep first-tree-under-token))
             (reserrf "type error that should not happen 2")))
        (cons first-tree-under-token
              processed-rest-trees))
    ;; can't get here, but return '() for logic reasons
    '()))

(define tokenize-yul ((yul-string stringp))
  :returns (yul-lexemes abnf::tree-list-resultp)
  :short "Lexes the bytes of @('yul-string') into a list of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "The returned trees are for rulenames @('keyword'), @('literal'), @('identifier'), or @('symbol').
     Each token is represented by an @(see abnf::tree).
     Discards comments and whitespace.  If the input structure from any lexeme
     down to the specific token type is incorrect, returns an error result value of type
     @(see fty::reserr) instead of a list of tokens.
     Also, if the input string ends in the middle of a token, returns @('reserr')."))
  (b* (((mv erp lexeme-trees) (lexemeize-yul yul-string))
       ((when erp) (reserrf "problem lexing yul-string"))
       (subtoken-trees (filter-and-reduce-lexeme-tree-to-subtoken-trees lexeme-trees))
       ((when (reserrp subtoken-trees))
        (reserrf "problem with structure of lexeme tree")))
    subtoken-trees))

;; A variation on tokenize-yul that takes a list of bytes
(define tokenize-yul-bytes ((yul-bytes nat-listp))
  :returns (yul-lexemes abnf::tree-list-resultp)
  :short "Lexes the bytes of a Yul source program into a list of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does the same thing as @(see tokenize-yul), but does not need to
convert the string to bytes first."))
  (b* (((mv erp lexeme-trees) (lexemeize-yul-bytes yul-bytes))
       ((when erp) (reserrf "problem lexing yul-bytes"))
       (subtoken-trees (filter-and-reduce-lexeme-tree-to-subtoken-trees lexeme-trees))
       ((when (reserrp subtoken-trees))
        (reserrf "problem with structure of lexeme tree")))
    subtoken-trees))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; example

(defun subtoken-treep (tree)
  (or (is-tree-rulename? tree "keyword")
      (is-tree-rulename? tree "literal")
      (is-tree-rulename? tree "identifier")
      (is-tree-rulename? tree "symbol")))

(defun subtoken-tree-listp (tl)
  (if (endp tl)
      t
    (and (subtoken-treep (car tl))
         (subtoken-tree-listp (cdr tl)))))

(assert-event
 (let ((subtoken-trees
(tokenize-yul "{
    function power(base, exponent) -> result
    {
        switch exponent
        case 0 { result := 1 }
        case 1 { result := base }
        default
        {
            result := power(mul(base, base), div(exponent, 2))
            switch mod(exponent, 2)
                case 1 { result := mul(base, result) }
        }
    }
}
")))
  (and (not (reserrp subtoken-trees))
       (subtoken-tree-listp subtoken-trees))))
