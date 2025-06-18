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

(include-book "parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-parser
  :parents (lexing-and-parsing)
  :short "An executable parser of Leo input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to the @(see parser) of Leo (code) files,
     but it is for the Leo input files."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-input-type ((token abnf::tree-optionp)
                          (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('input-type')."
  (b* (((pok tree) (parse-type token input)))
    (mv (abnf-tree-wrap tree "input-type")
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-input-type-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-input-type-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-input-expression ((token abnf::tree-optionp)
                                (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('input-expression')."
  (b* (((pok tree) (parse-expression token input)))
    (mv (abnf-tree-wrap tree "input-expression")
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-input-expression-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-input-expression-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-input-item ((token abnf::tree-optionp)
                          (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('input-item')."
  (b* (((pok tree1) (parse-identifier token input))
       ((pok tree2) (parse-symbol ":" token input))
       ((pok tree3) (parse-input-type token input))
       ((pok tree4) (parse-symbol "=" token input))
       ((pok tree5) (parse-input-expression token input))
       ((pok tree6) (parse-symbol ";" token input))
       (tree (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "input-item")
              :branches (list (list tree1)
                              (list tree2)
                              (list tree3)
                              (list tree4)
                              (list tree5)
                              (list tree6)))))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-input-item-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-input-item-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-input-item ((token abnf::tree-optionp)
                            (input abnf::tree-listp))
  :returns
  (mv (tree abnf::tree-list-resultp
            :hints
            (("Goal"
              :in-theory
              (enable
               abnf::treep-when-tree-resultp-and-not-reserrp
               abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
      (next-token abnf::tree-optionp)
      (rest-input abnf::tree-listp))
  :short "Parse a @('*input-item')."
  (b* (((unless (token-rootp "identifier" token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       ((pok tree) (parse-input-item token input))
       ((pok trees) (parse-*-input-item token input)))
    (mv (cons tree trees) token input))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-input-item
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Temporarily not used.  See parse-public/private/constant/const/main/registers

(define parse-public/private/constants/constant/const ((token abnf::tree-optionp)
                                                       (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a
          @('( %s\"public\" / %s\"private\" / %s\"constants\" / %s\"constant\" / %s\"const\" )')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that @('private') and @('constants') are identifiers,
     while the other three are keywords."))
  (cond ((token-stringp "private" token)
         (b* (((pok tree) (parse-identifier token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "public" token)
         (b* (((pok tree) (parse-keyword "public" token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "constants" token)
         (b* (((pok tree) (parse-identifier token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "constant" token)
         (b* (((pok tree) (parse-keyword "constant" token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "const" token)
         (b* (((pok tree) (parse-keyword "const" token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        (t (mv (reserrf (list :found (abnf::tree-option-fix token)))
               (abnf::tree-option-fix token)
               (abnf::tree-list-fix input))))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-public/private/constants/constant/const-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-public/private/constants/constant/const-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This definition is temporary.  [main] and [registers] are currently
;; the section titles in the .in files, but they should be eliminated soon.

(define parse-public/private/constants/constant/const/main/registers
  ((token abnf::tree-optionp)
   (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse a
          @('( %s\"public\" / %s\"private\" / %s\"constants\" / %s\"constant\" / %s\"const\" / %s\"main\" / %s\"registers\" )')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that @('private'), @('main'), @('registers'), and @('constants') are identifiers,
     while the others are keywords."))
  (cond ((token-stringp "private" token)
         (b* (((pok tree) (parse-identifier token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "main" token)
         (b* (((pok tree) (parse-identifier token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "registers" token)
         (b* (((pok tree) (parse-identifier token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "public" token)
         (b* (((pok tree) (parse-keyword "public" token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "constants" token)
         (b* (((pok tree) (parse-identifier token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "constant" token)
         (b* (((pok tree) (parse-keyword "constant" token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        ((token-stringp "const" token)
         (b* (((pok tree) (parse-keyword "const" token input))
              (tree (abnf::make-tree-nonleaf :rulename? nil
                                             :branches (list (list tree)))))
           (mv tree token input)))
        (t (mv (reserrf (list :found (abnf::tree-option-fix token)))
               (abnf::tree-option-fix token)
               (abnf::tree-list-fix input))))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-public/private/constants/constant/const/main/registers-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-public/private/constants/constant/const/main/registers-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-input-title ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('input-title')."
  (b* (((pok tree1) (parse-symbol "[" token input))
       ((pok tree2) (parse-public/private/constants/constant/const/main/registers
                     token input))
       ((pok tree3) (parse-symbol "]" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "input-title")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)))
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-input-title-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-input-title-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-input-section ((token abnf::tree-optionp)
                             (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('input-section')."
  (b* (((pok tree) (parse-input-title token input))
       ((pok trees) (parse-*-input-item token input)))
    (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "input-section")
                                 :branches (list (list tree)
                                                 trees))
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-input-section-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-input-section-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-*-input-section ((token abnf::tree-optionp)
                               (input abnf::tree-listp))
  :returns
  (mv (tree abnf::tree-list-resultp
            :hints
            (("Goal"
              :in-theory
              (enable
               abnf::treep-when-tree-resultp-and-not-reserrp
               abnf::tree-listp-when-tree-list-resultp-and-not-reserrp))))
      (next-token abnf::tree-optionp)
      (rest-input abnf::tree-listp))
  :short "Parse a @('*input-section')."
  (b* (((unless (token-stringp "[" token))
        (mv nil
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       ((pok tree) (parse-input-section token input))
       ((pok trees) (parse-*-input-section token input)))
    (mv (cons tree trees) token input))
  :measure (parsize token input)
  :hooks (:fix)
  ///

  (defret parsize-of-parse-*-input-section
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-input-file ((input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('input-file')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function that organizes a list of tokens
     into a CST.
     We get the first token (if any),
     and then we parse zero or more declarations,
     and return an @('input-file') CST.
     If there is no error, there is no next token and no remaining input."))
  (b* (((mv token input) (parse-token input))
       ((pok trees) (parse-*-input-section token input))
       ((when (or token
                  (consp input)))
        (mv (reserrf :impossible) token input))
       (tree (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "input-file")
              :branches (list trees))))
    (mv tree nil nil))
  :hooks (:fix))
