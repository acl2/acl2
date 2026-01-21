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

(defxdoc+ output-parser
  :parents (lexing-and-parsing)
  :short "An executable parser of Leo output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to the "
    (xdoc::seetopic "parser" "parser of Leo (code) files")
    " and the "
    (xdoc::seetopic "input-parser" "parser of Leo input files")
    ", but it is for the Leo output files."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-output-expression ((token abnf::tree-optionp)
                                 (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('output-expression')."
  (b* (((pok tree) (parse-expression token input)))
    (mv (abnf-tree-wrap tree "output-expression")
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-output-expression-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-output-expression-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-output-item ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('output-item')."
  (b* (((pok tree1) (parse-output-expression token input))
       ((pok tree2) (parse-symbol ";" token input))
       (tree (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "output-item")
              :branches (list (list tree1)
                              (list tree2)))))
    (mv tree token input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-output-item-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-output-item-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-output-title ((token abnf::tree-optionp)
                            (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('output-title')."
  (b* (((pok tree1) (parse-symbol "[" token input))
       ((unless (token-stringp "output" token))
        (mv (reserrf (list :found (abnf::tree-option-fix token)))
            (abnf::tree-option-fix token)
            (abnf::tree-list-fix input)))
       ((pok tree2) (parse-identifier token input))
       ((pok tree3) (parse-symbol "]" token input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "output-title")
         :branches (list (list tree1)
                         (list tree2)
                         (list tree3)))
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-output-title-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-output-title-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-output-section ((token abnf::tree-optionp)
                              (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('output-section')."
  (b* (((pok tree1) (parse-output-title token input))
       ((pok tree2) (parse-output-item token input)))
    (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "output-section")
                                 :branches (list (list tree1)
                                                 (list tree2)))
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-output-section-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear)

  (defret parsize-of-parse-output-section-<
    (implies (not (reserrp tree))
             (< (parsize next-token rest-input)
                (parsize token input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-output-file ((token abnf::tree-optionp)
                           (input abnf::tree-listp))
  :returns (mv (tree abnf::tree-resultp)
               (next-token abnf::tree-optionp)
               (rest-input abnf::tree-listp))
  :short "Parse an @('output-file')."
  (b* (((pok tree) (parse-output-section token input)))
    (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "output-file")
                                 :branches (list (list tree)))
        token
        input))
  :hooks (:fix)
  ///

  (defret parsize-of-parse-output-file-<=
    (<= (parsize next-token rest-input)
        (parsize token input))
    :rule-classes :linear))
