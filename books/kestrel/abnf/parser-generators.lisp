; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "parsing-primitives-defresult")

(include-book "kestrel/fty/pos-list" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-generators
  :parents (abnf)
  :short "Tools to generate parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide tools to generate parsing functions from ABNF grammar rules.
     This is not a full parser generator, but it a start towards one."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines def-parse-printing
  :short "Pretty-print ABNF
          elements, alternations, concatenations, and repetitions
          to ACL2 strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to generate portions of documentation strings.
     Not all the elements are supported."))

  (define def-parse-print-element ((elem elementp))
    :returns (string acl2::stringp)
    (element-case
     elem
     :rulename (rulename->get elem.get)
     :group (str::cat "( " (def-parse-print-alternation elem.get) " )")
     :option (str::cat "[ " (def-parse-print-alternation elem.get) " ]")
     :char-val (char-val-case
                elem.get
                :insensitive (str::cat
                              "\""
                              (char-val-insensitive->get elem.get)
                              "\"")
                :sensitive (str::cat
                            "%s\""
                            (char-val-sensitive->get elem.get)
                            "\""))
     :num-val (prog2$ (raise "Printing of ~x0 not supported." elem.get) "")
     :prose-val (prog2$ (raise "Printing of ~x0 not supported." elem.get) ""))
    :measure (element-count elem))

  (define def-parse-print-alternation ((alt alternationp))
    :returns (string acl2::stringp)
    (cond ((endp alt) "")
          ((endp (cdr alt)) (def-parse-print-concatenation (car alt)))
          (t (str::cat (def-parse-print-concatenation (car alt))
                       " / "
                       (def-parse-print-alternation (cdr alt)))))
    :measure (alternation-count alt))

  (define def-parse-print-concatenation ((conc concatenationp))
    :returns (string acl2::stringp)
    (cond ((endp conc) "")
          ((endp (cdr conc)) (def-parse-print-repetition (car conc)))
          (t (str::cat (def-parse-print-repetition (car conc))
                       " "
                       (def-parse-print-concatenation (cdr conc)))))
    :measure (concatenation-count conc))

  (define def-parse-print-repetition ((rep repetitionp))
    :returns (string acl2::stringp)
    (b* (((repetition rep) rep)
         ((repeat-range range) rep.range)
         ((when (and (equal range.min 1)
                     (equal range.max (nati-infinity))))
          (def-parse-print-element rep.element))
         ((when (equal range.max
                       (nati-finite range.min)))
          (str::cat (str::natstr range.min)
                    (def-parse-print-element rep.element))))
      (str::cat (if (equal range.min 0)
                    ""
                  (str::natstr range.min))
                "*"
                (if (nati-case range.max :infinity)
                    ""
                  (str::natstr (nati-finite->get range.max)))
                (def-parse-print-element rep.element)))
    :measure (repetition-count rep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist alternation-symbol-alist
  :short "Fixtype of alists from ABNF groups to ACL2 symbols."
  :key-type alternation
  :val-type acl2::symbol
  :true-listp t
  :pred alternation-symbol-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist repetition-symbol-alist
  :short "Fixtype of alists from ABNF repetitions to ACL2 symbols."
  :key-type repetition
  :val-type acl2::symbol
  :true-listp t
  :pred repetition-symbol-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-code-for-element ((elem elementp)
                                        (check-error-p booleanp)
                                        (group-fns alternation-symbol-alistp)
                                        (option-fns alternation-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF element."
  (element-case
   elem
   :num-val
   (num-val-case
    elem.get
    :direct `(((mv tree input)
               (parse-direct (list ,@(num-val-direct->get elem.get))
                             input))
              ,@(and check-error-p
                     '(((when (resulterrp tree)) (mv (err-push tree) input)))))
    :range `(((mv tree input)
              (parse-range ,(num-val-range->min elem.get)
                           ,(num-val-range->max elem.get)
                           input))
             ,@(and check-error-p
                    '(((when (resulterrp tree)) (mv (err-push tree) input))))))
   :char-val
   (char-val-case
    elem.get
    :insensitive `(((mv tree input)
                    (parse-ichars ,(char-val-insensitive->get elem.get)
                                  input))
                   ,@(and
                      check-error-p
                      '(((when (resulterrp tree)) (mv (err-push tree) input)))))
    :sensitive `(((mv tree input)
                  (parse-schars ,(char-val-sensitive->get elem.get)
                                input))
                 ,@(and
                    check-error-p
                    '(((when (resulterrp tree)) (mv (err-push tree) input))))))
   :rulename (b* ((parse-rulename-fn
                   (add-suffix 'parse- (str::upcase-string
                                        (rulename->get elem.get)))))
               `(((mv tree input) (,parse-rulename-fn input))
                 ,@(and
                    check-error-p
                    '(((when (resulterrp tree)) (mv (err-push tree) input))))))
   :group (b* ((parse-group-fn (cdr (assoc-equal elem.get group-fns))))
            `(((mv tree input) (,parse-group-fn input))
              ,@(and
                 check-error-p
                 '(((when (resulterrp tree)) (mv (err-push tree) input))))))
   :option (b* ((parse-option-fn (cdr (assoc-equal elem.get option-fns))))
             `(((mv tree input) (,parse-option-fn input))
               ,@(and
                  check-error-p
                  '(((when (resulterrp tree)) (mv (err-push tree) input))))))
   :prose-val (raise "Prose value ~x0 not supported." elem.get)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-code-for-repetition
  ((rep repetitionp)
   (index natp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (mv (code true-listp)
               (var acl2::symbolp))
  :short "Generate code to parse an instance of an ABNF repetition."
  (b* ((trees-index (add-suffix 'trees (str::natstr index)))
       (parse-repetition-fn? (cdr (assoc-equal rep repetition-fns)))
       ((when parse-repetition-fn?)
        (mv `(((mv ,trees-index input) (,parse-repetition-fn? input))
              ((when (resulterrp ,trees-index))
               (mv (err-push ,trees-index) input)))
            trees-index))
       ((repetition rep) rep)
       ((when (equal rep.range
                     (make-repeat-range :min 1
                                        :max (nati-finite 1))))
        (mv `(,@(def-parse-gen-code-for-element
                  rep.element t group-fns option-fns)
              (,trees-index (list tree)))
            trees-index)))
    (prog2$ (raise "Repetition ~x0 not supported yet." rep)
            (mv nil nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-code-for-concatenation
  ((conc concatenationp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF concatenation."
  (b* (((when (endp conc)) (raise "Empty concatenation."))
       ((mv code vars) (def-parse-gen-code-for-concatenation-aux
                         conc 1 group-fns option-fns repetition-fns)))
    `(,@code
      (treess (list ,@vars))))
  :prepwork
  ((define def-parse-gen-code-for-concatenation-aux
     ((conc concatenationp)
      (index natp)
      (group-fns alternation-symbol-alistp)
      (option-fns alternation-symbol-alistp)
      (repetition-fns repetition-symbol-alistp))
     :returns (mv (code true-listp)
                  (vars acl2::symbol-listp))
     :parents nil
     (b* (((when (endp conc)) (mv nil nil))
          ((mv code1 var) (def-parse-gen-code-for-repetition
                            (car conc)
                            index
                            group-fns
                            option-fns
                            repetition-fns))
          ((mv code2 vars) (def-parse-gen-code-for-concatenation-aux
                             (cdr conc)
                             (1+ index)
                             group-fns
                             option-fns
                             repetition-fns)))
       (mv (append code1 code2) (cons var vars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-reorder-alternation ((alt alternationp)
                                       (order pos-listp))
  :returns (new-alt alternationp)
  :short "Reorder the alternatives of an alternation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('order') list must be  a permutation of the list @('(1 ... n)'),
     where @('n') is the number of alternatives in @('alt').
     We returns the alternative, permuted according to the list.")
   (xdoc::p
    "This serves to try an alternative before another one,
     in order to satisfy extra-grammatical requiremens."))
  (b* (((when (endp order)) nil)
       (index (1- (car order)))
       ((unless (< index (len alt)))
        (raise "Bad position ~x0 in ~x1." (car order) alt)))
    (cons (concatenation-fix (nth index alt))
          (def-parse-reorder-alternation alt (cdr order)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-order-permutationp ((order pos-listp))
  :returns (yes/no booleanp)
  :short "Check if an @('order') parameter is a valid permutation."
  (def-parse-order-permutationp-aux order (integers-from-to 1 (len order)))
  :guard-hints (("Goal" :in-theory (enable integers-from-to)))
  :prepwork
  ((define def-parse-order-permutationp-aux ((a pos-listp) (b pos-listp))
     :returns (yes/no booleanp)
     (cond ((endp a) (endp b))
           (t (and (member (car a) b)
                   (def-parse-order-permutationp-aux
                     (cdr a)
                     (remove1 (car a) b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-code-for-alternation
  ((alt alternationp)
   (order pos-listp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF alternation."
  (b* (((when (endp alt)) (raise "Empty alternation."))
       ((unless (and (= (len order) (len alt))
                     (def-parse-order-permutationp order)))
        (raise "Bad permutation ~x0." order))
       (alt (def-parse-reorder-alternation alt order))
       ((mv code vars) (def-parse-gen-code-for-alternation-aux
                         alt 1 group-fns option-fns repetition-fns)))
    `(b* (,@code)
       (mv (err (list :found (list ,@vars) :required ',alt)) input)))
  :prepwork
  ((define def-parse-gen-code-for-alternation-aux
     ((alt alternationp)
      (index natp)
      (group-fns alternation-symbol-alistp)
      (option-fns alternation-symbol-alistp)
      (repetition-fns repetition-symbol-alistp))
     :returns (mv (code true-listp)
                  (vars acl2::symbol-listp))
     :parents nil
     (b* (((when (endp alt)) (mv nil nil))
          (treess-index (add-suffix 'treess (str::natstr index)))
          (code `(((mv ,treess-index input1)
                   (b* (,@(def-parse-gen-code-for-concatenation
                            (car alt) group-fns option-fns repetition-fns))
                     (mv treess input)))
                  ((when (not (resulterrp ,treess-index)))
                   (mv ,treess-index input1))))
          ((mv more-code vars)
           (def-parse-gen-code-for-alternation-aux
             (cdr alt) (1+ index) group-fns option-fns repetition-fns)))
       (mv (append code more-code) (cons treess-index vars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum def-parse-function-spec
  :short "Fixtype of specifications of parsing functions."
  (:rulename ((get acl2::stringp)
              (order pos-list)))
  (:group ((get alternation)
           (order pos-list)))
  (:option ((get alternation)
            (order pos-list)))
  (:repetition ((get repetition))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-function-for-rulename
  ((rulename acl2::stringp)
   (order pos-listp)
   (grammar rulelistp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for a rule name."
  (b* ((parse-rulename  (add-suffix 'parse- (str::upcase-string rulename)))
       (alt (lookup-rulename (rulename rulename) grammar))
       (order (or order (integers-from-to 1 (len alt)))))
    `(define ,parse-rulename ((input nat-listp))
       :returns (mv (tree tree-resultp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('" rulename "').")
       (b* (((mv treess input)
             ,(def-parse-gen-code-for-alternation
                alt order group-fns option-fns repetition-fns))
            ((when (resulterrp treess))
             (mv (err-push treess) (nat-list-fix input))))
         (mv (make-tree-nonleaf :rulename? (rulename ,rulename)
                                :branches treess)
             input))
       :hooks (:fix)
       ///
       (defret ,(acl2::packn-pos (list 'len-of- parse-rulename '-<=)
                                 parse-rulename)
         (<= (len rest-input)
             (len input))
         :rule-classes :linear)
       (defret ,(acl2::packn-pos (list 'len-of- parse-rulename '-<)
                                 parse-rulename)
         (implies (not (resulterrp tree))
                  (< (len rest-input)
                     (len input)))
         :rule-classes :linear))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-function-for-group
  ((alt alternationp)
   (order pos-listp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for an ABNF group."
  (b* ((parse-group (cdr (assoc-equal alt group-fns)))
       (order (or order (integers-from-to 1 (len alt)))))
    `(define ,parse-group ((input nat-listp))
       :returns (mv (tree tree-resultp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('"
                         (def-parse-print-element (element-group alt))
                         "').")
       (b* (((mv treess input)
             ,(def-parse-gen-code-for-alternation
                alt order group-fns option-fns repetition-fns))
            ((when (resulterrp treess))
             (mv (err-push treess) (nat-list-fix input))))
         (mv (make-tree-nonleaf :rulename? nil
                                :branches treess)
             input))
       :hooks (:fix)
       ///
       (defret ,(acl2::packn-pos (list 'len-of- parse-group '-<=)
                                 parse-group)
         (<= (len rest-input)
             (len input))
         :rule-classes :linear)
       (defret ,(acl2::packn-pos (list 'len-of- parse-group '-<)
                                 parse-group)
         (implies (not (resulterrp tree))
                  (< (len rest-input)
                     (len input)))
         :rule-classes :linear))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-function-for-option
  ((alt alternationp)
   (order pos-listp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for an ABNF option."
  (b* ((parse-option (cdr (assoc-equal alt option-fns)))
       (order (or order (integers-from-to 1 (len alt)))))
    `(define ,parse-option ((input nat-listp))
       :returns (mv (tree tree-resultp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('"
                         (def-parse-print-element (element-option alt))
                         "').")
       (b* (((mv treess input)
             ,(def-parse-gen-code-for-alternation
                alt order group-fns option-fns repetition-fns))
            ((when (resulterrp treess))
             (mv (make-tree-nonleaf
                  :rulename? nil
                  :branches nil)
                 (nat-list-fix input))))
         (mv (make-tree-nonleaf :rulename? nil
                                :branches treess)
             input))
       :hooks (:fix)
       ///
       (defret ,(acl2::packn-pos (list 'len-of- parse-option '-<=)
                                 parse-option)
         (<= (len rest-input)
             (len input))
         :rule-classes :linear))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-function-for-repetition
  ((rep repetitionp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event acl2::maybe-pseudo-event-formp)
  :short "Generate a parsing function for an ABNF repetition."
  (b* ((parse-repetition (cdr (assoc-equal rep repetition-fns)))
       ((repetition rep) rep)
       ((unless (equal rep.range
                       (make-repeat-range :min 0
                                          :max (nati-infinity))))
        (raise "Repetition ~x0 currently not supported." rep)))
    `(define ,parse-repetition ((input nat-listp))
       :returns (mv (trees tree-listp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('" (def-parse-print-repetition rep) "').")
       (b* (,@(def-parse-gen-code-for-element
                rep.element nil group-fns option-fns)
            ((when (resulterrp tree)) (mv nil input))
            ((mv trees input) (,parse-repetition input)))
         (mv (cons tree trees) input))
       :hooks (:fix)
       :measure (len input)
       ///
       (defret ,(acl2::packn-pos (list 'len-of- parse-repetition)
                                 parse-repetition)
         (<= (len rest-input)
             (len input))
         :rule-classes :linear))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-function-for-spec
  ((spec def-parse-function-spec-p)
   (grammar rulelistp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event acl2::maybe-pseudo-event-formp)
  :short "Generate a parsing function for a specification."
  (def-parse-function-spec-case
    spec
    :rulename (def-parse-gen-function-for-rulename
                spec.get spec.order grammar group-fns option-fns repetition-fns)
    :group (def-parse-gen-function-for-group
             spec.get spec.order group-fns option-fns repetition-fns)
    :option (def-parse-gen-function-for-option
              spec.get spec.order group-fns option-fns repetition-fns)
    :repetition (def-parse-gen-function-for-repetition
                  spec.get group-fns option-fns repetition-fns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-parse-single (spec)
  :short "Define a single parsing function for a specification."
  `(make-event (def-parse-gen-function-for-spec
                 ,spec
                 *grammar*
                 *parse-group-fns*
                 *parse-option-fns*
                 *parse-repetition-fns*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-parse-rulename (rulename &key order)
  :short "Define a single parsing function for an ABNF rule name,
          with an optional reordering of the alternatives."
  `(def-parse-single (def-parse-function-spec-rulename ,rulename ',order)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-parse-*-rulename (rulename)
  :short "Define a single parsing function for
          a @('*') repetition of an ABNF rule name."
  `(def-parse-single (def-parse-function-spec-repetition
                       (make-repetition
                        :element (element-rulename
                                  (rulename ,rulename))
                        :range (make-repeat-range
                                :min 0
                                :max (nati-infinity))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-parse-group (alt &key order)
  :short "Define a single parsing function for an ABNF group,
          with an optional reordering of the alternatives."
  `(def-parse-single (def-parse-function-spec-group ,alt ',order)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-parse-*-group (alt)
  :short "Define a single parsing function for
          a @('*') repetition of an ABNF group."
  `(def-parse-single (def-parse-function-spec-repetition
                       (make-repetition
                        :element (element-group ,alt)
                        :range (make-repeat-range
                                :min 0
                                :max (nati-infinity))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-parse-option (alt &key order)
  :short "Define a single parsing function for an ABNF option,
          with an optional reordering of the alternatives."
  `(def-parse-single (def-parse-function-spec-option ,alt ',order)))
