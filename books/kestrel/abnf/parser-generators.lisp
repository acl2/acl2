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
     This is not a full parser generator, but it is a start towards one.")
   (xdoc::p
    "The ABNF grammar of interest must be in an ACL2 named constant called
     @('abnf::*def-parse-grammar*')
     (note that it is in the @('\"ABNF\"') package).
     This constant is implicitly referenced by the parsing generation macros.
     If the grammar is in a differently named constant,
     it is easy to define the required constant to be equal to that one.
     This restriction may be lifted in the future,
     to allow any user-specified named constant.")
   (xdoc::p
    "The macro @(tsee def-parse-rulename) is used to generate
     a parsing function for the specified rule name,
     which is passed as an ACL2 string (not as a @(tsee rulename)).
     If the rule name is @('<R>'),
     the parsing function is called @('<parse>-<R>'),
     where @('<parse>') is a symbol that must be
     the value of a named constant called @('abnf::*def-parse-fn-name*'):
     for example, this could be
     the symbol @('parse') for a parser, or @('lex') for a lexer.
     The @(tsee def-parse-rulename) macro
     looks up the grammar rule(s) for @('<R>') in the grammar
     collecting the alternation that defines the rule name
     (including any incremental rule).
     The generated function attempts to parse each alternative in order,
     backtracking if the parsing of an alternative fails,
     stopping when either the parsing of an alternative succeeds
     or there are no more alternatives (in which case parsing fails).
     The macro @(tsee def-parse-rulename) also takes a keyword argument
     to optionally specify a reordering of the alternatives:
     the value of this argument must be a permutation of @('(1 2 ... n)')
     where @('n') is the number of alternatives that define @('<R>').
     The reordering is useful to enforce extra-grammatical requirements
     that provide disambiguation (e.g. parse the longest parsable text),
     or for greater efficiency (e.g. parse the more common alternative first).")
   (xdoc::p
    "The generated @('<parse>-<R>') function attempts to parse each alternative,
     which is a concatenation of repetitions,
     by attempting to parse the repetitions in order.
     Repetitions are often singletons, i.e. they are effectively elements:
     in this case, @('<parse>-<R>') directly attempts to parse the element.
     An element may be a rule name @('<S>'),
     in which case the corresponding @('<parse>-<S>') function is called,
     whose name is known because it is derived from @('<S>')
     similarly to how the name of @('<parse>-<R>') is derived from @('<R>').
     For elements that are groups or options,
     or for repetitions that are not singletons,
     the name of the corresponding parsing function
     must be specified by the user.
     This is done via three ACL2 named constants called
     @('abnf::*def-parse-group-fns*'),
     @('abnf::*def-parse-option-fns*'), and
     @('abnf::*def-parse-repetition-fns*')
     (note that they are in the @('\"ABNF\"') package).
     These are alists from groups or options or repetitions,
     represented as ABNF abstract syntax
     (i.e. values of type @(tsee alternation) for groups and options,
     and values of type @(tsee repetition) for repetitions)
     to symbols that are the names of the corresponding parsing functions.
     These three constants are implicitly referenced
     by the parsing generation macros.
     Future extensions of these parser generation tools
     may allow user-defined names for these constants.
     Future extensions of these parser generation tools
     may also automate the generation of these function names.")
   (xdoc::p
    "The @(tsee def-parse-*-rulename) macro generates a parsing function for
     a repetition of zero or more instances of the specified rule name.
     It uses @('abnf::*def-parse-repetition-fns*') to retrieve
     the name of the parsing function to generate.
     If the rule name is @('<R>'),
     the generated function calls @('<parse>-<R>')
     for as long as that succeeds.")
   (xdoc::p
    "The @(tsee def-parse-group) macro is similar to @(tsee def-parse-rulename),
     but it retrieves the name of the function to generate
     from @('abnf::*def-parse-group-fns*');
     the macro takes the group as an argument,
     which is used as a key in the alist.
     It attempts to parse each alternative,
     in the order in which the alternatives appear in the group,
     unless a reordering keyword argument is passed,
     which works in the same way as in @(tsee def-parse-rulename).")
   (xdoc::p
    "The @(tsee def-parse-*-group) macros
     is similar to @(tsee def-parse-*-rulename),
     but it repeatedly uses the parsing function for the group.
     The name of the generated function is retrieved from
     @('abnf::*def-parse-repetition-fns*').")
   (xdoc::p
    "The @(tsee def-parse-option) macro is similar to @(tsee def-parse-group),
     but its name is retrieved from @('abnf::*def-parse-option-fns*').
     Furthermore, if no alternative can be parsed,
     parsing succeeds because an instance of an option may be absent in fact.")
   (xdoc::p
    "The alists of function names are used in two circumstances:
     when generating a parsing function for a group or option or repetition;
     and when generating a parsing function
     that must parse an instance of that group or option or repetition.
     These alists should be normally defined prior to
     the calls of the macros that generate the parsing functions.")
   (xdoc::p
    "Singleton repetitions do not need to be in the alist for repetitions.
     Singleton repetitions are handled as their underlying elements
     in the generated parsing functions.")
   (xdoc::p
    "The parsing functions must be generated in the usual ACL2 order,
     i.e. if a parsing function must call another one,
     the latter must be generated before generating the former.
     Thus, these macros currently cannot generate
     mutually recursive parsing functions.
     This is clearly a severe limitation for typical parsing,
     but it is still useful for generating lexers,
     which often have less mutual recursion.
     Single recursion is supported, in the form or repetitions.
     We plan to extend these parser generation tools
     to support mutual recursion.")
   (xdoc::p
    "Not all the parsing functions need to be generated via the macros.
     Some may be handwritten, e.g. if they are mutually recursive.
     So long as the names of these handwritten functions
     have the form @('<parse>-<R>') for a rule name @('<R>')
     or are recorded in the alists for groups, options, and repetitions,
     generated parsing functions can seamlessly call handwritten ones.")
   (xdoc::p
    "Numeric and character terminal notations
     are handled automatically by these parser generation tools.
     That is, code to parse instances of those is automatically generated;
     the user does not have to generate any parsing functions for those,
     and does not need to specify any parsing function names for those
     (no parsing functions are generated for those;
     the parsing code for those is generated within larger parsing functions).")
   (xdoc::p
    "All of the three named constants
     @('abnf::*def-parse-group-fns*'),
     @('abnf::*def-parse-option-fns*'), and
     @('abnf::*def-parse-repetition-fns*')
     must be defined even if any of them is empty,
     i.e. if the user does not want or need to generate or use
     parsing functions for groups, options, or repetitions.
     The named constant @('abnf::*def-parse-fn-name*') must be also defined;
     there is no default.
     Finally, the named constant @('abnf::*def-parse-grammar*')
     must be also defined, as there is no default or implicit grammar.")
   (xdoc::p
    "All in all, these parser generation tools are quite preliminary,
     but they have been already useful to generate most of
     a lexer for a real (i.e. not toy) programming language.
     We plan to extend these tools more and more towards
     a customizable parser generator."))
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
    "This is used to generate portions of documentation strings
     in the generated parsing functions.
     Not all the ABNF elements are supported."))

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
  :short "Fixtype of alists from ABNF alternations to ACL2 symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the alists that specify
     the names of the functions to parse groups and options.
     Both groups and options are defined by alternations."))
  :key-type alternation
  :val-type acl2::symbol
  :true-listp t
  :pred alternation-symbol-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist repetition-symbol-alist
  :short "Fixtype of alists from ABNF repetitions to ACL2 symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the alists that specify
     the names of the functions to parse repetitions."))
  :key-type repetition
  :val-type acl2::symbol
  :true-listp t
  :pred repetition-symbol-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-code-for-element ((elem elementp)
                                        (check-error-p booleanp)
                                        (fn-name acl2::symbolp)
                                        (group-fns alternation-symbol-alistp)
                                        (option-fns alternation-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF element."
  :long
  (xdoc::topstring
   (xdoc::p
    "Numeric and character value notations are parsed directly.
     Rule names are parsed by calling the corresponding functions,
     whose names is derived from the rule names.
     Groups and options are parse by calling the corresponding functions,
     whose names are looked up in the alists.")
   (xdoc::p
    "We generate a @(tsee b*) binder that binds the parsing results
     to variables @('tree') (for a tree or error)
     and @('input') (for the remaining input).
     If the @('check-error-p') flag is set,
     we also generate a @(tsee b*) to propagate the error,
     if @('tree') is an error."))
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
                   (acl2::packn-pos (list fn-name
                                          '-
                                          (str::upcase-string
                                           (rulename->get elem.get)))
                                    fn-name)))
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
   (fn-name acl2::symbolp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (mv (code true-listp)
               (var acl2::symbolp))
  :short "Generate code to parse an instance of an ABNF repetition."
  :long
  (xdoc::topstring
   (xdoc::p
    "A repetition is part of a concatenation,
     and a concatenation (see @(tsee def-parse-gen-code-for-concatenation))
     is parsed by parsing each of its repetitions;
     the results of parsing the repetitions must be put together
     to yield the result of parsing the concatenation.
     The result of parsing each repetition is bound to a different variable,
     called @('trees<index>') where @('<index>') is a numeric index
     that starts with 1 and is incremented as we go through the concatenation.
     The index is passed to this code generation function,
     which generates @(tsee b*) binders and also returns the variable name.")
   (xdoc::p
    "If the repetition is in the alist,
     its parsing function is retrieved from there
     and we generate code to bind its result to @('trees<index>').
     We also propagate any error.")
   (xdoc::p
    "If the repetition is not in the alist,
     it must be a singleton repetition,
     in which case we generate code to parse the element,
     and we put the resulting tree into a singleton list if successful.
     Note that we propagate the error when parsing the element,
     i.e. we pass @('t') as the @('check-error-p') flag."))
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
                  rep.element t fn-name group-fns option-fns)
              (,trees-index (list tree)))
            trees-index)))
    (prog2$ (raise "Repetition ~x0 not supported yet." rep)
            (mv nil nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-parse-gen-code-for-concatenation
  ((conc concatenationp)
   (fn-name acl2::symbolp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF concatenation."
  :long
  (xdoc::topstring
   (xdoc::p
    "A concatenation is parsed by parsing each repetition in order.
     We also generate a final @(tsee b*) binder that
     puts all the lists of trees from the repetiitons
     into a list of lists of trees for the concatenation."))
  (b* (((when (endp conc)) (raise "Empty concatenation."))
       ((mv code vars) (def-parse-gen-code-for-concatenation-aux
                         conc 1 fn-name group-fns option-fns repetition-fns)))
    `(,@code
      (treess (list ,@vars))))
  :prepwork
  ((define def-parse-gen-code-for-concatenation-aux
     ((conc concatenationp)
      (index natp)
      (fn-name acl2::symbolp)
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
                            fn-name
                            group-fns
                            option-fns
                            repetition-fns))
          ((mv code2 vars) (def-parse-gen-code-for-concatenation-aux
                             (cdr conc)
                             (1+ index)
                             fn-name
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
     in order to satisfy extra-grammatical requirements."))
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
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if a list of length @('n') is a permutation of @('(1 ... n)')."))
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
   (fn-name acl2::symbolp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF alternation."
  :long
  (xdoc::topstring
   (xdoc::p
    "After possibly reordering the alternatives,
     we generate code that tries every alternative.
     We use variables @('treess<index>') to store
     either the resulting list of lists of trees or an error.
     For each alternative, we generate code for the concatenation
     and bind the result to @('treess<index>'),
     returning as soon as we get a non-error.
     If all the alternatives give an error,
     we return an error that includes all the errors for the alternatives:
     this is the reason for using and incremnting indices,
     i.e. so that we can combine them in case of error,
     not because we want to combine them in case of success.")
   (xdoc::p
    "Note that for each attempt to parse an alternative
     we bind the variable @('input1') to the remaining input,
     not the variable @('input').
     This is because we need to backtrack in case of failure,
     discarding @('input1') and going back to the previous input."))
  (b* (((when (endp alt)) (raise "Empty alternation."))
       ((unless (and (= (len order) (len alt))
                     (def-parse-order-permutationp order)))
        (raise "Bad permutation ~x0." order))
       (alt (def-parse-reorder-alternation alt order))
       ((mv code vars) (def-parse-gen-code-for-alternation-aux
                         alt 1 fn-name group-fns option-fns repetition-fns)))
    `(b* (,@code)
       (mv (err (list :found (list ,@vars) :required ',alt)) input)))
  :prepwork
  ((define def-parse-gen-code-for-alternation-aux
     ((alt alternationp)
      (index natp)
      (fn-name acl2::symbolp)
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
                            (car alt)
                            fn-name group-fns option-fns repetition-fns))
                     (mv treess input)))
                  ((when (not (resulterrp ,treess-index)))
                   (mv ,treess-index input1))))
          ((mv more-code vars)
           (def-parse-gen-code-for-alternation-aux
             (cdr alt) (1+ index)
             fn-name group-fns option-fns repetition-fns)))
       (mv (append code more-code) (cons treess-index vars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum def-parse-function-spec
  :short "Fixtype of specifications of parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A value of this type descriptively specifies a parsing function:")
   (xdoc::ul
    (xdoc::li
     "A parsing function for a rule name,
      with a possible reordering of the alternatives
      (or just the list @('(1 2 3 ...)') if there is no reordering.")
    (xdoc::li
     "A parsing function for a group,
      with a possible reordering of the alternatives
      (or just the list @('(1 2 3 ...)') if there is no reordering.")
    (xdoc::li
     "A parsing function for an option,
      with a possible reordering of the alternatives
      (or just the list @('(1 2 3 ...)') if there is no reordering.")
    (xdoc::li
     "A parsing function for a repetition.")))
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
   (fn-name acl2::symbolp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for a rule name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name is @('<parse>-<R>'), if @('<R>') is the rule name.
     We look up the alternation that defines the rule name in the grammar,
     and we generate code to parse that,
     propagating errors,
     and returning a tree for the rule name in case of success.")
   (xdoc::p
    "We also generate linear rules about the remaining input.
     These are needed to prove the termination of recursive functions
     that call this function."))
  (b* ((parse-rulename  (acl2::packn-pos (list fn-name
                                               '-
                                               (str::upcase-string rulename))
                                         fn-name))
       (alt (lookup-rulename (rulename rulename) grammar))
       (order (or order (integers-from-to 1 (len alt)))))
    `(define ,parse-rulename ((input nat-listp))
       :returns (mv (tree tree-resultp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('" rulename "').")
       (b* (((mv treess input)
             ,(def-parse-gen-code-for-alternation
                alt order fn-name group-fns option-fns repetition-fns))
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
   (fn-name acl2::symbolp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for an ABNF group."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name is retrieved from the alist for group parsing functions.
     We generate code to attempt to parse the alternation of the group,
     propagating errors,
     and returning a tree without rule name in case of success.")
   (xdoc::p
    "We also generate linear rules about the remaining input.
     These are needed to prove the termination of recursive functions
     that call this function."))
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
                alt order fn-name group-fns option-fns repetition-fns))
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
   (fn-name acl2::symbolp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for an ABNF option."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name is retrieved from the alist for option parsing functions.
     We generate code to attempt to parse the alternation of the option,
     and returning a tree without rule name in case of success.
     If parsing the alternative fails,
     we succeed and return a tree without branches.")
   (xdoc::p
    "We also generate a linear rule about the remaining input.
     These are needed to prove the termination of recursive functions
     that call this function."))
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
                alt order fn-name group-fns option-fns repetition-fns))
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
   (fn-name acl2::symbolp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event acl2::maybe-pseudo-event-formp)
  :short "Generate a parsing function for an ABNF repetition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only used for repetitions whose repeat prefix is @('*'),
     i.e. zero or more.
     The name is retrieved from the alist for repetition parsing functions.
     We generate a recursive function that
     repeatedly attempts to parse the underlying element.
     Note that we set the @('check-error-p') flag to @('nil') here,
     because we don't want the error to be returned,
     we just want to stop the recursion."))
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
                rep.element nil fn-name group-fns option-fns)
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
   (fn-name acl2::symbolp)
   (group-fns alternation-symbol-alistp)
   (option-fns alternation-symbol-alistp)
   (repetition-fns repetition-symbol-alistp))
  :returns (event acl2::maybe-pseudo-event-formp)
  :short "Generate a parsing function for a specification."
  (def-parse-function-spec-case
    spec
    :rulename (def-parse-gen-function-for-rulename
                spec.get spec.order grammar
                fn-name group-fns option-fns repetition-fns)
    :group (def-parse-gen-function-for-group
             spec.get spec.order
             fn-name group-fns option-fns repetition-fns)
    :option (def-parse-gen-function-for-option
              spec.get spec.order
              fn-name group-fns option-fns repetition-fns)
    :repetition (def-parse-gen-function-for-repetition
                  spec.get
                  fn-name group-fns option-fns repetition-fns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-parse-single (spec)
  :short "Define a single parsing function for a specification."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an auxiliary macro, used by the others,
     which are the ones that should be used by the user.")
   (xdoc::p
    "Here we hardwire the names of the named constants for
     the grammar and the group, option, and repetition alists."))
  `(make-event (def-parse-gen-function-for-spec
                 ,spec
                 *def-parse-grammar*
                 *def-parse-fn-name*
                 *def-parse-group-fns*
                 *def-parse-option-fns*
                 *def-parse-repetition-fns*)))

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
