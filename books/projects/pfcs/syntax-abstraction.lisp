; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2022,2024 Provable Inc. (https://www.provable.com)
;
; Authors: Alessandro Coglio (acoglio on GitHub)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "grammar")
(include-book "abstract-syntax")

(include-book "abnf-tree-utilities")

(include-book "kestrel/fty/character-result" :dir :system)
(include-book "kestrel/fty/character-list-result" :dir :system)
(include-book "kestrel/fty/integer-result" :dir :system)
(include-book "kestrel/fty/boolean-result" :dir :system)
(include-book "kestrel/fty/nat-natlist-result" :dir :system)
(include-book "kestrel/fty/nat-option-result" :dir :system)
(include-book "kestrel/fty/nat-option-list-result" :dir :system)
(include-book "kestrel/fty/natoption-natoptionlist-result" :dir :system)
(include-book "kestrel/fty/string-result" :dir :system)
(include-book "kestrel/fty/string-list-result" :dir :system)
(include-book "kestrel/std/strings/letter-chars" :dir :system)
(include-book "kestrel/std/strings/letter-digit-uscore-chars" :dir :system)
(include-book "kestrel/std/strings/ucletter-chars" :dir :system)
(include-book "kestrel/std/strings/lcletter-chars" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to string library

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled str::letter-char-p-alt-def
  (equal (str::letter-char-p x)
         (or (str::ucletter-char-p x)
             (str::lcletter-char-p x)))
  :enable (str::letter-char-p
           str::ucletter-char-p
           str::lcletter-char-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled str::letter/digit/uscore-char-p-alt-def
  (equal (str::letter/digit/uscore-char-p x)
         (or (str::letter-char-p x)
             (str::dec-digit-char-p x)
             (equal x #\_)))
  :enable (str::letter/digit/uscore-char-p
           str::letter-char-p
           str::dec-digit-char-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ syntax-abstraction
  :parents (abstract-syntax)
  :short "Mapping from concrete to abstract syntax, for PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " is an abstraction of the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    ". Here we define the abstraction mapping from "
    (xdoc::seetopic "concrete-syntax-trees" "CSTs")
    " to "
    (xdoc::seetopic "abstract-syntax-trees" "ASTs")
    ".")
   (xdoc::p
    "NOTE... (about deftreeops stuff)


For now our abstraction mapping has weak guards and many run-time checks.
     We plan to turn things around eventually,
     i.e. to have strong guards and ideally no run-time checks.
     This may involve the development of
     some more general support in our ABNF library for this."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-?-comma ((tree abnf::treep))
  :returns (pass pass-resultp)
  :short "Check if a tree is @('[ \",\" ]')."
  (b* (((okf treess) (check-tree-nonleaf tree nil))
       ((when (endp treess)) :pass)
       ((okf trees) (check-tree-list-list-1 treess))
       ((okf tree) (check-tree-list-1 trees)))
    (check-tree-ichars tree ","))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define abs-decimal-digit-to-nat ((tree abnf::treep))
  :returns (nat nat-resultp)
  :short "Abstract a @('digit') to a natural number."
  (b* (((okf nat) (check-tree-nonleaf-num-range tree "digit" #x30 #x39)))
    (- nat #x30))
  :hooks (:fix)
  ///

  (defret natp-of-decimal-digit-to-nat
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret abs-decimal-digit-to-nat-bound
    (implies (not (reserrp nat))
             (< nat 10))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-decimal-digit-to-nat ((trees abnf::tree-listp))
  :returns (nat nat-resultp)
  :short "Abstract a @('*decimal-digit') to a natural number,
          interpreting the digits in big endian."
  (abs-*-decimal-digit-to-nat-aux trees 0)
  :hooks (:fix)

  :prepwork
  ((define abs-*-decimal-digit-to-nat-aux ((trees abnf::tree-listp)
                                           (current natp))
     :returns (nat nat-resultp)
     :parents nil
     (b* (((when (endp trees)) (nfix current))
          ((okf digit-nat) (abs-decimal-digit-to-nat (car trees))))
       (abs-*-decimal-digit-to-nat-aux (cdr trees)
                                       (+ digit-nat
                                          (* (nfix current) 10))))
     :hooks (:fix)))

  ///

  (defret natp-of-abs-*-decimal-digit-to-nat
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-decimal-digit-to-char ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('digit') to an ACL2 character."
  (b* (((okf nat) (check-tree-nonleaf-num-range tree "digit" #x30 #x39)))
    (code-char nat))
  :hooks (:fix)
  ///

  (defret dec-digit-char-p-of-abs-decimal-digit-to-char
    (implies (not (reserrp char))
             (str::dec-digit-char-p char))
    :hints (("Goal" :in-theory (enable str::dec-digit-char-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-uppercase-letter ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract an @('uppercase-letter') to an ACL2 character."
  (b* (((okf nat)
        (check-tree-nonleaf-num-range tree "uppercase-letter" #x41 #x5a)))
    (code-char nat))
  :hooks (:fix)
  ///

  (defret ucletter-char-p-of-abs-uppercase-letter
    (implies (not (reserrp char))
             (str::ucletter-char-p char))
    :hints (("Goal" :in-theory (enable str::ucletter-char-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-lowercase-letter ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('lowercase-letter') to an ACL2 character."
  (b* (((okf nat)
        (check-tree-nonleaf-num-range tree "lowercase-letter" #x61 #x7a)))
    (code-char nat))
  :hooks (:fix)
  ///

  (defret lcletter-char-p-of-abs-lowercase-letter
    (implies (not (reserrp char))
             (str::lcletter-char-p char))
    :hints (("Goal" :in-theory (enable str::lcletter-char-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-letter ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('letter') to an ACL2 character."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree "letter"))
       (char (abs-uppercase-letter tree))
       ((when (not (reserrp char))) char)
       (char (abs-lowercase-letter tree))
       ((when (not (reserrp char))) char))
    (reserrf (list :found-subtree (tree-info-for-error tree))))
  :hooks (:fix)
  ///

  (defret letter-char-p-of-abs-letter
    (implies (not (reserrp char))
             (str::letter-char-p char))
    :hints (("Goal" :in-theory (enable str::letter-char-p-alt-def)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-letter/decimaldigit/underscore ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('( letter / decimal-digit / \"_\" )')
          to an ACL2 character."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree nil))
       (char (abs-letter tree))
       ((when (not (reserrp char))) char)
       (char (abs-decimal-digit-to-char tree))
       ((when (not (reserrp char))) char)
       (pass (check-tree-ichars tree "_"))
       ((when (not (reserrp pass))) #\_))
    (reserrf (list :found-subtree (tree-info-for-error tree))))
  :hooks (:fix)
  ///

  (defret letter/digit/uscore-char-p-of-abs-letter/decimaldigit/underscore
    (implies (not (reserrp char))
             (str::letter/digit/uscore-char-p char))
    :hints (("Goal" :in-theory (enable
                                str::letter/digit/uscore-char-p-alt-def)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-letter/decimaldigit/underscore ((trees abnf::tree-listp))
  :returns
  (chars
   character-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      acl2::characterp-when-character-resultp-and-not-reserrp
      acl2::character-listp-when-character-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*( letter / digit / \"_\" )')
          to a list of ACL2 characters."
  (b* (((when (endp trees)) nil)
       ((okf char) (abs-letter/decimaldigit/underscore (car trees)))
       ((okf chars) (abs-*-letter/decimaldigit/underscore (cdr trees))))
    (cons char chars))
  :hooks (:fix)
  ///

  (defret letter/digit/uscore-char-listp-of-abs-*-letter/decimaldigit/underscore
    (implies (not (reserrp chars))
             (str::letter/digit/uscore-charlist-p chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-identifier ((tree abnf::treep))
  ;; Right now there is no separate object for identifiers, we just use
  ;; ACL2 strings.
  :returns (id string-resultp)
  :short "Abstract an @('identifier') to an identifier."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (check-tree-nonleaf-2 tree "identifier"))
       ((okf letter-tree) (check-tree-list-1 sub.1st))
       ((okf char) (abs-letter letter-tree))
       ((okf chars) (abs-*-letter/decimaldigit/underscore sub.2nd))
       (string (str::implode (cons char chars)))
       )
    string)
  :hooks (:fix))

; This is an example of how to naively convert an abstraction function from
; type 1 to type 2, in this case abstracting an identifer CST to a string.
; Both types accept an abnf::treep.
; * Type 1 (above) returns an error if the tree is not a valid identifier CST,
;   so the return type is string-resultp.
; * Type 2 has a guard of cst-matchp (generated by deftreeops),
;   so it should not need to return an error.
;   However, if the callees are still type 1, then it still needs to
;   handle the case where they return an error.
;   That is the purpose of the (er hard? ..) side-effect call.
(define abs-identifier-alt ((tree abnf::treep))
  ;; Right now there is no separate object for identifiers, we just use
  ;; ACL2 strings.
  :returns (id stringp)
  :guard (cst-matchp tree "identifier")
  (let ((string-or-err  ; we should not have an err at this point,
         ; but the callees return type includes err.
         (b* (((okf (abnf::tree-list-tuple2 sub))
               (check-tree-nonleaf-2 tree "identifier"))
              ((okf letter-tree) (check-tree-list-1 sub.1st))
              ((okf char) (abs-letter letter-tree))
              ((okf chars) (abs-*-letter/decimaldigit/underscore sub.2nd))
              (string (str::implode (cons char chars))))
           string)))
    (b* (((when (stringp string-or-err)) string-or-err)
         (- (er hard? 'top-level "problem in abs-identifier-alt: ~x0" tree)))
      "")) ; this string will never actually be executed; it is for logic
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Syntax around abs-identifier used for other rules

(define abs-comma-identifier ((tree abnf::treep))
  :returns (id string-resultp)
  :short "Abstract a @('( \",\" identifier )') to a string."
  (b* (((okf (abnf::tree-list-tuple2 sub)) (check-tree-nonleaf-2 tree nil))
       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf &) (check-tree-ichars tree ","))
       ((okf tree) (check-tree-list-1 sub.2nd)))
    (abs-identifier tree))
  :hooks (:fix))

(define abs-*-comma-identifier ((trees abnf::tree-listp))
  :returns 
  (ids
   string-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      acl2::stringp-when-string-resultp-and-not-reserrp
      acl2::string-listp-when-string-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*( \",\" identifier )') to a list of identifiers."
  (b* (((when (endp trees)) nil)
       ((okf id) (abs-comma-identifier (car trees)))
       ((okf ids) (abs-*-comma-identifier (cdr trees))))
    (cons id ids))
  :hooks (:fix)
  ///
  
  (defret identifier-listp-of-abs-*-comma-identifier
    (implies (not (reserrp ids))
             (string-listp ids))))

(define abs-?-identifier-*-comma-identifier ((tree abnf::treep))
  :returns
  (ids
   string-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      acl2::stringp-when-string-resultp-and-not-reserrp
      acl2::string-listp-when-string-list-resultp-and-not-reserrp))))
  :short "Abstract a @('[ identifier *( \",\" identifier ) ]')
            to a list of identifiers (strings)."
  (b* (((okf treess) (check-tree-nonleaf tree nil))
       ((when (endp treess)) nil)
       ((okf (abnf::tree-list-tuple2 sub)) (check-tree-list-list-2 treess))
       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf id) (abs-identifier tree))
       ((okf ids) (abs-*-comma-identifier sub.2nd)))
    (cons id ids))
  :hooks (:fix)
  ///

  (defret identifier-listp-of-abs-?-identifier-*-comma-identifier
    (implies (not (reserrp ids))
             (string-listp ids))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-numeral ((tree abnf::treep))
  :returns (nat nat-resultp)
  :short "Abstract a @('numeral') to a natural number."
  (b* (((okf sub) (check-tree-nonleaf-1 tree "numeral"))
       ((unless (consp sub)) (reserrf (list :empty-numeral))))
    (abs-*-decimal-digit-to-nat sub))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-optional-minus-sign-p ((tree abnf::treep))
  :returns (ret boolean-resultp)
  :short "Check if a tree is @('[ \"-\" ]')."
  (b* (((okf treess) (check-tree-nonleaf tree nil))
       ((when (endp treess)) nil) ; empty optional tree
       ((okf trees) (check-tree-list-list-1 treess))
       ((okf tree) (check-tree-list-1 trees))
       (pass (check-tree-ichars tree "-"))
       ((when (reserrp pass)) pass))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-integer ((tree abnf::treep))
  :returns (int integer-resultp)
  :short "Abstract an @('integer') to an ACL2 int."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (check-tree-nonleaf-2 tree "integer"))
       ((okf optional-minus-tree) (check-tree-list-1 sub.1st))
       ((okf has-minus-sign?) (check-optional-minus-sign-p
                               optional-minus-tree))
       ((okf numeral-tree) (check-tree-list-1 sub.2nd))
       ((okf nat-value) (abs-numeral numeral-tree)))
    (if has-minus-sign?
        (- nat-value)
        nat-value))
  :hooks (:fix))

; deftreeops version doesn't return error,
; and has a guard that it is already a CST for the "integer" rule.

; Example of converting an abstraction function from type 1 to type 2.
; See also comment on abs-identifier-alt.
(define abs-integer-alt ((tree abnf::treep))
  :returns (int integerp)
  :guard (cst-matchp tree "integer")
  (let ((int-or-err ; we should not have an err at this point,
         ; but the callees return type includes err.
         (b* (((okf (abnf::tree-list-tuple2 sub))
               (check-tree-nonleaf-2 tree "integer"))
              ((okf optional-minus-tree) (check-tree-list-1 sub.1st))
              ((okf has-minus-sign?) (check-optional-minus-sign-p
                                      optional-minus-tree))
              ((okf numeral-tree) (check-tree-list-1 sub.2nd))
              ((okf nat-value) (abs-numeral numeral-tree)))
           (if has-minus-sign?
               (- nat-value)
               nat-value))))
    (b* (((when (integerp int-or-err)) int-or-err)
         (- (er hard? 'top-level "problem in abs-integer-alt: ~x0" tree)))
      0)) ; this int will never actually be executed; it is for logic
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-primary-expression ((tree abnf::treep))
  :returns (expr-or-err expression-resultp)
  :short "Abstract a @('primary-expression')."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree "primary-expression"))
       ((okf rulename?) (check-tree-nonleaf? tree)))
    (cond ((equal rulename? "identifier") 
           (let ((id-or-err (abs-identifier tree)))
             (if (stringp id-or-err)
                 (make-expression-var :name id-or-err)
                 id-or-err)))
          ((equal rulename? "integer")
           (let ((int-or-err (abs-integer tree)))
             (if (integerp int-or-err)
                 (make-expression-const :value int-or-err)
                 int-or-err)))
          (t (reserrf (list :found-subtree (tree-info-for-error tree))))))
  :hooks (:fix))

; Example of how to convert a more complex abstraction function from type 1
; to type 2, when the callees are still type 1:
; * You have to call cst-matchp first before calling the other functions;
;   if the other functions are called on the wrong thing, they get errors.
; Assuming you have a simple alternative rule like
;    primary-expression = identifier / integer
; then:
; * To find out which alternative you have, call
;   cst-<rulename>-conc? to get an integer (1-based).
; * Then to get the subtree, call
;   cst-<rulename>-conc<i>-rep-elem

(define abs-primary-expression-alt ((tree abnf::treep))
  :returns (expr-or-err expression-resultp)
  (b* (((unless (cst-matchp tree "primary-expression"))
        (reserrf (list :expecting-primary-expression
                       (tree-info-for-error tree))))
       (alternate-index (cst-primary-expression-conc? tree))
       (subtree (case alternate-index
                  (1 (cst-primary-expression-conc1-rep-elem tree))
                  (2 (cst-primary-expression-conc2-rep-elem tree))
                  (otherwise (reserrf (list :malformed-primary-express-tree
                                            (tree-info-for-error tree))))))
       ((when (reserrp subtree)) subtree))
    (case alternate-index
      (1 (let ((id-or-err (abs-identifier subtree)))
             (if (stringp id-or-err)
                 (make-expression-var :name id-or-err)
                 id-or-err)))
      (2 (let ((int-or-err (abs-integer subtree)))
             (if (integerp int-or-err)
                 (make-expression-const :value int-or-err)
                 int-or-err)))))
  :hooks (:fix))

; Example of how to convert an abstraction function from type 1 to type 2,
; when the callees have already been converted to type 2.
; Note that the function becomes simpler than either of the earlier versions.
;
; At the current time, deftreeops does not generate macros and theorems
; about concatenations of more than one thing, so we cannot yet
; convert the entire syntax abstractor to type 2.

(define abs-primary-expression-alt2 ((tree abnf::treep))
  :guard (cst-matchp tree "primary-expression")
  :returns (expr expressionp)
  (case (cst-primary-expression-conc? tree)
    (1 (make-expression-var
        :name
        (abs-identifier-alt (cst-primary-expression-conc1-rep-elem tree))))
    (2 (make-expression-const
        :value
        (abs-integer-alt (cst-primary-expression-conc2-rep-elem tree)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; multiplication-expression = primary-expression
;                           / multiplication-expression "*" primary-expression

; This does not use deftreeops macros because they don't yet
; handle a concatenation of more than 1 repetition
; (using alternation/concatenation/repetition terminology).

(define abs-multiplication-expression ((tree abnf::treep))
  :returns (expr-or-err expression-resultp)
  :short "Abstract a @('multiplication-expression')."
  (b* (((okf treess) (check-tree-nonleaf tree "multiplication-expression")))
    (case (len treess)
      (1 (b* (((okf trees) (check-tree-list-list-1 treess))
              ((okf tree) (check-tree-list-1 trees))
              ((okf primary) (abs-primary-expression tree)))
           primary))
      (3 (b* (((okf (abnf::tree-list-tuple3 sub))
               (check-tree-list-list-3 treess))
              ((okf tree) (check-tree-list-1 sub.1st))
              ((okf sub-mul) (abs-multiplication-expression tree))
              ((okf tree) (check-tree-list-1 sub.2nd))
              ((okf &) (check-tree-schars tree "*"))
              ((okf tree) (check-tree-list-1 sub.3rd))
              ((okf sub-prim) (abs-primary-expression tree)))
           (make-expression-mul :arg1 sub-mul :arg2 sub-prim)))
      (otherwise (reserrf (list :found-subtree (tree-info-for-error tree))))))
  :measure (abnf::tree-count tree)

  ;; The following pattern is needed because the function is recursive,
  ;; and the return type theorem must be proved before guard verification.
  :verify-guards nil 
  ///
  (verify-guards abs-multiplication-expression))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; addition-expression = multiplication-expression
;                     / addition-expression "+" multiplication-expression

(define abs-addition-expression ((tree abnf::treep))
  :returns (expr-or-err expression-resultp)
  :short "Abstract a @('addition-expression')."
  (b* (((okf treess) (check-tree-nonleaf tree "addition-expression")))
    (case (len treess)
      (1 (b* (((okf trees) (check-tree-list-list-1 treess))
              ((okf tree) (check-tree-list-1 trees))
              ((okf mult) (abs-multiplication-expression tree)))
           mult))
      (3 (b* (((okf (abnf::tree-list-tuple3 sub))
               (check-tree-list-list-3 treess))
              ((okf tree) (check-tree-list-1 sub.1st))
              ((okf sub-add) (abs-addition-expression tree))
              ((okf tree) (check-tree-list-1 sub.2nd))
              ((okf &) (check-tree-schars tree "+"))
              ((okf tree) (check-tree-list-1 sub.3rd))
              ((okf sub-mult) (abs-multiplication-expression tree)))
           (make-expression-add :arg1 sub-add :arg2 sub-mult)))
      (otherwise (reserrf (list :found-subtree (tree-info-for-error tree))))))
  :measure (abnf::tree-count tree)

  ;; The following pattern is needed because the function is recursive,
  ;; and the return type theorem must be proved before guard verification.
  :verify-guards nil 
  ///
  (verify-guards abs-addition-expression))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; expression = addition-expression

(define abs-expression ((tree abnf::treep))
  :returns (expr expression-resultp)
  :short "Abstract an @('expression') to an expression."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree "expression")))
    (abs-addition-expression tree))
  :hooks (:fix))

; Example.  See "-alt" functions above.
(define abs-expression-alt ((tree abnf::treep))
  :guard (cst-matchp tree "expression")
  :returns (ret-expr expressionp)
  (let ((expr (abs-expression tree)))
    (if (expressionp expr)
        expr
        ;; dummy expression which should never happen
        (make-expression-var :name "ABSTRACTION ERROR")))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Syntax around abs-expression used for other rules

(define abs-comma-expression ((tree abnf::treep))
  :returns (expr expression-resultp)
  :short "Abstract a @('( \",\" expression )') to an expression."
  (b* (((okf (abnf::tree-list-tuple2 sub)) (check-tree-nonleaf-2 tree nil))
       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf &) (check-tree-ichars tree ","))
       ((okf tree) (check-tree-list-1 sub.2nd)))
    (abs-expression tree))
  :hooks (:fix))

(define abs-*-comma-expression ((trees abnf::tree-listp))
  :returns
  (exprs 
   expression-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      expressionp-when-expression-resultp-and-not-reserrp
      expression-listp-when-expression-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*( \",\" expression )') to a list of expressions."
  (b* (((when (endp trees)) nil)
       ((okf expr) (abs-comma-expression (car trees)))
       ((okf exprs) (abs-*-comma-expression (cdr trees))))
    (cons expr exprs))
  :measure (abnf::tree-list-count trees)
  :hooks (:fix)
  :verify-guards nil
  ///
  (verify-guards abs-*-comma-expression)

  (defret expression-list-of-abs-*-comma-expression
    (implies (not (reserrp exprs))
             (expression-listp exprs))))

(define abs-?-expression-*-comma-expression ((tree abnf::treep))
  :returns
  (exprs
   expression-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      expressionp-when-expression-resultp-and-not-reserrp
      expression-listp-when-expression-list-resultp-and-not-reserrp))))
  :short "Abstract a @('[ expression *( \",\" expression ) ]')
            to a list of expressions."
  (b* (((okf treess) (check-tree-nonleaf tree nil))
       ((when (endp treess)) nil)
       ((okf (abnf::tree-list-tuple2 sub)) (check-tree-list-list-2 treess))
       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf expr) (abs-expression tree))
       ((okf exprs) (abs-*-comma-expression sub.2nd)))
    (cons expr exprs))
  :hooks (:fix)
  ///

  (defret expression-listp-of-abs-?-expression-*-comma-expression
    (implies (not (reserrp exprs))
             (expression-listp exprs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; equality-constraint = expression "==" expression

#||
; Note: this example doesn't work yet.  Not sure if the extra guard is
; the right way to make sure we have the right tree.

(define abs-equality-constraint-alt ((tree abnf::treep))
  :guard (and (cst-matchp tree "equality-constraint")
              (cst-list-list-conc-matchp
               (abnf::tree-nonleaf->branches tree)
               "expression \"==\" expression"))
  :returns (c constraintp)
  :short "Abstract an @('equality-constraint') to a constraint."
  (b* ((trees (abnf::tree-nonleaf->branches tree)))
    (make-constraint-equal
     :left (abs-expression-alt (first trees))
     :right (abs-expression-alt (third trees))))
  :hooks (:fix))
||#

(define abs-equality-constraint ((tree abnf::treep))
  :returns (c constraint-resultp)
  :short "Abstract an @('equality-constraint') to a constraint."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (check-tree-nonleaf-3 tree "equality-constraint"))

       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf lhs) (abs-expression tree))

       ((okf tree) (check-tree-list-1 sub.2nd))
       ((okf &) (check-tree-schars tree "=="))

       ((okf tree) (check-tree-list-1 sub.3rd))
       ((okf rhs) (abs-expression tree)))

    (make-constraint-equal :left lhs
                           :right rhs))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-relation-constraint ((tree abnf::treep))
  :returns (c constraint-resultp)
  :short "Abstract a @('relation-constraint') to a constraint."
  (b* (((okf (abnf::tree-list-tuple4 sub))
        (check-tree-nonleaf-4 tree "relation-constraint"))

       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf id) (abs-identifier tree))

       ((okf tree) (check-tree-list-1 sub.2nd))
       ((okf &) (check-tree-schars tree "("))

       ((okf tree) (check-tree-list-1 sub.3rd))
       ((okf expressions) (abs-?-expression-*-comma-expression tree))

       ((okf tree) (check-tree-list-1 sub.4th))
       ((okf &) (check-tree-schars tree ")")))

    (make-constraint-relation :name id
                              :args expressions))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-constraint ((tree abnf::treep))
  :returns (lit constraint-resultp)
  :short "Abstract a @('constraint') to a constraint."
  (b* (((okf tree) (check-tree-nonleaf-1-1 tree "constraint"))
       ((okf rulename?) (check-tree-nonleaf? tree)))
    (cond ((equal rulename? "equality-constraint")
           (abs-equality-constraint tree))
          ((equal rulename? "relation-constraint")
           (abs-relation-constraint tree))
          (t (reserrf (list :found-subtree (tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Syntax around abs-constraint used for other rules

(define abs-*-constraint ((trees abnf::tree-listp))
  :returns
  (constraints 
   constraint-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      constraintp-when-constraint-resultp-and-not-reserrp
      constraint-listp-when-constraint-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*constraint') to a list of constraints."
  (b* (((when (endp trees)) nil)
       ((okf constraint) (abs-constraint (car trees)))
       ((okf constraints) (abs-*-constraint (cdr trees))))
    (cons constraint constraints))
  :measure (abnf::tree-list-count trees)
  :hooks (:fix)
  :verify-guards nil
  ///
  (verify-guards abs-*-constraint)

  (defret constraint-listp-of-abs-*-constraint
    (implies (not (reserrp constraints))
             (constraint-listp constraints))))

(define abs-comma-constraint ((tree abnf::treep))
  :returns (expr constraint-resultp)
  :short "Abstract a @('( \",\" constraint )') to an constraint."
  (b* (((okf (abnf::tree-list-tuple2 sub)) (check-tree-nonleaf-2 tree nil))
       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf &) (check-tree-ichars tree ","))
       ((okf tree) (check-tree-list-1 sub.2nd)))
    (abs-constraint tree))
  :hooks (:fix))

(define abs-*-comma-constraint ((trees abnf::tree-listp))
  :returns
  (constraints 
   constraint-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      constraintp-when-constraint-resultp-and-not-reserrp
      constraint-listp-when-constraint-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*( \",\" constraint )') to a list of constraints."
  (b* (((when (endp trees)) nil)
       ((okf constraint) (abs-comma-constraint (car trees)))
       ((okf constraints) (abs-*-comma-constraint (cdr trees))))
    (cons constraint constraints))
  :measure (abnf::tree-list-count trees)
  :hooks (:fix)
  :verify-guards nil
  ///
  (verify-guards abs-*-comma-constraint)

  (defret constraint-list-of-abs-*-comma-constraint
    (implies (not (reserrp constraints))
             (constraint-listp constraints))))

(define abs-?-constraint-*-comma-constraint ((tree abnf::treep))
  :returns
  (constraints
   constraint-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      constraintp-when-constraint-resultp-and-not-reserrp
      constraint-listp-when-constraint-list-resultp-and-not-reserrp))))
  :short "Abstract a @('[ constraint *( \",\" constraint ) ]')
            to a list of constraints."
  (b* (((okf treess) (check-tree-nonleaf tree nil))
       ((when (endp treess)) nil)
       ((okf (abnf::tree-list-tuple2 sub)) (check-tree-list-list-2 treess))
       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf constraint) (abs-constraint tree))
       ((okf constraints) (abs-*-comma-constraint sub.2nd)))
    (cons constraint constraints))
  :hooks (:fix)
  ///

  (defret constraint-listp-of-abs-?-constraint-*-comma-constraint
    (implies (not (reserrp constraints))
             (constraint-listp constraints))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-definition ((tree abnf::treep))
  :returns (def definition-resultp)
  :short "Abstract a @('definition') CST to a definition AST."
  (b* (((okf (abnf::tree-list-tuple8 sub))
        (check-tree-nonleaf-8 tree "definition"))

       ((okf tree) (check-tree-list-1 sub.1st))
       ((okf id) (abs-identifier tree))

       ((okf tree) (check-tree-list-1 sub.2nd))
       ((okf &) (check-tree-schars tree "("))

       ((okf tree) (check-tree-list-1 sub.3rd))
       ((okf params) (abs-?-identifier-*-comma-identifier tree))

       ((okf tree) (check-tree-list-1 sub.4th))
       ((okf &) (check-tree-schars tree ")"))

       ((okf tree) (check-tree-list-1 sub.5th))
       ((okf &) (check-tree-schars tree ":="))

       ((okf tree) (check-tree-list-1 sub.6th))
       ((okf &) (check-tree-schars tree "{"))

       ((okf tree) (check-tree-list-1 sub.7th))
       ((okf constraints) (abs-?-constraint-*-comma-constraint tree))

       ((okf tree) (check-tree-list-1 sub.8th))
       ((okf &) (check-tree-schars tree "}")))

    (make-definition :name id
                     :para params
                     :body constraints))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-definition ((trees abnf::tree-listp))
  :returns
  (definitions 
   definition-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      definitionp-when-definition-resultp-and-not-reserrp
      definition-listp-when-definition-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*definition') to a list of definitions."
  (b* (((when (endp trees)) nil)
       ((okf definition) (abs-definition (car trees)))
       ((okf definitions) (abs-*-definition (cdr trees))))
    (cons definition definitions))
  :measure (abnf::tree-list-count trees)
  :hooks (:fix)
  :verify-guards nil
  ///
  (verify-guards abs-*-definition)

  (defret definition-listp-of-abs-*-definition
    (implies (not (reserrp definitions))
             (definition-listp definitions))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-system ((tree abnf::treep))
  :returns (sys system-resultp)
  :short "Abstract a @('system') CST to a system AST."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (check-tree-nonleaf-2 tree "system"))

       ((okf defs) (abs-*-definition sub.1st))
       ((okf constraints) (abs-*-constraint sub.2nd)))

    (make-system :definitions defs
                 :constraints constraints))
  :hooks (:fix))

