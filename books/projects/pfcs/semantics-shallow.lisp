; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-operations")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/system/pseudo-event-form-listp" :dir :system)
(include-book "std/strings/char-case" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defund-sk" :dir :system)

(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define current-package+ (state)
  :returns (package stringp)
  (b* ((package (current-package state))
       ((unless (and (stringp package)
                     (not (equal package ""))))
        (raise "Internal error: current package ~x0 is not a string." package)
        "."))
    package)
  ///

  (defret current-package+-not-empty
    (not (equal package ""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics-shallow
  :parents (semantics)
  :short "Shallowly embedded semantics of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The semantics informally described in @(see semantics)
     can be also formalized in a shallowly embedded way,
     by defining ACL2 functions that turn expressions and constraints
     into ACL2 terms and functions that express the semantics.")
   (xdoc::p
    "In the names of the ACL2 functions defined below,
     the prefix @('sesem') stands for `shallowly embedded semantics'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-to-symbol ((name stringp) state)
  :returns (sym symbolp)
  :short "Turn a PFCS relation or variable name into an ACL2 symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "The PFCS abstract syntax uses strings for relation and variable names.
     These must be turned into symbols in the shallowly embedded semantics.
     Here we define the mapping.")
   (xdoc::p
    "Assuming that PFCS relation and variable names
     would normally consist of lowercase letters, digits, and underscores,
     we map lowercase letters to uppercase letters,
     digits to themselves,
     and underscores to dashes;
     we use the resulting string as name of the symbol,
     which we put in the current package.
     This way, idiomatic PFCS names are mapped to idiomatic ACL2 symbols.")
   (xdoc::p
    "This mapping is not bulletproof.
     The current package may import symbols from the Lisp package, for example,
     and a PFCS name may end up being mapped to a symbol in the Lisp package,
     which cannot be used as an ACL2 name.
     In the future, we may make this mapping more robust."))
  (b* ((chars (str::explode name))
       (new-chars (name-to-symbol-aux chars))
       (new-string (str::implode new-chars)))
    (intern$ new-string (current-package+ state)))

  :prepwork
  ((define name-to-symbol-aux ((chars character-listp))
     :returns (new-chars character-listp)
     :parents nil
     (b* (((when (endp chars)) nil)
          (char (car chars))
          (new-char (if (equal char #\_)
                        #\-
                      (str::upcase-char char)))
          (new-chars (name-to-symbol-aux (cdr chars))))
       (cons new-char new-chars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection name-list-to-symbol-list (x state)
  :guard (string-listp x)
  :returns (symbols symbol-listp)
  :short "Turn a list of PFCS relation or variable names
          into a list of ACL2 symbols."
  (name-to-symbol x state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-set-to-symbol-list ((names string-setp) state)
  :returns (syms symbol-listp)
  :short "Lift @(tsee name-to-symbol) to a mapping
          from sets of strings to lists of symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "The order of the list is according to
     the total order that osets are based on."))
  (cond ((set::emptyp names) nil)
        (t (cons (name-to-symbol (set::head names) state)
                 (name-set-to-symbol-list (set::tail names) state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-expression ((expr expressionp) (prime symbolp) state)
  :returns term
  :short "Shallowly embedded semantics of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the expression, this function also takes as argument
     a variable (symbol) to use as the prime.
     This is needed because we generate terms involving prime field operations,
     which all take a prime as argument;
     the prime is also used to reduce integer constants.")
   (xdoc::p
    "A constant is mapped to itself, reduced modulo the prime.")
   (xdoc::p
    "A variable is mapped to a symbol, according to @(tsee name-to-symbol).")
   (xdoc::p
    "Additions and multiplications are mapped to calls of
     the corresponding prime field operations applied to
     the terms obtained by translating the argument expressions."))
  (expression-case
   expr
   :const `(mod ,expr.value ,prime)
   :var (name-to-symbol expr.name state)
   :add `(add ,(sesem-expression expr.arg1 prime state)
              ,(sesem-expression expr.arg2 prime state)
              ,prime)
   :mul `(mul ,(sesem-expression expr.arg1 prime state)
              ,(sesem-expression expr.arg2 prime state)
              ,prime))
  :measure (expression-count expr)
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-expression-list ((exprs expression-listp) (prime symbolp) state)
  :returns (terms true-listp)
  :short "Shallowly embedded semantics of lists of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee sesem-expression) to lists.
     We obtain a list of terms."))
  (cond ((endp exprs) nil)
        (t (cons (sesem-expression (car exprs) prime state)
                 (sesem-expression-list (cdr exprs) prime state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-constraint ((constr constraintp) (prime symbolp) state)
  :returns term
  :short "Shallowly embedded semantics of a constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn an equality constraint into an ACL2 equality
     of the terms denoted by the left and right expressions.
     We turn a relation constraint into an ACL2 call of the relation
     on the terms denoted by the argument expressions.
     Note that we include the variable for the prime."))
  (constraint-case
   constr
   :equal `(equal ,(sesem-expression constr.left prime state)
                  ,(sesem-expression constr.right prime state))
   :relation `(,(name-to-symbol constr.name state)
               ,@(sesem-expression-list constr.args prime state)
               ,prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-constraint-list ((constrs constraint-listp) (prime symbolp) state)
  :returns (terms true-listp)
  :short "Shallowly embedded semantics of a list of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee sesem-constraint) to lists.
     We obtain a list of terms."))
  (cond ((endp constrs) nil)
        (t (cons (sesem-constraint (car constrs) prime state)
                 (sesem-constraint-list (cdr constrs) prime state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-gen-fep-terms ((vars symbol-listp) (prime symbolp))
  :returns (terms pseudo-term-listp :hyp :guard)
  :short "Generate a list of terms @('(fep x1 p)'), ..., @('(fep xn p)')
          from a list of variables @('x1'), ..., @('xn')."
  (cond ((endp vars) nil)
        (t (cons `(fep ,(car vars) ,prime)
                 (sesem-gen-fep-terms (cdr vars) prime))))
  :prepwork ((local (in-theory (enable pseudo-termp pseudo-term-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-definition ((def definitionp) (prime symbolp) state)
  :returns (event pseudo-event-formp)
  :short "Shallowly embedded semantics of a definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the definition into an ACL2 function definition
     that defines a predicate that holds exactly on the values
     that satisfy all the constraints.
     If the definition has no free variables,
     we generate a @(tsee defun).
     Otherwise, we generate a @(tsee defun-sk)
     with those free variables existentially quantified.
     (More precisely, we generate @(tsee defund) or @(tsee defund-sk)).")
   (xdoc::p
    "The existential quantification is the right semantics
     for the free variables in a relation's definition,
     based on the intended use of these constraints in zero-knowledge proofs.
     However, the quantification is avoided
     if all the variables in the body are treated as parameters."))
  (b* (((definition def) def)
       (pred-name (name-to-symbol def.name state))
       (free (definition-free-vars def))
       (quant (name-set-to-symbol-list free state))
       (para (name-list-to-symbol-list def.para state))
       (body `(and ,@(sesem-constraint-list def.body prime state))))
    (if free
        `(defund-sk ,pred-name (,@para ,prime)
           (exists (,@quant) (and ,@(sesem-gen-fep-terms quant prime) ,body)))
      `(defund ,pred-name (,@para ,prime)
         ,body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-definition-list ((defs definition-listp) (prime symbolp) state)
  :returns (events pseudo-event-form-listp)
  :short "Shallowly embedded semanics of a list of definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the list of events generated from the definitions."))
  (cond ((endp defs) nil)
        (t (cons (sesem-definition (car defs) prime state)
                 (sesem-definition-list (cdr defs) prime state)))))
