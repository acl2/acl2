; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "kestrel/std/system/defchoose-queries" :dir :system)
(include-book "kestrel/std/system/definedp" :dir :system)
(include-book "kestrel/std/system/defun-sk-queries" :dir :system)
(include-book "kestrel/std/system/function-symbol-listp" :dir :system)
(include-book "kestrel/std/system/measure" :dir :system)
(include-book "kestrel/std/system/uguard" :dir :system)
(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "std/alists/alist-equiv" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ soft-implementation-core
  :parents (soft-implementation)
  :short "Core implementation code of SOFT."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define *-listp (stars)
  :returns (yes/no booleanp)
  :short "Recognize true lists of @('*')s."
  :long
  (xdoc::topstring
   (xdoc::p
    "These lists are used to indicate
     the number of arguments of function variables
     in @(tsee defunvar).")
   (xdoc::p
    "Any @('*') symbol (i.e. in any package) is allowed.
     Normally, the @('*') in the current package should be used
     (without package qualifier),
     which is often the one from the main Lisp package,
     which other packages generally import."))
  (if (atom stars)
      (null stars)
    (and (symbolp (car stars))
         (equal (symbol-name (car stars)) "*")
         (*-listp (cdr stars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection function-variables-table
  :short "Table of function variables."
  :long
  (xdoc::topstring-p
   "The names of declared function variables
    are stored as keys in a @(tsee table).
    No values are associated to these keys, so the table is essentially a set.
    Note that the arity of a function variable
    can be retrieved from the @(see world).")

  (table function-variables nil nil :guard (and (symbolp acl2::key)
                                                (null acl2::val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funvarp (funvar (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize names of function variables."
  :long
  (xdoc::topstring-p
   "These are symbols that name declared function variables,
    i.e. that are in the table of function variables.")
  (let ((table (table-alist 'function-variables wrld)))
    (and (symbolp funvar)
         (not (null (assoc-eq funvar table))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funvar-listp (funvars (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recoegnize true lists of function variables."
  (if (atom funvars)
      (null funvars)
    (and (funvarp (car funvars) wrld)
         (funvar-listp (cdr funvars) wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection second-order-functions-table
  :short "Table of second-order functions."
  :long
  (xdoc::topstring-p
   "The names of declared second-order functions
    are stored as keys in a @(see table),
    associated with the function variables they depend on.")

  (table second-order-functions nil nil
    :guard (and (symbolp acl2::key)
                (funvar-listp acl2::val world))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sofunp (sofun (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize names of second-order functions."
  (let ((table (table-alist 'second-order-functions wrld)))
    (and (symbolp sofun)
         (not (null (assoc-eq sofun table))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sofun-kindp (kind)
  :returns (yes/no booleanp)
  :short "Recognize symbols that denote
          the kinds of second-order functions supported by SOFT."
  :long
  (xdoc::topstring
   (xdoc::p
    "Following the terminology used in the Workshop paper,
     in the implementation we use:")
   (xdoc::ul
    (xdoc::li
     "@('plain') for second-order functions introduced
      via @(tsee defun2).")
    (xdoc::li
     "@('choice') for second-order functions introduced
      via @(tsee defchoose2).")
    (xdoc::li
     "@('quant') for second-order functions introduced
      via @(tsee defun-sk2).")))
  (or (eq kind 'plain)
      (eq kind 'choice)
      (eq kind 'quant)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sofun-kind ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :returns (kind "A @(tsee sofun-kindp).")
  :verify-guards nil
  :short "Kind of a second-order function."
  (cond ((defchoosep sofun wrld) 'choice)
        ((defun-sk-p sofun wrld) 'quant)
        (t 'plain)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plain-sofunp (sofun (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize plain second-order functions."
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'plain)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define choice-sofunp (sofun (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize choice second-order functions."
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'choice)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define quant-sofunp (sofun (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize quantifier second-order functions."
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'quant)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sofun-funvars ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :verify-guards nil
  :short "Function variables that a second-order function depends on."
  (let ((table (table-alist 'second-order-functions wrld)))
    (cdr (assoc-eq sofun table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines funvars-of-term/terms
  :verify-guards nil
  :short "Function variables that terms depend on."
  :long
  (xdoc::topstring
   (xdoc::p
    "A term may depend on a function variable directly
     (when the function variable occurs in the term)
     or indirectly
     (when a the second-order function that occurs in the term
     depends on the function variable).")
   (xdoc::p
    "Note that, in the following code,
     if @('(sofunp fn wrld)') is @('nil'),
     then @('fn') is a first-order function,
     which depends on no function variables.")
   (xdoc::p
    "The returned list may contain duplicates.")
   (xdoc::@def "funvars-of-term")
   (xdoc::@def "funvars-of-terms"))

  (define funvars-of-term ((term pseudo-termp) (wrld plist-worldp))
    :returns (funvars "A @(tsee funvar-listp).")
    (if (or (variablep term)
            (quotep term))
        nil
      (let* ((fn (fn-symb term))
             (fn-vars
              (if (flambdap fn)
                  (funvars-of-term (lambda-body fn) wrld)
                (if (funvarp fn wrld)
                    (list fn)
                  (if (sofunp fn wrld)
                      (sofun-funvars fn wrld)
                    nil)))))
        (append fn-vars (funvars-of-terms (fargs term) wrld)))))

  (define funvars-of-terms ((terms pseudo-term-listp) (wrld plist-worldp))
    :returns (funvars "A @(tsee funvar-listp).")
    (if (endp terms)
        nil
      (append (funvars-of-term (car terms) wrld)
              (funvars-of-terms (cdr terms) wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funvars-of-plain-fn ((fun symbolp) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :mode :program
  :short "Function variables depended on
          by a plain second-order function or by an instance of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "Plain second-order functions and their instances
     may depend on function variables
     via their defining bodies,
     via their measures (absent in non-recursive functions),
     and via their guards.
     For now recursive second-order functions (which are all plain)
     and their instances
     are only allowed to use @(tsee o<) as their well-founded relation,
     and so plain second-order functions and their instances
     may not depend on function variables via their well-founded relations.")
   (xdoc::p
    "Note that if the function is recursive,
     the variable @('measure') in the following code is @('nil'),
     and @(tsee funvars-of-term) applied to that yields @('nil').")
   (xdoc::p
    "The returned list may contain duplicates."))
  (let* ((body (ubody fun wrld))
         (measure (if (recursivep fun nil wrld)
                      (measure fun wrld)
                    nil))
         (guard (uguard fun wrld))
         (body-funvars (funvars-of-term body wrld))
         (measure-funvars (funvars-of-term measure wrld))
         (guard-funvars (funvars-of-term guard wrld)))
    (append body-funvars
            measure-funvars
            guard-funvars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funvars-of-choice-fn ((fun symbolp) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :mode :program
  :short "Function variables depended on
          by a choice second-order function or by an instance of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "Choice second-order functions and their instances
     may depend on function variables via their defining bodies.")
   (xdoc::p
    "The returned list may contain duplicates."))
  (funvars-of-term (defchoose-body fun wrld) wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funvars-of-quantifier-fn ((fun symbolp) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :mode :program
  :short "Function variables depended on
          by a quantifier second-order function or by an instance of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "Quantifier second-order functions and their instances
     may depend on function variables
     via their matrices
     and via their guards (which are introduced via @(tsee declare) forms).")
   (xdoc::p
    "The returned list may contain duplicates."))
  (let* ((matrix (defun-sk-matrix fun wrld))
         (guard (uguard fun wrld))
         (matrix-funvars (funvars-of-term matrix wrld))
         (guard-funvars (funvars-of-term guard wrld)))
    (append matrix-funvars
            guard-funvars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funvars-of-thm ((thm symbolp) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :mode :program
  :short "Function variables depended on
          by a second-order theorem or by an instance of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "Second-order theorems and their instances
     may depend on function variables via their formulas.")
   (xdoc::p
    "The returned list may contain duplicates."))
  (funvars-of-term (formula thm nil wrld) wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sothmp ((sothm symbolp) (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :short "Recognize second-order theorems."
  :long
  (xdoc::topstring-p
   "A theorem is second-order iff
    it depends on one or more function variables.")
  (not (null (funvars-of-thm sothm wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define no-trivial-pairsp ((alist alistp))
  :returns (yes/no booleanp)
  :short "Check if an alist has no pairs with equal key and value."
  :long
  (xdoc::topstring-p
   "This is a constraint satisfied by function substitutions;
    see @(tsee fun-substp).
    A pair that substitutes a function with itself would have no effect,
    so such pairs are useless.")
  (if (endp alist)
      t
    (let ((pair (car alist)))
      (and (not (equal (car pair) (cdr pair)))
           (no-trivial-pairsp (cdr alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-substp (fsbs)
  :returns (yes/no booleanp)
  :short "Recognize function substitutions."
  :long
  (xdoc::topstring-p
   "A function substitution is an alist from function names to function names,
    with unique keys and with no trivial pairs.")
  (and (symbol-symbol-alistp fsbs)
       (no-duplicatesp (alist-keys fsbs))
       (no-trivial-pairsp fsbs))
  :guard-hints (("Goal" :in-theory (enable symbol-symbol-alistp)))
  :prepwork ((local (include-book "std/alists/alist-equiv" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funvar-instp (inst (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize instantiations."
  :long
  (xdoc::topstring-p
   "These are non-empty function substitutions
    whose keys are function variables and whose values are function names.")
  (and (fun-substp inst)
       (consp inst)
       (funvar-listp (alist-keys inst) wrld)
       (function-symbol-listp (alist-vals inst) wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funvar-inst-listp (insts (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize true lists of instantiations."
  (if (atom insts)
      (null insts)
    (and (funvar-instp (car insts) wrld)
         (funvar-inst-listp (cdr insts) wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sof-instancesp (instmap (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize the information about the instances
          that is associated to second-order function names
          in the @(tsee sof-instances) table."
  :long
  (xdoc::topstring-p
   "This is an alist from instantiations to function names.
    Each pair in the alist maps an instantiation
    to the corresponding instance.")
  (and (alistp instmap)
       (funvar-inst-listp (alist-keys instmap) wrld)
       (symbol-listp (alist-vals instmap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-sof-instance ((inst (funvar-instp inst wrld))
                          (instmap (sof-instancesp instmap wrld))
                          (wrld plist-worldp))
  :returns (instance symbolp
                     :hyp (sof-instancesp instmap wrld)
                     :hints (("Goal" :in-theory (enable sof-instancesp))))
  :verify-guards nil
  :short "Retrieve the instance associated to a given instantiation,
          in the map of known instances of a second-order function."
  :long
  (xdoc::topstring-p
   "Instantiations are treated as equivalent according to @(tsee alist-equiv).
    If no instance for the instantiation is found, @('nil') is returned.")
  (if (endp instmap)
      nil
    (let ((pair (car instmap)))
      (if (alist-equiv (car pair) inst)
          (cdr pair)
        (get-sof-instance inst (cdr instmap) wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define put-sof-instance ((inst (funvar-instp inst wrld))
                          (fun symbolp)
                          (instmap (and (sof-instancesp instmap wrld)
                                        (null
                                         (get-sof-instance inst instmap wrld))))
                          (wrld plist-worldp))
  :returns (new-instmap "A @(tsee sof-instancesp).")
  :verify-guards nil
  :short "Associates an instantiation with an instance
          in an existing map of know instances of a second-order function."
  :long
  (xdoc::topstring-p
   "The guard requires the absence of an instance for the same instantiation
    (equivalent up to @(tsee alist-equiv)).")
  (declare (ignore wrld)) ; only used in guard
  (acons inst fun instmap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection sof-instances-table
  :short "Table of instances of second-order functions."
  :long
  (xdoc::topstring-p
   "The known instances of second-order functions are stored in a @(see table).
    The keys are the names of second-order functions that have instances,
    and the values are alists from instantiations to instances.")

  (table sof-instances nil nil :guard (and (symbolp acl2::key)
                                           (sof-instancesp acl2::val world))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sof-instances ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :returns (instmap "A @(tsee sof-instancesp).")
  :verify-guards nil
  :short "Known instances of a second-order function."
  (let ((table (table-alist 'sof-instances wrld)))
    (cdr (assoc-eq sofun table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-subst-function ((fsbs fun-substp) (fun symbolp) (wrld plist-worldp))
  :returns (new-fun "A @(tsee symbolp).")
  :verify-guards nil
  :short "Apply a function substitution to an individual function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Applying an instantiation to a term involves replacing
     not only the function variables that are keys of the instantiation
     and that occur explicitly in the term,
     but also the ones that occur implicitly in the term
     via occurrences of second-order functions that depend on
     those function variables.
     For example, if @('ff') is a second-order function
     with function parameter @('f'),
     and an instantiation @('I') replaces @('f') with @('g'),
     applying @('I') to the term @('(cons (f x) (ff y))')
     should yield the term @('(cons (g x) (gg y))'),
     where @('gg') is the instance that results form applying @('I') to @('ff').
     The @(tsee sof-instances) table is used to find @('gg'):
     @('I') is restricted to the function parameters of @('ff')
     before searching the map of instances of @('ff');
     if the restriction is empty, @('gg') is @('ff'),
     i.e. no replacement takes place.
     If @('gg') does not exist,
     the application of @('I') to @('(cons (f x) (ff y))') fails;
     the user must create @('gg')
     and try applying @('I') to @('(cons (f x) (ff y))') again.")
   (xdoc::p
    "When an instantiation is applied
     to the body of a recursive second-order function @('sofun')
     to obtain an instance @('fun'),
     occurrences of @('sofun') in the body must be replaced with @('fun'),
     but at that time @('fun') does not exist yet,
     and thus the table of second-order function instances of @('sofun')
     has no entries for @('fun') yet.
     Thus, it is convenient to use function substitutions
     (not just instantiations)
     to instantiate terms.")
   (xdoc::p
    "The following code applies a function substitution to an individual function,
     in the manner explained above.
     It is used by @(tsee fun-subst-term),
     which applies a function substitution to a term.
     If a needed second-order function instance does not exist,
     an error occurs."))
  (let ((pair (assoc-eq fun fsbs)))
    (if pair
        (cdr pair)
      (if (sofunp fun wrld)
          (let* ((funvars (sofun-funvars fun wrld))
                 (subfsbs (restrict-alist funvars fsbs)))
            (if (null subfsbs)
                fun
              (let* ((instmap (sof-instances fun wrld))
                     (new-fun (get-sof-instance subfsbs instmap wrld)))
                (if new-fun
                    new-fun
                  (raise "~x0 has no instance for ~x1." fun fsbs)))))
        fun))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines fun-subst-term/terms
  :verify-guards nil
  :short "Apply function substitutions to terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the discussion in @(tsee fun-subst-function).")
   (xdoc::@def "fun-subst-term")
   (xdoc::@def "fun-subst-terms"))

  (define fun-subst-term
    ((fsbs fun-substp) (term pseudo-termp) (wrld plist-worldp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (if (or (variablep term)
            (quotep term))
        term
      (let* ((fn (fn-symb term))
             (new-fn (if (symbolp fn)
                         (fun-subst-function fsbs fn wrld)
                       (make-lambda (lambda-formals fn)
                                    (fun-subst-term fsbs
                                                    (lambda-body fn)
                                                    wrld))))
             (new-args (fun-subst-terms fsbs (fargs term) wrld)))
        (cons new-fn new-args))))

  (define fun-subst-terms
    ((fsbs fun-substp) (terms pseudo-term-listp) (wrld plist-worldp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (if (endp terms)
        nil
      (cons (fun-subst-term fsbs (car terms) wrld)
            (fun-subst-terms fsbs (cdr terms) wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ext-fun-subst-term/terms/function
  :mode :program
  :short "Extend function substitutions for functional instantiation."
  :long
  (xdoc::topstring
   (xdoc::p
    "An instance @('thm') of a second-order theorem @('sothm')
     is also a theorem,
     provable using a @(':functional-instance') of @('sothm').
     The pairs of the @(':functional-instance') are
     not only the pairs of the instantiation
     that creates @('thm') from @('sothm'),
     but also all the pairs
     whose first components are
     second-order functions that @('sothm') depends on
     and whose second components are the corresponding instances.")
   (xdoc::p
    "For example,
     if @('sothm') is @('(p (sofun x))'),
     @('sofun') is a second-order function,
     @('p') is a first-order predicate,
     and applying an instantiation @('I') to @('(p (sofun x))')
     yields @('(p (fun x))'),
     then @('thm') is proved using
     @('(:functional-instance sothm (... (sofun fun) ...))'),
     where the first @('...') are the pairs of @('I')
     and the second @('...') are further pairs
     of second-order functions and their instances,
     e.g. if @('sofun') calls a second-order function @('sofun1'),
     the pair @('(sofun1 fun1)') must be in the second @('...'),
     where @('fun1') is the instance of @('sofun1') corresponding to @('I').
     All these pairs are needed to properly instantiate
     the constraints that arise from the @(':functional-instance'),
     which involve the second-order functions that @('sothm') depends on,
     directly or indirectly.")
   (xdoc::p
    "The following code extends a function substitution
     (initially an instantiation)
     to contain all those extra pairs.
     The starting point is a term;
     the bodies of second-order functions referenced in the term
     are recursively processed.
     The table of instances of second-order functions is searched,
     similarly to @(tsee fun-subst-function).")
   (xdoc::@def "ext-fun-subst-term")
   (xdoc::@def "ext-fun-subst-terms")
   (xdoc::@def "ext-fun-subst-function"))

  (define ext-fun-subst-term
    ((term pseudo-termp) (fsbs fun-substp) (wrld plist-worldp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (if (or (variablep term)
            (quotep term))
        fsbs
      (let* ((fn (fn-symb term))
             (fsbs (if (symbolp fn)
                       (ext-fun-subst-function fn fsbs wrld)
                     (ext-fun-subst-term (lambda-body fn) fsbs wrld))))
        (ext-fun-subst-terms (fargs term) fsbs wrld))))

  (define ext-fun-subst-terms
    ((terms pseudo-term-listp) (fsbs fun-substp) (wrld plist-worldp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (if (endp terms)
        fsbs
      (let ((fsbs (ext-fun-subst-term (car terms) fsbs wrld)))
        (ext-fun-subst-terms (cdr terms) fsbs wrld))))

  (define ext-fun-subst-function
    ((fun symbolp) (fsbs fun-substp) (wrld plist-worldp))
    :returns (new-fun "A @(tsee symbolp).")
    (cond
     ((assoc fun fsbs) fsbs)
     ((sofunp fun wrld)
      (b* ((funvars (sofun-funvars fun wrld))
           (subfsbs (restrict-alist funvars fsbs))
           ((if (null subfsbs)) fsbs)
           (instmap (sof-instances fun wrld))
           (funinst (get-sof-instance subfsbs instmap wrld))
           ((unless funinst)
            (raise "~x0 has no instance for ~x1." fun fsbs))
           (fsbs (acons fun funinst fsbs)))
        (case (sofun-kind fun wrld)
          ((plain quant) (ext-fun-subst-term (ubody fun wrld) fsbs wrld))
          (choice (ext-fun-subst-term (defchoose-body fun wrld) fsbs wrld)))))
     (t fsbs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sothm-inst-pairs ((fsbs fun-substp) (wrld plist-worldp))
  :returns (pairs "A @('doublet-listp').")
  :mode :program
  :short "Create a list of doublets for functional instantiation."
  :long
  (xdoc::topstring
   (xdoc::p
    "From a function substitution obtained by extending an instantiation
     via @(tsee ext-fun-subst-term/terms/function),
     the list of pairs to supply to @(':functional-instance') is obtained.
     Each dotted pair is turned into a doublet
     (a different representation of the pair).")
   (xdoc::p
    "In addition, when a dotted pair is encountered
     whose @(tsee car) is the name of a quantifier second-order function,
     an extra pair for instantiating the associated witness is inserted.
     The witnesses of quantifier second-order functions
     must also be part of the @(':functional-instance'),
     because they are referenced by the quantifier second-order functions.
     However, these witnesses are not recorded as second-order functions
     in the table of second-order functions,
     and thus the code of @(tsee ext-fun-subst-term/terms/function)
     does not catch these witnesses."))
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (if (quant-sofunp 1st wrld)
          (let ((1st-wit (defun-sk-witness 1st wrld))
                (2nd-wit (defun-sk-witness 2nd wrld)))
            (cons (list 1st 2nd)
                  (cons (list 1st-wit 2nd-wit)
                        (sothm-inst-pairs (cdr fsbs) wrld))))
        (cons (list 1st 2nd)
              (sothm-inst-pairs (cdr fsbs) wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sothm-inst-facts ((fsbs fun-substp) (wrld plist-worldp))
  :returns (fact-names "A @(tsee symbol-listp).")
  :mode :program
  :short "Create list of facts for functional instantiation."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a @(':functional-instance') is used in a proof,
     proof subgoals are created to ensure that the replacing functions
     satisfy all the constraints of the replaced functions.
     In a @(':functional-instance') with a function substitution @('S')
     as calculated by @(tsee ext-fun-subst-term/terms/function),
     each function variable (which comes from the instantiation)
     has no constraints and so no subgoals are generated for them.
     Each second-order function @('sofun') in @('S')
     has the following constraints:")
   (xdoc::ul
    (xdoc::li
     "If @('sofun') is a plain second-order function,
      the constraint is that
      the application of @('S') to the definition of @('sofun') is a theorem,
      which follows by the construction of the instance @('fun') of @('sofun'),
      i.e. it follows from the definition of @('fun').")
    (xdoc::li
     "If @('sofun') is a choice second-order function,
      the constraint is that
      the application of @('S') to the choice axiom of @('sofun') is a theorem,
      which follows by the construction of the instance @('fun') of @('sofun'),
      i.e. it follows from the choice axiom of @('fun').")
    (xdoc::li
     "If @('sofun') is a quantifier second-order function,
      the constraints are that
      (1) the application of @('S')
      to the rewrite rule generated by the @(tsee defun-sk) of @('sofun'),
      and (2) the application of @('S') to the definition of @('sofun')
      (or to the defining theorem of @('sofun')
      if @('sofun') was introduced with @(':constrain t')),
      are both theorems,
      which both follow by the construction
      of the instance @('fun') of @('sofun'),
      i.e. they follow from
      (1) the rewrite rule generated by the @(tsee defun-sk) of @('fun')
      and (2) the definition of @('fun')
      (or the defining theorem of @('fun')
      if @('fun') was introduced with @(':constrain nil'))."))
   (xdoc::p
    "The list of facts needed to prove these constraints is determined
     by the function substitution @('S').
     For each pair @('(fun1 . fun2)') of the function substitution:")
   (xdoc::ul
    (xdoc::li
     "If @('fun1') is a plain second-order function,
      the fact used in the proof is the definition of @('fun2'),
      whose name is the name of @('fun2').
      (Note that by construction, since @('fun2') is an instance of @('fun1'),
      @('fun2') is introduced by a @(tsee defun).)")
    (xdoc::li
     "If @('fun1') is a choice second-order function,
      the fact used in the proof is the @(tsee defchoose) axiom of @('fun2'),
      whose name is the name of @('fun2').
      (Note that by construction, since @('fun2') is an instance of @('fun1'),
      @('fun2') is introduced by a @(tsee defchoose).)")
    (xdoc::li
     "If @('fun1') is a quantifier second-order function,
      the facts used in the proof are
      (1) the @(tsee defun-sk) rewrite rule of @('fun2')
      and (2)
      either (i) the definition of @('fun2')
      (if @('fun2') was introduced with @(':constrain nil')),
      whose name is the name of @('fun2'),
      or (ii) the defining theorem of @('fun2')
      (if @('fun2') was introduced with @(':constrain t')),
      whose name is @('fun2') followed by @('-definition').
      (Note that by construction, since @('fun2') is an instance of @('fun1'),
      @('fun2') is introduced by a @(tsee defun-sk).)")
    (xdoc::li
     "Otherwise, @('fun1') is a function variable, which has no constraints,
      so no fact is used in the proof.")))
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (cond ((or (plain-sofunp 1st wrld)
                 (choice-sofunp 1st wrld))
             (cons 2nd (sothm-inst-facts (cdr fsbs) wrld)))
            ((quant-sofunp 1st wrld)
             `(,(defun-sk-rewrite-name 2nd wrld)
               ,(if (definedp 2nd wrld)
                    2nd
                  (defun-sk-definition-name 2nd wrld))
               ,@(sothm-inst-facts (cdr fsbs) wrld)))
            (t (sothm-inst-facts (cdr fsbs) wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sothm-inst-proof
  ((sothm symbolp) (fsbs fun-substp) (wrld plist-worldp))
  :returns (instructions "A @(tsee true-listp).")
  :mode :program
  :short "Proof builder instructions to prove
          instances of second-order theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "Instances of second-order theorems are proved using the ACL2 proof builder.
     Each such instance is proved by
     first using the @(':functional-instance')
     determined by @(tsee sothm-inst-pairs),
     then using the facts computed by @(tsee sothm-inst-facts) on the subgoals.
     Each sugoal only needs a subset of those facts,
     but for simplicity all the facts are used for each subgoal,
     using the proof builder
     <see topic='@(url acl2-pc::repeat)'>@(':repeat')</see> command.
     Since sometimes the facts are not quite identical to the subgoals,
     the proof builder
     <see topic='@(url acl2-pc::prove)'>@(':prove')</see> command
     is used to iron out any such differences."))
  `(:instructions
    ((:use (:functional-instance ,sothm ,@(sothm-inst-pairs fsbs wrld)))
     (:repeat (:then (:use ,@(sothm-inst-facts fsbs wrld)) :prove)))))
