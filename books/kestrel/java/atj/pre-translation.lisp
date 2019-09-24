; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "library-extensions")

(include-book "kestrel/std/system/all-free-bound-vars" :dir :system)
(include-book "kestrel/std/system/remove-mbe" :dir :system)
(include-book "kestrel/std/system/remove-progn" :dir :system)
(include-book "kestrel/std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "kestrel/utilities/strings/hexchars" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel natp-of-incremented-index
  (implies (natp x)
           (natp (1+ x))))

(defrulel posp-of-incremented-index
  (implies (posp x)
           (posp (1+ x))))

(local (in-theory (disable natp posp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation
  :parents (atj-code-generation)
  :short "Pre-translation performed by ATJ, as part of code generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-code-generation" "here")
    ", prior to generating Java code,
     ATJ performs an ACL2-to-ACL2 pre-translation.
     Currently, this pre-translation consists of the following steps:")
   (xdoc::ol
    (xdoc::li
     "In both the deep and shallow embedding,
      we remove all occurrences of @(tsee return-last).
      See @(tsee atj-remove-return-last).")
    (xdoc::li
     "In the shallow embedding, we rename all the ACL2 variables
      so that their names are valid Java variable names
      and so that different ACL2 variables with the same name are renamed apart.
      See @(tsee atj-rename-formals+body).")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-return-last ((term pseudo-termp) (guards$ booleanp))
  :returns (new-term pseudo-termp :hyp (pseudo-termp term))
  :short "Remove all the @(tsee return-last)s from a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "We selectively remove the @(':logic') or @(':exec') parts of @(tsee mbe)s
     (which are translated to @('(return-last 'mbe1-raw <exec> <logic>)'))
     based on the @(':guards') input.
     We remove all the non-last arguments of @(tsee prog2$)s and @(tsee progn$)s
     (which are translated to @('(return-last 'progn <non-last> <last>)')).
     These are the only @(tsee return-last) forms
     that make it through input validation."))
  (b* ((term (if guards$
                 (remove-mbe-logic-from-term term)
               (remove-mbe-exec-from-term term)))
       (term (remove-progn-from-term term)))
    term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-char-to-jchars-id ((char characterp)
                               (startp booleanp)
                               (flip-case-p booleanp))
  :returns (jchars character-listp :hyp (characterp char))
  :short "Turn an ACL2 character into one or more Java characters
          of an ASCII Java identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "For various purposes,
     we want to turn ACL2 symbols and package names into Java identifiers.
     ACL2 symbols may consist of arbitrary sequences of 8-bit characters,
     while Java identifiers may only contain certain Unicode characters;
     when Unicode is restricted to ASCII,
     Java identifiers are much more restricted than ACL2 symbols.
     They are also more restricted than ACL2 package names,
     although ACL2 package names have restrictions of their own
     compared to Java identifiers, notably the uppercase restriction.")
   (xdoc::p
    "If an ACL2 character (part of an ACL2 symbol or package name) is a letter,
     we keep it unchanged in forming the Java identifier,
     but we flip it from uppercase to lowercase or from lowercase to uppercase
     if the @('flip-case-p') flag is @('t'):
     since ACL2 symbols often have uppercase letters,
     by flipping them to lowercase we generate
     more readable and idiomatic Java identifiers;
     and flipping lowercase letters to uppercase letters avoids conflicts.
     If the ACL2 character is a digit, we keep it unchanged
     only if it is not at the start of the Java identifier:
     this is indicated by the @('startp') flag.
     Otherwise, we turn it into an ``escape'' consisting of
     @('$') followed by two hexadecimal digits for the ASCII code of the digit.
     We use this same mapping for all the ACL2 characters
     that are neither letters nor digits,
     except for dash, which is very common in ACL2 symbols and package names,
     and which we map into an underscore in Java,
     which is allowed in Java identifiers.
     The hexadecimal digits greater than 9 are uppercase.
     Note that @('$') itself, which is valid in Java identifiers,
     is mapped to itself followed by its hex code (not just to itself)
     when it appears in the ACL2 symbol or package name."))
  (cond ((str::up-alpha-p char) (if flip-case-p
                                    (list (str::downcase-char char))
                                  (list char)))
        ((str::down-alpha-p char) (if flip-case-p
                                      (list (str::upcase-char char))
                                    (list char)))
        ((and (digit-char-p char)
              (not startp)) (list char))
        ((eql char #\-) (list #\_))
        (t (b* ((acode (char-code char))
                ((mv hi-char lo-char) (ubyte8=>hexchars acode)))
             (list #\$ hi-char lo-char)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-chars-to-jchars-id ((chars character-listp)
                                (startp booleanp)
                                (flip-case-p booleanp))
  :returns (jchars character-listp :hyp (character-listp chars))
  :short "Lift @(tsee atj-char-to-jchars-id) to lists."
  :long
  (xdoc::topstring-p
   "This is used on the sequence of characters
    that form an ACL2 symbol or package name;
    see the callers of this function for details.
    The @('startp') flag becomes @('nil') at the first recursive call,
    because after the first character
    we are no longer at the start of the Java identifier.")
  (cond ((endp chars) nil)
        (t (append (atj-char-to-jchars-id (car chars) startp flip-case-p)
                   (atj-chars-to-jchars-id (cdr chars) nil flip-case-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-disallowed-jvar-names*
  :short "Disallowed Java variable names
          for the shallowly embedded ACL2 variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 variable is turned into a Java variable.
     The function @(tsee atj-chars-to-jchars-id) takes care of
     ensuring that only characters valid for Java identifiers are used,
     but this is not sufficient:
     a Java variable name cannot be a keyword,
     a boolean literal, or the null literal.")
   (xdoc::p
    "This constant collects these disallowed sequences of characters,
     which otherwise consist of valid Java identifier characters.
     It also includes the empty sequence,
     because an ACL2 symbol may consist of no characters,
     but a Java identifier cannot be empty."))
  (append *atj-java-keywords*
          *atj-java-boolean-literals*
          (list *atj-java-null-literal*)
          (list ""))
  ///
  (assert-event (string-listp *atj-disallowed-jvar-names*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-jvar-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-var ((var symbolp)
                        (index natp)
                        (curr-pkg stringp)
                        (vars-by-name string-symbollist-alistp))
  :guard (not (equal curr-pkg ""))
  :returns (new-var symbolp)
  :short "Rename an ACL2 variable to its Java name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 variable is turned into a Java variable:
     either a local variable or a method parameter.
     This function renames an ACL2 variable
     so that its name (without the package prefix)
     can be directly used as the name of the Java variable.")
   (xdoc::p
    "Each ACL2 function is turned into a Java method,
     whose body is a shallowly embedded representation
     of the ACL2 function body.
     The ACL2 function body may reference the ACL2 function's parameter,
     as well as @(tsee let)-bound variables (via lambda expressions).
     Thus, the same variable symbol may in fact denote different variables
     in different parts of an ACL2 function body.
     Java does not allow different local variables with the same name
     in (nested scopes in) the same method,
     and so we need to map homonymous but different ACL2 variables
     in the same ACL2 function
     to differently named Java variables
     in the same Java method.
     We use numeric indices, one for each variable name,
     which is appended (as explained below) to the Java variable name
     to make it unique within the Java mehtod.")
   (xdoc::p
    "Another need for disambiguation arises because of package prefixes.
     An ACL2 variable is a symbol,
     which consists of a name and also a package name:
     two distinct variables may have the same name
     but different package names.
     However, when we append the package name and the name of the symbol,
     we have unique Java variable names.")
   (xdoc::p
    "Systematically prefixing, in the generated Java variables,
     every symbol name with the package prefix affects readability.
     In ACL2, package prefixes are normally omitted
     for symbols in the current ACL2 package.
     Here we do something similar for the Java variable names,
     where the notion of current package is as follows.
     As mentioned above, each ACL2 function is turned into a Java method:
     this method is inside a Java class whose name is derived from
     the ACL2 package name of the function name:
     thus, the ``current package'' in this context is
     the one of the function name.
     This is the @('curr-pkg') parameter of this code generation function.")
   (xdoc::p
    "Given an ACL2 variable (i.e. symbol)
     with name @('name') and package name @('pname'),
     in general the generated Java variable name is
     @('<pname>$$$<name>$$<index>'),
     where @('<pname>') and @('<name>') are representations of the ACL2 names
     that are valid for Java identifiers,
     and @('<index>') is a decimal representation of the numeric index.")
   (xdoc::p
    "If @('<pname>') is the same as the current package,
     we omit @('<pname>$$$').
     We omit @('<pname>$$$') also when the variable
     is the only one with name @('<name>')
     within the ``current'' ACL2 function:
     since the scope of Java method parameters and local variables
     is limited to the method where they occur,
     no naming conflict may arise in this case.
     The parameter @('vars-by-name') consists of
     all the variables in the current ACL2 function,
     organized by symbol name for easy lookup.
     We retrieve the variables with the same name of the variable,
     we remove the variable being processed from them,
     and we check if the result is empty:
     in this case, this is the only variable with that name.
     (The alist may have duplicate symbols in its values.)")
   (xdoc::p
    "If the index is 0, we omit @('$$<index>'),
     so that if there is just one variable with a certain name,
     since we start with index 0, no index is added to the name.")
   (xdoc::p
    "Thus there are a few combinations possible with these three parts;
     the use of triple and double @('$') characters guarantees
     that there is no confusion with the @('$hh') escapes
     where @('hh') is the hex code of an ACL2 character
     that is not valid for a Java identifier.
     Furthermore, if the resulting variable name is just @('<name>')
     and happens to be a Java keyword or Java literal or empty,
     we add a single @('$') at the end, which again is unambiguous.")
   (xdoc::p
    "This is a relatively simple and uniform scheme to keep names unique,
     but we may improve it to generate more readable names.")
   (xdoc::p
    "We call @(tsee atj-chars-to-jchars-id) to create
     @('<pname') and @('<name>') from @('pname') and @('name').
     If there is a package prefix, the @('startp') flag is @('t')
     only for @('pname'), but not for @('name'),
     because @('<name>') is not the start of the Java identifier.
     Otherwise, @('startp') is @('t') for @('name')
     if there is no package prefix.")
   (xdoc::p
    "We put the renamed variable in the current package (i.e. @('curr-pkg')).
     The choice of package is irrelevant, because the variables in a function
     are renamed in a way that their names are all distinct
     regardless of package prefixes.
     However, using the current package makes things uniform."))
  (b* ((pkg (symbol-package-name var))
       (name (symbol-name var))
       (omit-pname? (or (equal pkg curr-pkg)
                        (null (remove-eq
                               var
                               (cdr (assoc-equal name vars-by-name))))))
       (pname$$$-jchars (if omit-pname?
                            nil
                          (append (atj-chars-to-jchars-id (explode pkg) t t)
                                  (list #\$ #\$ #\$))))
       (name-jchars (atj-chars-to-jchars-id (explode name)
                                            (endp pname$$$-jchars)
                                            t))
       ($$index-jchars (if (= index 0)
                           nil
                         (append (list #\$ #\$)
                                 (str::natchars index))))
       (jchars (append pname$$$-jchars name-jchars $$index-jchars))
       (new-name (implode jchars))
       (new-name (if (member-equal new-name *atj-disallowed-jvar-names*)
                     (str::cat new-name "$")
                   new-name)))
    (intern$ new-name curr-pkg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-vars ((vars symbol-listp)
                         (indices symbol-nat-alistp)
                         (curr-pkg stringp)
                         (vars-by-name string-symbollist-alistp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (renaming symbol-symbol-alistp :hyp (symbol-listp vars))
               (new-indices
                symbol-nat-alistp
                :hyp (and (symbol-listp vars)
                          (symbol-nat-alistp indices))))
  :short "Rename a sequence of ACL2 variables to their Java names."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-rename-var),
     the shallowly embedded ACL2 variables are made unique via indices.
     There is an independent index for each ACL2 variable,
     so we use an alist from symbols to natural numbers
     to keep track of these indices.
     This alist is threaded through the functions
     that rename all the variables in ACL2 terms.")
   (xdoc::p
    "In ACL2, a variable is ``introduced''
     as a formal parameter of a function or lambda expression,
     and then referenced in the body of the function or lambda expression.
     The choice and use of the index must be done at this introduction time,
     and not at every reference to the variable after its introduction.
     Thus, in the shallow embedding approach,
     when we encounter the formals of a function or lambda expression,
     we generate the Java variable names for these ACL2 variables,
     using the current indices, and update and return the indices.
     This function does that,
     and returns the renamed ACL2 variables as an alist
     from the old ACL2 variables to the new ACL2 variables,
     i.e. the renaming map.")
   (xdoc::p
    "Each ACL2 variable in the input list is processed as follows.
     If it has no index in the alist of indices,
     it has index 0,
     and the alist is extended to associate 1 (the next index) to the symbol.
     Otherwise, the index in the alist is used,
     and the alist is updated with the next index."))
  (b* (((when (endp vars)) (mv nil indices))
       (var (car vars))
       (var+index (assoc-eq var indices))
       (index (if (consp var+index) (cdr var+index) 0))
       (indices (acons var (1+ index) indices))
       ((mv renaming indices) (atj-rename-vars (cdr vars)
                                               indices
                                               curr-pkg
                                               vars-by-name)))
    (mv (acons var
               (atj-rename-var var index curr-pkg vars-by-name)
               renaming)
        indices))
  :verify-guards :after-returns
  :prepwork
  ((defrulel verify-guards-lemma
     (implies (natp x)
              (acl2-numberp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formals ((formals symbol-listp)
                            (renaming symbol-symbol-alistp))
  :returns (new-formals symbol-listp :hyp :guard)
  :short "Rename the formal parameters of
          a defined function or lambda expression
          according to a supplied renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used after calling @(tsee atj-rename-vars),
     which introduces the new names for the formal parameters.
     This function just looks up the names in the renaming alist
     and replaces them, returning a list of renamed parameters.")
   (xdoc::p
    "The reason for having this separate function,
     instead of having @(tsee atj-rename-var)
     also return the new list of variables,
     is motivated by the way lambda expression are treated:
     see @(tsee atj-rename-term).
     As explained there, the formal parameters of a lambda expression
     that are the same as the correspoding actual parameters
     are excluded from the call of @(tsee atj-rename-vars),
     so that the old variable names can be re-used.
     Thus, we must use the combined renaming
     not only on the body of the lambda expression,
     but also on its formal parameters:
     this function does that for the formal parameters.
     For uniformity, this function is also used when processing
     a function definition, in order to rename the formal parameters
     in a way that is consistent with the renamings in the body."))
  (cond ((endp formals) nil)
        (t (cons (cdr (assoc-eq (car formals) renaming))
                 (atj-rename-formals (cdr formals) renaming))))
  ///

  (defrule len-of-atj-rename-formals
    (equal (len (atj-rename-formals formals renaming))
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-rename-term
  :short "Rename all the ACL2 variables in an ACL2 term to their Java names."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the top level,
     this function is called on the body of a defined ACL2 function
     prior to translating its body into Java.
     This makes the translation to Java,
     because each ACL2 variable can be turned
     into a Java variable with same name.
     In other words, we factor the overall translation from ACL2 to Java
     by performing the renaming of variables from ACL2 to ACL2 first,
     and then turning the resulting ACL2 into Java.")
   (xdoc::p
    "The alist from variables to indices
     is threaded through this function and its mutually recursive companion.
     On the other hand, the renaming alist is just passed down.")
   (xdoc::p
    "If the term is a variable, it is looked up in the renaming alist,
     and replaced with the renamed variable.
     Recall that new variable names are generated
     via @(tsee atj-rename-var) and @(tsee atj-rename-vars),
     when variables are introduced,
     i.e. from formal parameters of defined functions and lambda expressions.
     When instead a variable occurrence is encountered in a term,
     it refers to the variable introduced in its surrounding scope,
     and thus the occurrence must be just replaced with the renamed variable.")
   (xdoc::p
    "If the term is a quoted constant, it is left unchanged.")
   (xdoc::p
    "If the term is a function application,
     its actual arguments are recursively processed,
     renaming all their variables.
     If the function is a named one, it is left unchanged.
     If instead it is a lambda expression,
     we introduce new variables renamings from its formal parameters,
     and then recursively process the body of the lambda expression.
     As an optimization,
     we exclude the formal parameters
     that are the same as their corresponding actual parameters
     (which happens often in ACL2: see @(tsee remove-unneeded-lambda-formals)),
     because for those we do not need to generate new Java variables,
     but can instead reference the existing variables.
     We append the newly generated renaming to the existing one,
     achieving the desired ``shadowing'' of the old mappings."))

  (define atj-rename-term ((term pseudo-termp)
                           (renaming symbol-symbol-alistp)
                           (indices symbol-nat-alistp)
                           (curr-pkg stringp)
                           (vars-by-name string-symbollist-alistp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (new-term pseudo-termp
                           :hyp (and (pseudo-termp term)
                                     (symbol-symbol-alistp renaming)))
                 (new-indices symbol-nat-alistp
                              :hyp (and (pseudo-termp term)
                                        (symbol-nat-alistp indices))))
    (cond ((variablep term) (mv (cdr (assoc-eq term renaming)) indices))
          ((fquotep term) (mv term indices))
          (t (b* ((fn (ffn-symb term))
                  (args (fargs term))
                  ((mv new-args
                       indices) (atj-rename-terms args
                                                  renaming
                                                  indices
                                                  curr-pkg
                                                  vars-by-name))
                  ((when (symbolp fn)) (mv (fcons-term fn new-args)
                                           indices))
                  (formals (lambda-formals fn))
                  (body (lambda-body fn))
                  (trimmed-formals (remove-unneeded-lambda-formals
                                    formals args))
                  ((mv new-renaming
                       indices) (atj-rename-vars trimmed-formals
                                                 indices
                                                 curr-pkg
                                                 vars-by-name))
                  (renaming (append new-renaming renaming))
                  (new-formals (atj-rename-formals formals renaming))
                  ((mv new-body
                       indices) (atj-rename-term body
                                                 renaming
                                                 indices
                                                 curr-pkg
                                                 vars-by-name)))
               (mv (fcons-term (make-lambda new-formals new-body)
                               new-args)
                   indices)))))

  (define atj-rename-terms ((terms pseudo-term-listp)
                            (renaming symbol-symbol-alistp)
                            (indices symbol-nat-alistp)
                            (curr-pkg stringp)
                            (vars-by-name string-symbollist-alistp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (new-terms (and (pseudo-term-listp new-terms)
                                 (equal (len new-terms) (len terms)))
                            :hyp (and (pseudo-term-listp terms)
                                      (symbol-symbol-alistp renaming)))
                 (new-indices symbol-nat-alistp
                              :hyp (and (pseudo-term-listp terms)
                                        (symbol-nat-alistp indices))))
    (cond ((endp terms) (mv nil indices))
          (t (b* (((mv new-term
                       indices) (atj-rename-term (car terms)
                                                 renaming
                                                 indices
                                                 curr-pkg
                                                 vars-by-name))
                  ((mv new-terms
                       indices) (atj-rename-terms (cdr terms)
                                                  renaming
                                                  indices
                                                  curr-pkg
                                                  vars-by-name)))
               (mv (cons new-term new-terms)
                   indices)))))

  :prepwork

  ((defrulel consp-of-assoc-equal
     (implies (alistp x)
              (iff (consp (assoc-equal k x))
                   (assoc-equal k x))))

   (defrulel alistp-when-symbol-symbol-alistp
     (implies (symbol-symbol-alistp x)
              (alistp x)))

   (defrulel pseudo-termp-when-symbolp
     (implies (symbolp x)
              (pseudo-termp x)))

   (defrulel true-listp-when-alistp
     (implies (alistp x)
              (true-listp x))))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-rename-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formals+body ((formals symbol-listp)
                                 (body pseudo-termp)
                                 (curr-pkg stringp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-formals symbol-listp :hyp (symbol-listp formals))
               (new-body pseudo-termp :hyp (and (pseudo-termp body)
                                                (symbol-listp formals))))
  :verify-guards nil
  :short "Rename all the ACL2 variables to their Java names,
          in the formal parameters and body of an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting with the empty alist of indices,
     we introduce renamed variables for the formal parameters.
     We use the renaming as the starting one to process the body."))
  (b* ((vars (union-eq formals (all-free/bound-vars body)))
       (vars-by-name (organize-symbols-by-name vars))
       ((mv renaming indices)
        (atj-rename-vars formals nil curr-pkg vars-by-name))
       (new-formals (atj-rename-formals formals renaming))
       ((mv new-body &)
        (atj-rename-term body renaming indices curr-pkg vars-by-name)))
    (mv new-formals new-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-pre-translate ((fn symbolp)
                           (formals symbol-listp)
                           (body pseudo-termp)
                           (deep$ booleanp)
                           (guards$ booleanp))
  :returns (mv (new-formals symbol-listp :hyp :guard)
               (new-body pseudo-termp :hyp :guard))
  :verify-guards nil
  :short "Pre-translate the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done before the translation from ACL2 to Java proper.")
   (xdoc::p
    "The pre-translation steps are described "
    (xdoc::seetopic "atj-pre-translation" "here")
    "."))
  (b* ((body (atj-remove-return-last body guards$))
       ((when deep$) (mv formals body)))
    (atj-rename-formals+body formals body (symbol-package-name fn))))
