; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "type-annotation")
(include-book "var-reuse")

(include-book "../name-translation")

(include-book "kestrel/std/system/all-free-bound-vars" :dir :system)
(include-book "std/typed-alists/symbol-pos-alistp" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-var-renaming
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          renaming of the ACL2 variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "We systematically rename all the ACL2 variables
     so that their new names are valid Java variable names
     and so that different ACL2 variables with the same name are renamed apart,
     unless the variables have been marked for reuse
     by the previous pre-translation step.
     This simplifies the ACL2-to-Java translation,
     which can just turn each ACL2 variable
     into a Java variable with the same name."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-init-indices*
  :short "Initial variable index alist."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we rename ACL2 variables to Java variables,
     we must avoid the names in @(tsee *atj-disallowed-jvar-names*).
     We do that by initializing the alist from variables to indices
     to associate index 1 to all the disallowed names.
     That is, we pretend that
     variables with the disallowed names have already been used,
     so that an index 1 (or greater) will be appended to any variable
     that would otherwise happen to be a disallowed name.
     Appending an index to a disallowed name always yields an allowed name.")
   (xdoc::p
    "Note that @(tsee *atj-disallowed-jvar-names*) is a list of strings,
     but the keys of the index map must be symbols.
     We use @(tsee str::intern-list) to convert them.
     It is critical to use the same package (currently @('\"JAVA\"'))
     used by @(tsee atj-var-to-jvar)."))
  (pairlis$ (str::intern-list *atj-disallowed-jvar-names* (pkg-witness "JAVA"))
            (repeat (len *atj-disallowed-jvar-names*) 1))
  ///
  (assert-event (symbol-pos-alistp *atj-init-indices*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formal ((var symbolp)
                           (indices symbol-pos-alistp)
                           (curr-pkg stringp)
                           (vars-by-name string-symbollist-alistp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-var symbolp)
               (new-indices symbol-pos-alistp
                            :hyp (and (symbol-pos-alistp indices)
                                      (symbolp var))))
  :short "Rename a formal parameters of
          a defined function or lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-rename-formals),
     the renaming of a variable is established
     when the variable is encountered as a formal parameter.
     This motivates the name of this function.")
   (xdoc::p
    "This function is called only on formal parameters marked as `new'.
     Formal parameters marked as `old' are just renamed
     according to the existing renaming map @('renaming-old').")
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
    "We use @(tsee atj-var-to-jvar) to turn @('var')
     into a new symbol whose name is a valid Java variable name.
     Then we ensure its uniqueness by retrieving and using the next index,
     from the parameter @('indices'); more on this below.
     In general, as mentioned in @(tsee atj-var-to-jvar),
     we append the index after the result of @(tsee atj-var-to-jvar);
     but if the index is 0, we do not append it, to improve readability;
     in particular, if there is just one variable with a certain name,
     since we start with index 0, no index is ever added to the name.
     When this function is called,
     the indices alist always associates non-0 indices to
     the symbols whose names are in @(tsee *atj-disallowed-jvar-names*):
     see @(tsee *atj-init-indices*).")
   (xdoc::p
    "The name obtained by optionally appending the index
     may not be a valid Java identifier:
     this happens if it is a Java keyword or literal, or if it is empty.
     (This may actually happen only if no index is appended.)
     If this is the case, we add a single @('$') at the end,
     which makes the name valid and unambiguous.")
   (xdoc::p
    "The index to use for this variable
     is retrieved from the @('indices') parameter,
     which is an alist that associates each variable to its next index to use.
     If a variable is not in the alist, it is as if it had index 0,
     and in that case no index is added, as explained above.
     The alist is updated
     by incrementing the next index to use for the variable,
     and returned along with the new variable.")
   (xdoc::p
    "The keys of the alist are not the original ACL2 variables,
     but the renamed variables resulting from @(tsee atj-var-to-jvar).
     This gives us more flexibility,
     by obviating the requirement that @(tsee atj-var-to-jvar) be injective:
     if this function is not injective,
     then different ACL2 variables may become the same Java variable,
     and the next index must be the same for all of these variables,
     so that they can be properly disambiguated.")
   (xdoc::p
    "This pre-translation step is performed
     after the type annotation and new/old marking steps,
     but the caller of this function decomposes the marked annotated variable
     into its unmarked unannotated name, type, and marking,
     and only passes the unannotated name @('var') to this function.
     The @('vars-by-name') parameter of this function
     consists of variable names without annotations and markings."))
  (b* ((jvar (atj-var-to-jvar var curr-pkg vars-by-name))
       (jvar+index? (assoc-eq jvar indices))
       (index (if jvar+index? (cdr jvar+index?) 0))
       (indices (acons jvar (1+ index) indices))
       (jvar (atj-var-add-index jvar index)))
    (mv jvar indices))

  :prepwork
  ((defrulel returns-lemma
     (implies (posp x)
              (posp (1+ x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formals ((formals symbol-listp)
                            (renaming-new symbol-symbol-alistp)
                            (renaming-old symbol-symbol-alistp)
                            (indices symbol-pos-alistp)
                            (curr-pkg stringp)
                            (vars-by-name string-symbollist-alistp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-formals symbol-listp
                            :hyp (and (symbol-listp formals)
                                      (symbol-symbol-alistp renaming-new)))
               (new-renaming-new symbol-symbol-alistp
                                 :hyp (and (symbol-listp formals)
                                           (symbol-symbol-alistp renaming-new)))
               (new-renaming-old symbol-symbol-alistp
                                 :hyp (and (symbol-listp formals)
                                           (symbol-symbol-alistp renaming-old)))
               (new-indices symbol-pos-alistp
                            :hyp (and (symbol-listp formals)
                                      (symbol-pos-alistp indices))))
  :short "Rename the formal parameters of
          a defined function or lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-rename-formal),
     the shallowly embedded ACL2 variables are made unique via indices.
     There is an independent index for each ACL2 variable,
     so we use an alist from symbols to natural numbers
     to keep track of these indices.
     This alist is threaded through the functions
     that rename all the variables in ACL2 terms.
     This pre-translation step happens
     after the type annotation and new/old marking step,
     but the variables in this alist are without annotations and markings,
     because annotations and markings are discarded
     when generating Java variables,
     and thus two ACL2 variables that only differ in annotations or markings
     must be renamed apart and must share the same index in the alist.")
   (xdoc::p
    "In ACL2, a variable is ``introduced''
     as a formal parameter of a function or lambda expression,
     and then referenced in the body of the function or lambda expression.
     The choice and use of the index must be done at this introduction time,
     and not at every reference to the variable after its introduction.
     Thus, when we encounter the formals of a function or lambda expression,
     we generate the Java variable names for these ACL2 variables,
     using the current indices, and update and return the indices.
     This is the case only if the formal parameter is marked as `new';
     if instead it is marked as `old',
     we look it up in a renaming map,
     which is an alist from the old variable names to the new variable names,
     i.e. it expresses the current renaming of variables.
     There are actually two renaming alists:
     one for the variables marked as `new',
     and one for the variables marked as `old':
     see @(tsee atj-rename-term) for more information.
     This function takes both renaming maps,
     and augments both of them with the renamings for the formal parameters
     that are marked as `new'.
     The variables in the renaming maps are all type-annotated,
     for faster lookup when renaming variables in terms.
     The variables in the renaming maps are not marked as `new' or `old';
     as mentioned above, we have two separate maps for new and old variables.")
   (xdoc::p
    "Each ACL2 formal parameter in the input list
     is processed differently based on whether it is marked `new' or `old'.
     If it is marked `old',
     it is simply renamed according to the @('renaming-old') alist,
     which must include an entry for the variable.
     When it is marked as `new',
     it is unmarked and unannotated and passed to @(tsee atj-rename-formal),
     which uses and updates the index associated to the variable.")
   (xdoc::p
    "The formals @('formals') being renamed are annotated,
     because this pre-translation step happens after the type annotation step.
     Thus, the type annotations are removed prior to the renaming
     and added back after the renaming."))
  (b* (((when (endp formals)) (mv nil renaming-new renaming-old indices))
       (formal (car formals))
       ((mv uformal new?) (atj-unmark-var formal))
       ((when (not new?)) ; i.e. old
        (b* ((renaming-pair (assoc-eq uformal renaming-old))
             ((unless (consp renaming-pair))
              (raise "Internal error: ~x0 has no renaming." formal)
              (mv (true-list-fix formals)
                  renaming-new
                  renaming-old
                  indices))
             (new-uformal (cdr renaming-pair))
             (new-formal (atj-mark-var-old new-uformal))
             ((mv new-formals
                  renaming-new
                  renaming-old
                  indices) (atj-rename-formals (cdr formals)
                                               renaming-new
                                               renaming-old
                                               indices
                                               curr-pkg
                                               vars-by-name)))
          (mv (cons new-formal new-formals) renaming-new renaming-old indices)))
       ((mv uuformal types) (atj-type-unannotate-var uformal))
       ((mv new-uuformal indices)
        (atj-rename-formal uuformal indices curr-pkg vars-by-name))
       (new-uformal (atj-type-annotate-var new-uuformal types))
       (renaming-new (acons uformal new-uformal renaming-new))
       (renaming-old (acons uformal new-uformal renaming-old))
       (new-formal (atj-mark-var-new new-uformal))
       ((mv new-formals
            renaming-new
            renaming-old
            indices) (atj-rename-formals (cdr formals)
                                         renaming-new
                                         renaming-old
                                         indices
                                         curr-pkg
                                         vars-by-name)))
    (mv (cons new-formal new-formals) renaming-new renaming-old indices))

  ///

  (more-returns
   (new-formals true-listp :rule-classes :type-prescription))

  (defret len-of-atj-rename-formals.new-formals
    (equal (len new-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-rename-term
  :short "Rename all the ACL2 variables in an ACL2 term to their Java names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The alist from variables to indices
     is threaded through this function and its mutually recursive companion,
     in the same way as the renaming alist for the `old' variables;
     thus different variables in different Java scopes may have the same index.
     This alist contains variables without annotations or markings;
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "The renaming alist for variables marked as `new'
     is not threaded through:
     it is just passed down, according to ACL2's scoping.
     This alist contains variables with type annotations
     but without markings for `old' or `new';
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "The renaming alist for variables marked as `old'
     is threaded through instead,
     in the same way as the set of variables in scope in @(tsee atj-mark-term)
     (see that function for details).
     This is because variables are marked for reuse
     based (also) on that threading of the variables in scope:
     when we encounter a variable to rename that is marked for reuse,
     we must have its name available in the renaming alist.
     This alist contains variables with type annotations
     but without markings for `old' or `new';
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "If the term is a variable,
     it is unmarked,
     looked up in the appropriate renaming alist based on the marking,
     and replaced with the renamed variable, which is re-marked.
     Recall that variable names are generated
     via @(tsee atj-rename-formals) when variables are introduced,
     i.e. from formal parameters of defined functions and lambda expressions.")
   (xdoc::p
    "If the term is a quoted constant, it is obviously left unchanged.")
   (xdoc::p
    "If the term is a function call,
     its actual arguments are recursively processed,
     renaming all their variables.
     If the function is a named one, it is of course left unchanged.
     If instead it is a lambda expression,
     we process the renaming of its formal parameters,
     which in general augments the two renaming alists,
     and then recursively process the body of the lambda expression."))

  (define atj-rename-term ((term pseudo-termp)
                           (renaming-new symbol-symbol-alistp)
                           (renaming-old symbol-symbol-alistp)
                           (indices symbol-pos-alistp)
                           (curr-pkg stringp)
                           (vars-by-name string-symbollist-alistp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (new-term pseudo-termp)
                 (new-renaming-old symbol-symbol-alistp)
                 (new-indices symbol-pos-alistp))
    (b* (((unless (mbt (pseudo-termp term))) (mv nil nil nil))
         ((unless (mbt (symbol-symbol-alistp renaming-new))) (mv nil nil nil))
         ((unless (mbt (symbol-symbol-alistp renaming-old))) (mv nil nil nil))
         ((unless (mbt (symbol-pos-alistp indices))) (mv nil nil nil))
         ((unless (mbt (stringp curr-pkg))) (mv nil nil nil))
         ((unless (mbt (string-symbollist-alistp vars-by-name)))
          (mv nil nil nil))
         ((when (variablep term))
          (b* (((mv var new?) (atj-unmark-var term))
               (renaming-pair (assoc-eq var (if new?
                                                renaming-new
                                              renaming-old)))
               ((unless (consp renaming-pair))
                (raise "Internal error: no renaming found for variable ~x0."
                       term)
                (mv nil nil nil))
               (new-var (cdr renaming-pair))
               (new-term (if new?
                             (atj-mark-var-new new-var)
                           (atj-mark-var-old new-var))))
            (mv new-term renaming-old indices)))
         ((when (fquotep term)) (mv term renaming-old indices))
         (fn (ffn-symb term))
         ((when (eq fn 'if))
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3)))
            (if (equal test then)
                (b* (((mv new-test
                          renaming-old
                          indices) (atj-rename-term test
                                                    renaming-new
                                                    renaming-old
                                                    indices
                                                    curr-pkg
                                                    vars-by-name))
                     ((mv new-else
                          &
                          &) (atj-rename-term else
                                              renaming-new
                                              renaming-old
                                              indices
                                              curr-pkg
                                              vars-by-name)))
                  (mv `(if ,new-test ,new-test ,new-else)
                      renaming-old
                      indices))
              (b* (((mv new-test
                        renaming-old
                        indices) (atj-rename-term test
                                                  renaming-new
                                                  renaming-old
                                                  indices
                                                  curr-pkg
                                                  vars-by-name))
                   ((mv new-then
                        &
                        &) (atj-rename-term then
                                            renaming-new
                                            renaming-old
                                            indices
                                            curr-pkg
                                            vars-by-name))
                   ((mv new-else
                        &
                        &) (atj-rename-term else
                                            renaming-new
                                            renaming-old
                                            indices
                                            curr-pkg
                                            vars-by-name)))
                (mv `(if ,new-test ,new-then ,new-else)
                    renaming-old
                    indices)))))
         (args (fargs term))
         ((mv new-args
              renaming-old
              indices) (atj-rename-terms args
                                         renaming-new
                                         renaming-old
                                         indices
                                         curr-pkg
                                         vars-by-name))
         ((when (symbolp fn)) (mv (fcons-term fn new-args)
                                  renaming-old
                                  indices))
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         ((mv new-formals
              renaming-new
              renaming-old
              indices) (atj-rename-formals formals
                                           renaming-new
                                           renaming-old
                                           indices
                                           curr-pkg
                                           vars-by-name))
         ((mv new-body
              renaming-old
              indices) (atj-rename-term body
                                        renaming-new
                                        renaming-old
                                        indices
                                        curr-pkg
                                        vars-by-name)))
      (mv (fcons-term (make-lambda new-formals new-body)
                      new-args)
          renaming-old
          indices)))

  (define atj-rename-terms ((terms pseudo-term-listp)
                            (renaming-new symbol-symbol-alistp)
                            (renaming-old symbol-symbol-alistp)
                            (indices symbol-pos-alistp)
                            (curr-pkg stringp)
                            (vars-by-name string-symbollist-alistp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (new-terms (and (pseudo-term-listp new-terms)
                                 (equal (len new-terms) (len terms))))
                 (new-renaming-old symbol-symbol-alistp)
                 (new-indices symbol-pos-alistp))
    (b* (((unless (mbt (pseudo-term-listp terms)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (symbol-symbol-alistp renaming-new)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (symbol-symbol-alistp renaming-old)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (symbol-pos-alistp indices)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (stringp curr-pkg)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (string-symbollist-alistp vars-by-name)))
          (mv (repeat (len terms) nil) nil nil)))
      (cond ((endp terms) (mv nil renaming-old indices))
            (t (b* (((mv new-term
                         renaming-old
                         indices) (atj-rename-term (car terms)
                         renaming-new
                         renaming-old
                         indices
                         curr-pkg
                         vars-by-name))
                    ((mv new-terms
                         renaming-old
                         indices) (atj-rename-terms (cdr terms)
                         renaming-new
                         renaming-old
                         indices
                         curr-pkg
                         vars-by-name)))
                 (mv (cons new-term new-terms)
                     renaming-old
                     indices))))))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-rename-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formals+body ((formals symbol-listp)
                                 (body pseudo-termp)
                                 (curr-pkg stringp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-formals symbol-listp :hyp :guard)
               (new-body pseudo-termp :hyp :guard))
  :short "Rename all the ACL2 variables to their Java names,
          in the formal parameters and body of an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect all the variables in the formals and body,
     remove their markings and annotations
     (recall that the type annotation and new/old marking pre-translation steps
     take place before this renaming step),
     and organize them by symbol name:
     the resulting alist is passed to the renaming functions.")
   (xdoc::p
    "Starting with the empty alist of indices and the empty renaming alists,
     we introduce renamed variables for the formal parameters,
     and we use the resulting renaming alists to process the body."))
  (b* ((vars (union-eq formals (all-free/bound-vars body)))
       ((mv vars &) (atj-unmark-vars vars))
       (vars (atj-type-unannotate-vars vars))
       (vars-by-name (organize-symbols-by-name vars))
       ((mv new-formals renaming-new renaming-old indices)
        (atj-rename-formals
         formals nil nil *atj-init-indices* curr-pkg vars-by-name))
       ((mv new-body & &)
        (atj-rename-term
         body renaming-new renaming-old indices curr-pkg vars-by-name)))
    (mv new-formals new-body))
  ///

  (defret len-of-atj-rename-formals+body.new-formals
    (equal (len new-formals)
           (len formals))))
