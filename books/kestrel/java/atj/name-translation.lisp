; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "aij-notions")

(include-book "../language/keywords")
(include-book "../language/boolean-literals")
(include-book "../language/null-literal")

(include-book "kestrel/std/basic/organize-symbols-by-name" :dir :system)
(include-book "kestrel/utilities/strings/hexchars" :dir :system)
(include-book "std/typed-alists/string-string-alistp" :dir :system)
(include-book "std/typed-alists/symbol-string-alistp" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-name-translation
  :parents (atj-code-generation)
  :short "Translation of ACL2 names to Java names performed by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "Translating ACL2 to Java involves
     translating ACL2 names (of packages, functions, and variables)
     to corresponding Java names.
     The rules for what constitutes a valid Java name
     differ from the rules for what constitutes a valid ACL2 name,
     necessitating a non-identity translation mapping.")
   (xdoc::p
    "For certain purposes, we also need to translate ACL2 characters and strings
     to (parts of) valid Java identifiers.
     The issues here are similar to the ones arising
     when converting ACL2 names to Java names."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-char-to-jchars-id ((char characterp)
                               (startp booleanp)
                               (uscore (member-eq uscore '(nil :dash :space)))
                               (flip-case-p booleanp))
  :returns (jchars character-listp :hyp (characterp char))
  :short "Turn an ACL2 character into one or more Java characters
          for an ASCII Java identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to translate ACL2 variable, function, and package names
     to Java identifiers in the shallow embedding approach.
     It is also used to map ACL2 characters and strings
     to parts of Java identifiers.")
   (xdoc::p
    "ACL2 symbol names may consist of arbitrary sequences of 8-bit characters,
     while Java identifiers may only contain certain Unicode characters;
     when Unicode is restricted to ASCII,
     Java identifiers are much more restricted than ACL2 symbols.
     They are also more restricted than ACL2 package names,
     although ACL2 package names have restrictions of their own
     compared to Java identifiers, notably the uppercase restriction.")
   (xdoc::p
    "If an ACL2 character (part of an ACL2 symbol name or package name)
     is a letter,
     we keep it unchanged in forming the Java identifier,
     but we flip it from uppercase to lowercase or from lowercase to uppercase
     if the @('flip-case-p') flag is @('t'):
     since ACL2 symbols often have uppercase letters,
     by flipping them to lowercase we generate
     more readable and idiomatic Java identifiers;
     and flipping lowercase letters to uppercase letters avoids conflicts
     with ACL2 symbols that already have lowercase letters.
     On the other hand, since ACL2 package names cannot use lowercase letters,
     the @('flip-case-p') is @('nil') when we translate package names.")
   (xdoc::p
    "If the ACL2 character is a digit, we keep it unchanged
     only if it is not at the start of the Java identifier:
     this is indicated by the @('startp') flag.
     If the digit is at the start of the Java identifier,
     we turn it into an ``escape'' @('$<digit>$'):
     see the @('*atj-char-to-jchars-id*') alist.")
   (xdoc::p
    "If the ACL2 character is neither a letter or a digit,
     by default we turn it into an ``escape'' of the form @('$...').
     For the printable ASCII characters that are not letters,
     we use the readable descriptions in the @('*atj-char-to-jchars-id*') alist,
     e.g. @('HASH') for @('#').
     For each of the other ISO 8859-1 characters
     (non-ASCII, or non-printable ASCII),
     we use a description that consists of @('x') (for `hexadecimal')
     followed by the two hex digits that form the code of the character.
     The hexadecimal digits greater than 9 are all uppercase.")
   (xdoc::p
    "However, if the @('uscore') parameter is non-@('nil'),
     we turn the character indicated by @('uscore') into an underscore instead.
     The possible non-@('nil') values of @('uscore')
     are @(':dash') and @(':space').
     The value @(':dash') is used when translating ACL2 names to Java names:
     in ACL2 names, dash is a very common ``separator'';
     thus, we map that to an underscore in Java,
     which fulfills a similar separation role.
     The value @(':space') is used when translating ACL2 strings
     to parts of Java identifiers:
     in strings, space is perhaps a common character
     (at least for human-readable strings),
     and so by mapping that to an underscore,
     we retain some of the readability.")
   (xdoc::@def "*atj-char-to-jchars-id*"))
  (b* (((when (str::up-alpha-p char)) (if flip-case-p
                                          (list (str::downcase-char char))
                                        (list char)))
       ((when (str::down-alpha-p char)) (if flip-case-p
                                            (list (str::upcase-char char))
                                          (list char)))
       ((when (and (digit-char-p char)
                   (not startp)))
        (list char))
       ((when (or (and (eq uscore :dash)
                       (eql char #\-))
                  (and (eq uscore :space)
                       (eql char #\Space)))) (list #\_))
       (pair? (assoc char *atj-char-to-jchars-id*))
       ((when (consp pair?)) (explode (cdr pair?)))
       (code (char-code char))
       ((mv hi-char lo-char) (ubyte8=>hexchars code)))
    (list #\$ #\x hi-char lo-char))

  :prepwork
  ((defconst *atj-char-to-jchars-id*
     '((#\Space . "$SPACE")
       (#\! . "$BANG")
       (#\" . "$DQUOTE")
       (#\# . "$HASH")
       (#\$ . "$DOLLAR")
       (#\% . "$PCENT")
       (#\& . "$AMPER")
       (#\' . "$SQUOTE")
       (#\( . "$OROUND")
       (#\) . "$CROUND")
       (#\* . "$STAR")
       (#\+ . "$PLUS")
       (#\, . "$COMMA")
       (#\- . "$DASH")
       (#\. . "$DOT")
       (#\/ . "$SLASH")
       (#\: . "$COLON")
       (#\; . "$SCOLON")
       (#\< . "$LT")
       (#\= . "$EQ")
       (#\> . "$GT")
       (#\? . "$QMARK")
       (#\@ . "$AT")
       (#\[ . "$OSQUARE")
       (#\\ . "$BSLASH")
       (#\] . "$CSQUARE")
       (#\^ . "$CARET")
       (#\_ . "$USCORE")
       (#\` . "$BQUOTE")
       (#\{ . "$OCURLY")
       (#\| . "$BAR")
       (#\} . "$CCURLY")
       (#\~ . "$TILDE")
       (#\0 . "$0$")
       (#\1 . "$1$")
       (#\2 . "$2$")
       (#\3 . "$3$")
       (#\4 . "$4$")
       (#\5 . "$5$")
       (#\6 . "$6$")
       (#\7 . "$7$")
       (#\8 . "$8$")
       (#\9 . "$9$")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-chars-to-jchars-id ((chars character-listp)
                                (startp booleanp)
                                (uscore (member-eq uscore '(nil :dash :space)))
                                (flip-case-p booleanp))
  :returns (jchars character-listp :hyp (character-listp chars))
  :short "Lift @(tsee atj-char-to-jchars-id) to lists."
  :long
  (xdoc::topstring-p
   "This is used on the sequence of characters
    that form an ACL2 symbol name or package name.
    The @('startp') flag becomes @('nil') at the first recursive call,
    because after the first character
    we are no longer at the start of the Java identifier.")
  (cond ((endp chars) nil)
        (t (append
            (atj-char-to-jchars-id (car chars) startp uscore flip-case-p)
            (atj-chars-to-jchars-id (cdr chars) nil uscore flip-case-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-var-to-jvar ((var symbolp)
                         (curr-pkg stringp)
                         (vars-by-name string-symbollist-alistp))
  :returns (jvar symbolp)
  :short "Turn an ACL2 variable into a Java variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('var') has name @('name') and package name @('pname'),
     in general we return the symbol @('java::<pname>$$<name>'),
     where @('<pname>') and @('<name>') are representations of the ACL2 names
     that are valid for Java identifiers.
     This is not necessarily the final name of the Java variable:
     in general, a numeric index is added at the end,
     via @(tsee atj-var-add-index).
     So the final name of the Java variable has generally the form
     @('java::<pname>$$<name>$<index>').")
   (xdoc::p
    "Back to this function, which just produces @('java::<pname>$$<name>'),
     note that the package of the new symbol is always @('\"JAVA\"').
     Other choices are possible, but the point is that we want to ignore it.
     We incorporate the original package name @('pname')
     into the new symbol name and deal with just the symbol name afterwards,
     for greater simplicity.
     If this package is ever changed,
     it must be changed accordingly in @(tsee *atj-init-indices*).")
   (xdoc::p
    "Systematically prefixing, in the generated Java variables,
     every symbol name with the package prefix affects readability.
     In ACL2, package prefixes are normally omitted
     for symbols in the current ACL2 package.
     Here we do something similar for the Java variable names,
     where the notion of current package is as follows:
     in the shallow embedding approach,
     each ACL2 function is turned into a Java method,
     and this method is inside a Java class whose name is derived from
     the ACL2 package name of the function name;
     thus, the ``current package'' in this context is
     the one of the function name, which is the @('curr-pkg') parameter.
     If @('<pname>') is the same as the current package,
     we omit @('<pname>$$').
     We omit @('<pname>$$') also when the variable
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
     in this case, this is the only variable with that name.")
   (xdoc::p
    "We call @(tsee atj-chars-to-jchars-id) to create
     @('<pname>') and @('<name>') from @('pname') and @('name').
     If there is a package prefix, the @('startp') flag is @('t')
     only for @('pname'), but not for @('name'),
     because @('<name>') is not the start of the Java identifier.
     Otherwise, @('startp') is @('t') for @('name')
     if there is no package prefix.")
   (xdoc::p
    "The variable @('var') passed to this function
     is without markings or annotations.
     The called removes them before calling this function."))
  (b* ((pname (symbol-package-name var))
       (name (symbol-name var))
       (omit-pname? (or (equal pname curr-pkg)
                        (null (remove-eq
                               var
                               (cdr (assoc-equal name vars-by-name))))))
       (pname$$-jchars (if omit-pname?
                           nil
                         (append (atj-chars-to-jchars-id
                                  (explode pname) t :dash t)
                                 (list #\$ #\$))))
       (name-jchars (atj-chars-to-jchars-id
                     (explode name) (endp pname$$-jchars) :dash t))
       (jchars (append pname$$-jchars name-jchars))
       (new-name (implode jchars))
       ;; keep package below in sync with *ATJ-INIT-INDICES*:
       (new-var (intern$ new-name "JAVA")))
    new-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-var-add-index ((var symbolp) (index natp))
  :returns (new-var symbolp)
  :short "Append a numeric index to a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to make Java variables unique.
     The index is appended to the result of @(tsee atj-var-to-jvar),
     as explained there."))
  (b* ((index-chars (if (= index 0)
                        nil
                      (append (list #\$)
                              (str::natchars index))))
       (index-string (implode index-chars)))
    (add-suffix var index-string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-disallowed-jvar-names*
  :short "Disallowed Java variable names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee atj-var-to-jvar) turns an ACL2 symbol
     into one whose characters are all allowed in Java variables,
     but this is not sufficient:
     a Java variable name cannot be a keyword,
     a boolean literal, or the null literal.")
   (xdoc::p
    "This constant collects these disallowed sequences of characters,
     which otherwise consist of valid Java identifier characters.
     It also includes the empty sequence,
     because an ACL2 symbol may consist of no characters,
     but a Java identifier cannot be empty.
     It also includes the uppercase names of the @('t') and @('nil') symbols,
     because those are generated as static final fields,
     which would therefore conflict with homonymous variables."))
  (append *jkeywords*
          *boolean-literals*
          (list *null-literal*)
          (list "")
          (list "T" "NIL"))
  ///
  (assert-event (string-listp *atj-disallowed-jvar-names*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-jvar-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-disallowed-class-names*
  :short "Disallowed Java class names."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     a Java class is generated for each ACL2 package
     that includes ACL2 functions for which we generate Java code;
     each ACL2 function is turned into a Java method in that Java class.")
   (xdoc::p
    "The name of the Java class is obtained from the name of the ACL2 package
     via @(tsee atj-pkg-to-class),
     but since the generated Java code imports some classes
     from other Java packages,
     we need to make sure that the Java class name for an ACL2 package
     does not conflict with any of the imported classes.
     The generated Java code imports all the classes
     in the Java package of AIJ,
     as well as some Java library classes and interfaces,
     including all the ones in @('java.lang').
     This constant collects all of these.
     This constant must be kept in sync with @(tsee atj-gen-shallow-main-cunit),
     which generates the Java imports.")
   (xdoc::p
    "We also disallow Java keywords, boolean literals, and the null literal,
     which are not valid Java identiers.
     There is no need to exclude the empty string explicitly
     (unlike @(tsee *atj-disallowed-jvar-names*)),
     because ACL2 package names are never empty
     and the mapping in @(tsee atj-pkg-to-class)
     never produces empty strings."))
  (append *jkeywords*
          *boolean-literals*
          (list *null-literal*)
          *aij-class-names*
          ;; keep in sync with ATJ-GEN-SHALLOW-MAIN-CUNIT:
          (list "BigInteger"
                "ArrayList"
                "List"))
  ///
  (assert-event (string-listp *atj-disallowed-class-names*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-class-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-pkg-to-class ((pkg stringp) (java-class$ stringp))
  :returns (class stringp)
  :short "Turn an ACL2 package name into a Java class name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     a Java class is generated for each ACL2 package
     that includes ACL2 functions that we generate Java code for;
     each ACL2 function is turned into a Java method in that Java class.")
   (xdoc::p
    "The name of the Java class for the ACL2 package
     is obtained by turning the ACL2 package name
     into a valid Java identifier,
     using @(tsee atj-chars-to-jchars-id),
     but without flipping uppercase and lowercase.
     The resulting Java class name
     must not be in @(tsee *atj-disallowed-class-names*).
     Since the Java class is contained in the main class generated by ATJ,
     we also ensure that the name is distinct from the containing class,
     whose name is passed to this function.
     We also ensure that the Java class name is distinct from
     all the @(tsee mv) class names:
     we do so by checking that the class name does not start with @('MV_'),
     which is a little stronger than necessary
     but simpler and in practice should not be too restrictive."))
  (b* ((jchars (atj-chars-to-jchars-id (explode pkg) t :dash nil))
       (jstring (implode jchars))
       (jstring (if (or (member-equal jstring *atj-disallowed-class-names*)
                        (equal jstring java-class$)
                        (and (>= (length jstring) 3)
                             (eql (char jstring 0) #\M)
                             (eql (char jstring 1) #\V)
                             (eql (char jstring 2) #\_)))
                    (str::cat jstring "$")
                  jstring)))
    jstring))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-pkgs-to-classes ((pkgs string-listp) (java-class$ stringp))
  :guard (no-duplicatesp-equal pkgs)
  :returns (pkg-class-names string-string-alistp :hyp (string-listp pkgs))
  :short "Generate the mapping from ACL2 package names to Java class names."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call @(tsee atj-pkg-to-class) on all the argument package names,
     and generate an alist from those to the corresponding Java class names.
     This function is called on all the packages that include ACL2 functions
     that must be translated to Java.")
   (xdoc::p
    "For now each package name is translated independently from the others,
     but future versions of this function could generate mappings
     according to more ``global'' strategies.")
   (xdoc::p
    "The resulting alist is passed to the code generation functions,
     which use the alist to look up the Java class names
     corresponding to the ACL2 package names."))
  (b* (((when (endp pkgs)) nil)
       (pkg (car pkgs))
       (class (atj-pkg-to-class pkg java-class$))
       (rest-alist (atj-pkgs-to-classes (cdr pkgs) java-class$)))
    (acons pkg class rest-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-get-pkg-class-name ((pkg stringp)
                                (pkg-class-names string-string-alistp))
  :returns (class stringp :hyp (string-string-alistp pkg-class-names))
  :short "Retrieve the Java class name for an ACL2 package name
          from the mapping, ensuring that the name is present."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function causes an error if the package name is not in the alist,
     but it should always be called with arguments
     that do not result in the error.
     In other words, the error is never expected to actually happen."))
  (b* ((pair (assoc-equal pkg pkg-class-names))
       ((unless (consp pair))
        (raise "Internal error: no class name for package ~x0." pkg)
        ""))
    (cdr pair)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-disallowed-method-names*
  :short "Disallowed Java method names."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     ACL2 function names are turned into Java method names
     that must be valid identifiers.
     The mapping in @(tsee atj-fn-to-method) always produces
     characters that are valid for identifiers,
     but the sequence of such characters must not be
     a Java keyword, boolean or null literal, or empty.")
   (xdoc::p
    "This constant collects these disallowed names."))
  (append *jkeywords*
          *boolean-literals*
          (list *null-literal*)
          (list ""))
  ///
  (assert-event (string-listp *atj-disallowed-method-names*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-method-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-predefined-method-names*
  :short "Predefined Java method names for certain ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certain primitive ACL2 functions are generally used frequently,
     and thus we want to use more readable Java method names
     than would be produced by
     the default translation in @(tsee atj-fn-to-method).
     In particular,
     the default translation for @(tsee unary--) would be @('unary__'),
     even though the second dash is not really a separator
     but rather stands for the `minus' sign:
     for this function,
     we want to use the more readable @('unary_minus') method name.
     Other primitive functions like @(tsee binary-+)
     would include @('$') escapes according to their default translation;
     while not as bad as the default for @(tsee unary--),
     we want to use more readable method names like @('binary_plus').")
   (xdoc::p
    "We store these predefined method names as values of this alist,
     whose keys are the corresponding primitive functions.
     This alist is used in @(tsee atj-fn-to-method).")
   (xdoc::p
    "These predefined names currently use
     lowercase letters separated by underscores,
     consistently with the character translation
     in @(tsee atj-chars-to-jchars-id)."))
  '((bad-atom<= . "bad_atom_less_than_or_equal_to")
    (binary-* . "binary_star")
    (binary-+ . "binary_plus")
    (unary-- . "unary_minus")
    (unary-/ . "unary_slash")
    (< . "less_than"))
  ///
  (assert-event (symbol-string-alistp *atj-predefined-method-names*))
  (assert-event (no-duplicatesp-eq
                 (strip-cars *atj-predefined-method-names*)))
  (assert-event (no-duplicatesp-equal
                 (strip-cdrs *atj-predefined-method-names*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-fn-to-method ((fn symbolp))
  :returns (method stringp)
  :short "Turn an ACL2 function symbol into a Java method name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function is represented as a Java method.
     The Java methods for all the ACL2 functions that are translated to Java
     are partitioned by ACL2 packages:
     there is a Java class for each ACL2 package,
     and the Java method for each ACL2 function
     is in the Java class corresponding to the ACL2 package of the function.")
   (xdoc::p
    "The name of the Java method is obtained by turning the ACL2 function name
     into a valid Java identifier, via @(tsee atj-chars-to-jchars-id).
     The resulting name must not be in @(tsee *atj-disallowed-method-names*);
     if it is, we add a @('$') at the end, which makes the name allowed.
     However, if the function is a key in @(tsee *atj-predefined-method-names*),
     we directly use the associated name instead.
     To avoid conflicts with these predefined names,
     we add a @('$') at the end of every method name
     that happens to be one of the predefined ones
     (where the function is not the primitive one associated to that name.")
   (xdoc::p
    "The generation of the method name
     does not consider the package name of the function:
     the package name is used, instead, to generate the name of the Java class
     that contains the method;
     see @(tsee atj-pkg-to-class)."))
  (b* ((predef? (assoc-eq fn *atj-predefined-method-names*))
       ((when (consp predef?)) (cdr predef?))
       (jchars (atj-chars-to-jchars-id (explode (symbol-name fn)) t :dash t))
       (jstring (implode jchars))
       (jstring (if (or (member-equal jstring *atj-disallowed-method-names*)
                        (member-equal jstring (strip-cdrs
                                               *atj-predefined-method-names*)))
                    (str::cat jstring "$")
                  jstring)))
    jstring))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-fns-to-methods ((fns symbol-listp))
  :guard (no-duplicatesp-equal fns)
  :returns (fn-method-names symbol-string-alistp :hyp (symbol-listp fns))
  :short "Generate the mapping from ACL2 function symbols to Java method names."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call @(tsee atj-fn-to-method) on all the argument function symbols,
     and generate an alist from those to the corresponding Java method names.
     This function is called on all the functions
     that must be translated to Java.")
   (xdoc::p
    "For now each function symbol is translated independently from the others,
     but future versions of this function could generate mappings
     according to more ``global'' strategies.
     In this case, this function could be split into
     one that generates an alist
     for all the functions (to be translated) in a package
     (as the method names need to be unambiguous only within a class),
     and one that puts all the alist together.")
   (xdoc::p
    "The resulting alist is passed to the code generation functions,
     which use the alist to look up the Java method names
     corresponding to the ACL2 function symbols."))
  (b* (((when (endp fns)) nil)
       (fn (car fns))
       (method (atj-fn-to-method fn))
       (rest-alist (atj-fns-to-methods (cdr fns))))
    (acons fn method rest-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-get-fn-method-name ((fn symbolp)
                                (fn-method-names symbol-string-alistp))
  :returns (method stringp :hyp (symbol-string-alistp fn-method-names))
  :short "Retrieve the Java method name for an ACL2 function name
          from the mapping, ensuring that the name is present."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function causes an error if the function name is not in the alist,
     but it should always be called with arguments
     that do not result in the error.
     In other words, the error is never expected to actually happen."))
  (b* ((pair (assoc-equal fn fn-method-names))
       ((unless (consp pair))
        (raise "Internal error: no method name for function ~x0." fn)
        ""))
    (cdr pair)))
