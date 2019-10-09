; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../language/keywords")
(include-book "../language/boolean-literals")
(include-book "../language/null-literal")

(include-book "kestrel/std/basic/organize-symbols-by-name" :dir :system)
(include-book "kestrel/utilities/strings/hexchars" :dir :system)
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
     necessitating a non-identity translation mapping."))
  :order-subtopics t
  :default-parent t)

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
    "This is used to translate ACL2 variable, function, and package names
     into Java identifiers.")
   (xdoc::p
    "ACL2 symbols may consist of arbitrary sequences of 8-bit characters,
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
     @('$') followed by a short unambiguous description of the character
     (with one exception, described below).")
   (xdoc::p
    "For the printable ASCII characters that are not letters,
     we use the descriptions in the @('*atj-char-to-jchars-id*') alist.
     These include digits, used when @('startp') is @('t').
     The exception is dash,
     which is very common in ACL2 symbols and package names as ``separator'':
     we map that to an underscore in Java,
     which fulfills a similar separator role.
     Note that @('$') itself, which is valid in Java identifiers,
     is escaped.")
   (xdoc::p
    "For each of the other ISO 8859-1 characters,
     we use a description that consists of @('x') (for `hexadecimal')
     followed by the two hex digits that form the ASCII code of the character.
     The hexadecimal digits greater than 9 are uppercase.")
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
       (#\- . "_")
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
                         (append (atj-chars-to-jchars-id (explode pname) t t)
                                 (list #\$ #\$))))
       (name-jchars (atj-chars-to-jchars-id (explode name)
                                            (endp pname$$-jchars)
                                            t))
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
     but a Java identifier cannot be empty."))
  (append *keywords*
          *boolean-literals*
          (list *null-literal*)
          (list ""))
  ///
  (assert-event (string-listp *atj-disallowed-jvar-names*))
  (assert-event (no-duplicatesp-equal *atj-disallowed-jvar-names*)))
