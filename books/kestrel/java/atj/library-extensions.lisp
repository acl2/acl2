; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/std/typed-alists/string-symbollist-alistp" :dir :system)
(include-book "kestrel/std/typed-alists/symbol-nat-alistp" :dir :system)
(include-book "kestrel/std/typed-alists/symbol-string-alistp" :dir :system)
(include-book "kestrel/utilities/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/utilities/strings/char-kinds" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/strings/coerce" :dir :system)
(include-book "std/util/defalist" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)

(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-library-extensions atj)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; basic:

(define organize-symbols-by-pkg ((syms symbol-listp))
  :returns (syms-by-pkg "A @(tsee string-symbollist-alistp).")
  :verify-guards nil
  :short "Organize a list of symbols by their packages."
  :long
  (xdoc::topstring-p
   "The result is an alist from package names (strings)
    to the non-empty lists of the symbols
    that are in the respective packages.")
  (organize-symbols-by-pkg-aux syms nil)

  :prepwork
  ((define organize-symbols-by-pkg-aux ((syms symbol-listp)
                                        (acc string-symbollist-alistp))
     :returns syms-by-pkg ; STRING-SYMBOLLIST-ALISTP
     :verify-guards nil
     :parents nil
     (b* (((when (endp syms)) acc)
          (sym (car syms))
          (pkg (symbol-package-name sym))
          (prev-syms-for-pkg (cdr (assoc-equal pkg acc))))
       (organize-symbols-by-pkg-aux (cdr syms)
                                    (put-assoc-equal
                                     pkg
                                     (add-to-set-eq sym prev-syms-for-pkg)
                                     acc))))))

(define organize-symbols-by-name ((syms symbol-listp))
  :returns (syms-by-name "A @(tsee string-symbollist-alistp).")
  :verify-guards nil
  :short "Organize a list of symbols by their names."
  :long
  (xdoc::topstring-p
   "The result is an alist from symbol names (strings)
    to the non-empty lists of the symbols
    that have the respective names.")
  (organize-symbols-by-name-aux syms nil)

  :prepwork
  ((define organize-symbols-by-name-aux ((syms symbol-listp)
                                         (acc string-symbollist-alistp))
     :returns syms-by-name ; STRING-SYMBOLLIST-ALISTP
     :verify-guards nil
     :parents nil
     (b* (((when (endp syms)) acc)
          (sym (car syms))
          (name (symbol-name sym))
          (prev-syms-for-name (cdr (assoc-equal name acc))))
       (organize-symbols-by-name-aux (cdr syms)
                                     (put-assoc-equal
                                      name
                                      (add-to-set-eq sym prev-syms-for-name)
                                      acc))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; strings:

(define strtok! ((string stringp) (delimiters character-listp))
  :returns (strings string-listp)
  :short "Variant of @(tsee str::strtok)
          that does not treat contiguous delimiters as one."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee str::strtok) treats contiguous delimiters as one,
     and thus it never returns empty strings, e.g.:")
   (xdoc::codeblock
    "(strtok \"abc.de..f\" (list #\\.)) --> (\"abc\" \"de\" \"f\")")
   (xdoc::p
    "In contrast, @('strtok!') considers each delimiter separately,
     possibly returning empty string between contiguous delimiters:")
   (xdoc::codeblock
    "(strtok! \"abc.de..f\" (list #\\.)) --> (\"abc\" \"de\" \"\" \"f\")")
   (xdoc::p
    "The implementation of @('strtok!') is very similar to @(tsee str::strtok),
     aside from some parameter name changes.
     The main difference is that @('strtok!') omits some tests
     about the (reversed) current token being non-empty:
     in this way, empty tokens are considered and returned.")
   (xdoc::p
    "Note that @('strtok!') returns the singleton list @('(\"\")')
     when given the empty string @('\"\"') as argument.
     This seems to make sense because the beginning and end of the string
     are considered like delimiters,
     and @('strtok!') considers and returns empty strings between delimiters.
     However, it would be easy to change @('strtok!') to return @('nil')
     when given the empty string as argument, if so desired and agreed upon."))
  (b* ((rev-tokens (strtok!-aux string
                                0
                                (mbe :logic (len (explode string))
                                     :exec (length string))
                                delimiters
                                nil
                                nil)))
    (mbe :logic (rev rev-tokens)
         :exec (reverse rev-tokens)))

  :prepwork
  ((define strtok!-aux ((string stringp :type string)
                        (pos natp :type (integer 0 *))
                        (len natp :type (integer 0 *))
                        (delimiters character-listp)
                        (rev-curr-tok character-listp)
                        (acc string-listp))
     :guard (and (<= pos len) (<= len (length string)))
     :returns (result string-listp :hyp (string-listp acc))
     (if (mbe :logic (zp (- (nfix len) (nfix pos)))
              :exec (int= pos len))
         (cons (str::rchars-to-string rev-curr-tok) acc)
       (b* ((char (char string pos))
            (matchp (member char delimiters)))
         (strtok!-aux (the string string)
                      (the (integer 0 *) (1+ (mbe :logic (nfix pos) :exec pos)))
                      (the (integer 0 *) len)
                      delimiters
                      (if matchp nil (cons char rev-curr-tok))
                      (if matchp
                          (cons (str::rchars-to-string rev-curr-tok) acc)
                        acc))))
     :measure (nfix (- (nfix len) (nfix pos)))
     ///
     (defcong str::streqv equal
       (strtok!-aux string pos len delimiters rev-curr-tok acc) 1)))

  ///

  (defcong str::streqv equal (strtok! string delimiters) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; system:

(define remove-unneeded-lambda-formals ((formals symbol-listp)
                                        (actuals pseudo-term-listp))
  :guard (= (len formals) (len actuals))
  :returns (new-formals symbol-listp :hyp (symbol-listp formals))
  :short "Remove ``unneeded'' formal parameters of a lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 lambda expressions are always closed,
     which means that often they include formal parameters
     that are replaced by themselves (i.e. by the same symbols)
     when the lambda expression is applied.
     For instance, the untranslated term @('(let ((x 0)) (+ x y))')
     is @('((lambda (x y) (binary-+ x y)) '3 y)') in translated form:
     the lambda expression includes the extra formal parameter @('y')
     which is not bound by the @(tsee let),
     applied to @('y') itself,
     making the lambda expression closed.")
   (xdoc::p
    "For certain purposes,
     these additional formal parameters are ``unneeded'',
     in the sense that they are not bound in the @(tsee let) expression
     that the applied lambda expression represents.
     This function removes such unneeded formal parameters:
     it goes through the formal parameters of a lambda expression
     and through the corresponding actual arguments,
     and drops the formal parameters
     that are equal to the corresponding actual arguments,
     keeping the rest.")
   (xdoc::p
    "This function can be turned into a more general list utility,
     which goes through two lists of equal length
     and drops from the first list all the elements
     that are equal to the corresponding ones in the second list."))
  (cond ((endp formals) nil)
        (t (if (eq (car formals) (car actuals))
               (remove-unneeded-lambda-formals (cdr formals)
                                               (cdr actuals))
             (cons (car formals)
                   (remove-unneeded-lambda-formals (cdr formals)
                                                   (cdr actuals)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Java:

(defval *atj-java-keywords*
  :short "The keywords of the Java language, as ACL2 strings."
  (list "abstract"
        "assert"
        "boolean"
        "break"
        "byte"
        "case"
        "catch"
        "char"
        "class"
        "const"
        "continue"
        "default"
        "do"
        "double"
        "else"
        "enum"
        "extends"
        "final"
        "finally"
        "float"
        "for"
        "if"
        "goto"
        "implements"
        "import"
        "instanceof"
        "int"
        "interface"
        "long"
        "native"
        "new"
        "package"
        "private"
        "protected"
        "public"
        "return"
        "short"
        "static"
        "strictfp"
        "super"
        "switch"
        "synchronized"
        "this"
        "throw"
        "throws"
        "transient"
        "try"
        "void"
        "volatile"
        "while"
        "_")
  ///
  (assert-event (string-listp *atj-java-keywords*))
  (assert-event (no-duplicatesp-equal *atj-java-keywords*)))

(defval *atj-java-boolean-literals*
  :short "The boolean literals of the Java language, as ACL2 strings."
  (list "true" "false"))

(defval *atj-java-null-literal*
  :short "The null literal of the Java language, as an ACL2 string."
  "null")

(define atj-string-ascii-java-identifier-p ((string stringp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 string is a valid ASCII Java identifier."
  :long
  (xdoc::topstring-p
   "The string must be non-empty,
    start with a letter or underscore or dollar sign,
    and continue with zero or more
    letters, digits, underscores, and dollar signs.
    It must also be different
    from Java keywords and from the boolean and null literals.")
  (and (not (member-equal string *atj-java-keywords*))
       (not (member-equal string *atj-java-boolean-literals*))
       (not (equal string *atj-java-null-literal*))
       (b* ((chars (explode string)))
         (and (consp chars)
              (alpha/uscore/dollar-char-p (car chars))
              (alpha/digit/uscore/dollar-charlist-p (cdr chars))))))

(std::deflist atj-string-ascii-java-identifier-listp (x)
  (atj-string-ascii-java-identifier-p x)
  :guard (string-listp x)
  :short "Check if a list of ACL2 strings includes only ASCII Java identifiers."
  :true-listp t
  :elementp-of-nil nil)

(define atj-string-ascii-java-package-name-p ((string stringp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Check if an ACL2 string is a valid ASCII Java package name."
  :long
  (xdoc::topstring-p
   "The string must consist of one or more ASCII Java identifiers
    separated by dots.")
  (b* ((identifiers (strtok! string (list #\.))))
    (and (consp identifiers)
         (atj-string-ascii-java-identifier-listp identifiers))))
