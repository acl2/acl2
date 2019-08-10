; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/utilities/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/utilities/strings/char-kinds" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/strings/coerce" :dir :system)
(include-book "std/util/defalist" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defval" :dir :system)

(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-library-extensions atj)

(defines remove-mbe-logic/exec-from-term
  :short "Turn every call @('(mbe :logic a :exec b)') in a term
          into just its @(':logic') part @('a') or @(':exec') part @('b')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The choice is determinated by the boolean flag,
     which is @('t') when the @(':logic') part is to be removed.")
   (xdoc::p
    "In translated terms,
     @(tsee mbe)s have the form @('(return-last 'acl2::mbe1-raw b a)')."))

  (define remove-mbe-logic/exec-from-term ((term pseudo-termp)
                                           (logic? booleanp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         (args (fargs term))
         ((when (and (eq fn 'return-last)
                     (equal (first args) '(quote acl2::mbe1-raw))))
          (remove-mbe-logic/exec-from-term (if logic?
                                               (second args)
                                             (third args))
                                           logic?))
         (new-fn (if (symbolp fn)
                     fn
                   (make-lambda (lambda-formals fn)
                                (remove-mbe-logic/exec-from-term
                                 (lambda-body fn)
                                 logic?))))
         (new-args (remove-mbe-logic/exec-from-terms args logic?)))
      (fcons-term new-fn new-args)))

  (define remove-mbe-logic/exec-from-terms ((terms pseudo-term-listp)
                                            (logic? booleanp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (b* (((when (endp terms)) nil)
         ((cons term terms) terms)
         (new-term (remove-mbe-logic/exec-from-term term logic?))
         (new-terms (remove-mbe-logic/exec-from-terms terms logic?)))
      (cons new-term new-terms))))

(define remove-mbe-logic-from-term ((term pseudo-termp))
  :returns (new-term "A @(tsee pseudo-termp).")
  :short "Turn every call @('(mbe :logic a :exec b)') in a term
          into just its @(':exec') part @('b')."
  (remove-mbe-logic/exec-from-term term t))

(define remove-mbe-exec-from-term ((term pseudo-termp))
  :returns (new-term "A @(tsee pseudo-termp).")
  :short "Turn every call @('(mbe :logic a :exec b)') in a term
          into just its @(':logic') part @('a')."
  (remove-mbe-logic/exec-from-term term nil))

(define unquote-list ((list quote-listp))
  :returns (new-list true-listp)
  :verify-guards nil
  :short "Unquote all the elements of a list."
  (cond ((endp list) nil)
        (t (cons (unquote (car list))
                 (unquote-list (cdr list))))))

(define decompose-at-dots ((string stringp))
  :returns (substrings string-listp)
  :verify-guards nil
  :short "Decompose an ACL2 string
          into its substrings delimited by dot characters,
          including empty substrings."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the string has no dots, a singleton list with the string is returned.
     Otherwise, we return a list consisting of
     the substring from the start of the string to the first dot,
     the substrings between two consecutive dots (in order),
     and the substring from the last dot to the end of the string.
     The substrings include no dots, and may be empty.")
   (xdoc::p
    "For example:")
   (xdoc::ul
    (xdoc::li
     "@('\"ab.c.def\"') is decomposed into @('(\"ab\" \"c\" \"def\")').")
    (xdoc::li
     "@('\"xyz\"') is decomposed into @('(\"xyz\")').")
    (xdoc::li
     "@('\".abc..de.\"') is decomposed into
      @('(\"\" \"abc\" \"\" \"de\" \"\")').")))
  (decompose-at-dots-aux (explode string) nil)

  :prepwork
  ((define decompose-at-dots-aux ((chars character-listp)
                                  (rev-current-substrings string-listp))
     :returns (final-substrings string-listp
                                :hyp (string-listp rev-current-substrings))
     :verify-guards nil
     :parents nil
     (if (endp chars)
         (rev rev-current-substrings)
       (b* ((pos (position #\. chars)))
         (if pos
             (b* ((substring (implode (take pos chars)))
                  (chars (nthcdr (1+ pos) chars))
                  (rev-current-substrings (cons substring
                                                rev-current-substrings)))
               (decompose-at-dots-aux chars rev-current-substrings))
           (b* ((substring (implode chars))
                (rev-final-substrings (cons substring rev-current-substrings)))
             (rev rev-final-substrings)))))
     :measure (len chars))))

(std::defalist symbol-nat-alistp (x)
  :short "Recognize alists from symbols to natural numbers."
  :key (symbolp x)
  :val (natp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defrule natp-of-cdr-of-assoc-equal-when-symbol-nat-alistp
    (implies (and (symbol-nat-alistp alist)
                  (assoc-equal key alist))
             (natp (cdr (assoc-equal key alist))))))

(std::defalist symbol-string-alistp (x)
  :short "Recognize alists from symbols to strings."
  :key (symbolp  x)
  :val (stringp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil)

(std::defalist string-symbols-alistp (x)
  :short "Recognize alists from strings to true lists of symbols."
  :key (stringp x)
  :val (symbol-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t)

(define organize-fns-by-pkg ((fns symbol-listp))
  :returns (fns-by-pkg "A @(tsee string-symbols-alistp).")
  :verify-guards nil
  :short "Organize a list of function names by their packages."
  :long
  (xdoc::topstring-p
   "The result is an alist from package names (strings)
    to the non-empty lists of the function symbols
    that are in the respective packages.")
  (organize-fns-by-pkg-aux fns nil)

  :prepwork
  ((define organize-fns-by-pkg-aux ((fns symbol-listp)
                                    (acc string-symbols-alistp))
     :returns fns-by-pkg ; STRING-SYMBOLS-ALISTP
     :verify-guards nil
     :parents nil
     (b* (((when (endp fns)) acc)
          (fn (car fns))
          (pkg (symbol-package-name fn))
          (prev-fns-for-pkg (cdr (assoc-equal pkg acc))))
       (organize-fns-by-pkg-aux (cdr fns)
                                (acons pkg (cons fn prev-fns-for-pkg) acc))))))

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
        "while")
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
  (b* ((identifiers (decompose-at-dots string)))
    (and (consp identifiers)
         (atj-string-ascii-java-identifier-listp identifiers))))

(defval *atj-aij-jpackage*
  :short "Name of the Java package of AIJ."
  "edu.kestrel.acl2.aij"
  ///
  (assert-event (atj-string-ascii-java-package-name-p *atj-aij-jpackage*)))
