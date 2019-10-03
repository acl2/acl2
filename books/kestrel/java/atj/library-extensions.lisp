; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../language/null-literal")
(include-book "../language/boolean-literals")
(include-book "../language/keywords")

(include-book "kestrel/std/strings/strtok-bang" :dir :system)
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
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-library-extensions atj)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; basic:

(define organize-symbols-by-pkg ((syms symbol-listp))
  :returns (syms-by-pkg string-symbollist-alistp :hyp :guard)
  :short "Organize a list of symbols by their packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is an alist from package names (strings)
     to the non-empty lists of the symbols
     that are in the respective packages.")
   (xdoc::p
    "The alist has unique keys,
     and each of its values has no duplicates."))
  (organize-symbols-by-pkg-aux syms nil)

  :prepwork
  ((define organize-symbols-by-pkg-aux ((syms symbol-listp)
                                        (acc string-symbollist-alistp))
     :returns (syms-by-pkg string-symbollist-alistp :hyp :guard)
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
  :returns (syms-by-name string-symbollist-alistp :hyp :guard)
  :short "Organize a list of symbols by their names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is an alist from symbol names (strings)
     to the non-empty lists of the symbols
     that have the respective names.")
   (xdoc::p
    "The alist has unique keys,
     and each of its values has no duplicates."))
  (organize-symbols-by-name-aux syms nil)

  :prepwork
  ((define organize-symbols-by-name-aux ((syms symbol-listp)
                                         (acc string-symbollist-alistp))
     :returns (syms-by-name string-symbollist-alistp :hyp :guard)
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

; Java:

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
  (and (not (member-equal string *keywords*))
       (not (member-equal string *boolean-literals*))
       (not (equal string *null-literal*))
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
  (b* ((identifiers (str::strtok! string (list #\.))))
    (and (consp identifiers)
         (atj-string-ascii-java-identifier-listp identifiers))))
