; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../language/null-literal")
(include-book "../language/boolean-literals")
(include-book "../language/keywords")

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/strings/strtok-bang" :dir :system)
(include-book "kestrel/std/system/check-mv-let-call" :dir :system)
(include-book "kestrel/std/system/dumb-occur-var-open" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/ubody-plus" :dir :system)
(include-book "kestrel/utilities/strings/char-kinds" :dir :system)
(include-book "std/typed-lists/pseudo-term-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-library-extensions atj)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Std/system:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-fn-body ((fn symbolp) (wrld plist-worldp))
  :returns (body pseudo-termp)
  :short "Return the unnormalized body or attachment of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function extends @(tsee ubody+) as follows:
     if @('fn') has no unnormalized body,
     but it has an attachment @('fn2'),
     we consider @('(fn2 x1 ... xn)') to be the body of @('fn'),
     where @('x1'), ..., @('xn') are the formals of @('fn').
     For the purpose of ATJ's code generation,
     the attachment of @('fn2') to @('fn') is equivalent to
     @('fn2') being defined to call @('fn') with the same arguments.")
   (xdoc::p
    "The attachment is in the @('acl2::attachment') property of @('fn').
     The property has the form @('((fn . fn2))').
     If the property is absent or does not have this form,
     @('fn') is regarded as not being defined,
     and ATJ will stop because it cannot generate code for it."))
  (b* ((ubody (ubody+ fn wrld))
       ((when ubody) ubody)
       (attachment (getpropc fn 'acl2::attachment nil wrld))
       ((unless (tuplep 1 attachment)) nil)
       (element (car attachment)))
    (if (and (consp element)
             (eq (car element) fn)
             (symbolp (cdr element))
             (not (eq (cdr element) 'quote)))
        (fcons-term (cdr element) (formals+ fn wrld))
      nil))
  :prepwork
  ((defrulel returns-lemma
     (implies (symbol-listp x)
              (pseudo-term-listp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pseudo-term fixtype:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pseudo-term-count-lemma1
  (implies (not (member-eq (pseudo-term-kind term)
                           '(:null :var :quote)))
           (< (pseudo-term-list-count (pseudo-term-call->args term))
              (pseudo-term-count term)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pseudo-term-count-lemma2
  (implies (and (not (member-eq (pseudo-term-kind term)
                                '(:null :var :quote)))
                (pseudo-lambda-p (pseudo-term-call->fn term)))
           (< (pseudo-term-count
               (pseudo-lambda->body (pseudo-term-call->fn term)))
              (pseudo-term-count term)))
  :expand ((pseudo-term-count term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pseudo-term-count-lemma3
  (implies (pseudo-term-case term :lambda)
           (< (pseudo-term-count
               (pseudo-lambda->body (pseudo-term-call->fn term)))
              (pseudo-term-count term)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pseudo-term-count-lemma4
  (implies (< (nfix i) (len terms))
           (< (pseudo-term-count (nth i terms))
              (pseudo-term-list-count terms)))
  :rule-classes :linear
  :enable (pseudo-term-count pseudo-term-list-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (mv-var symbolp)
               (vars symbol-listp)
               (indices nat-listp)
               (hides boolean-listp)
               (mv-term pseudo-termp)
               (body-term pseudo-termp))
  :short "An FTY variant of @(tsee check-mv-let-call)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Like many other system utilities,
     @(tsee check-mv-let-call) is written to use the built-in ACL2 term API.
     When using this kind of system utilities
     in code that is written to use the "
    (xdoc::seetopic "acl2::pseudo-term-fty" "FTY term API")
    ", there may be a slight ``mismatch'',
     e.g. in the way the two APIs fix non-terms,
     or in the fact that, for termination,
     the ACL2 API is based on @(tsee acl2-count)
     while the FTY API is based on @(tsee pseudo-term-count).")
   (xdoc::p
    "The mismatch can be often bridged by introducing
     simple wrappers of those system utilities
     that fix the term (in the FTY way) and then call the wrapped utilities.
     This utility, @('fty-check-mv-let-call') demonstrates this,
     for the @(tsee check-mv-let-call) system utility.")
   (xdoc::p
    "Note that the retun type theorems readily become unconditional,
     as is common with fixtypes.
     In order to prove that the FTY term count decreases,
     we first prove lemmas saying that,
     under the assumption @(tsee pseudo-termp),
     the results of @(tsee check-mv-let-call) are smaller.
     Note that, under that assumption,
     the wrapper and the original utility return the same result
     (they only possibly differ on non-terms).
     In proving those lemmas, we need to break the FTY abstraction
     so that we can reduce the FTY term API operations
     to the ACL2 term API operations."))
  (check-mv-let-call (pseudo-term-fix term))
  ///

  (defret len-of-fty-check-mv-let-call.indices/vars
    (implies yes/no
             (equal (len indices)
                    (len vars)))
    :hyp :guard
    :hints (("Goal"
             :in-theory (enable acl2::len-of-check-mv-let-call.indices/vars))))

  (defret len-of-fty-check-mv-let-call.hides/vars
    (implies yes/no
             (equal (len hides)
                    (len vars)))
    :hyp :guard
    :hints (("Goal"
             :in-theory (enable acl2::len-of-check-mv-let-call.hides/vars))))

  (in-theory (disable len-of-fty-check-mv-let-call.indices/vars
                      len-of-fty-check-mv-let-call.indices/vars))

  (defrulel remove-equal-formals-actuals-lemma
    (<= (pseudo-term-list-count
         (mv-nth 1 (acl2::remove-equal-formals-actuals formals actuals)))
        (pseudo-term-list-count actuals))
    :rule-classes :linear
    :enable (acl2::remove-equal-formals-actuals pseudo-term-list-count))

  (defrulel pseudo-term-count-of-fty-check-mv-let-call.mv-term-lemma
    (implies (pseudo-termp term)
             (b* (((mv yes/no & & & & mv-term &) (check-mv-let-call term)))
               (implies yes/no
                        (< (pseudo-term-count mv-term)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-mv-let-call
             pseudo-term-kind)
    :prep-lemmas
    ((defrule lemma
       (implies (and (pseudo-termp term)
                     (not (pseudo-term-case term :quote)))
                (<= (pseudo-term-list-count (cdr term))
                    (pseudo-term-count term)))
       :rule-classes :linear
       :expand (pseudo-term-count term)
       :enable (pseudo-term-call->args
                pseudo-term-kind))))

  (defret pseudo-term-count-of-fty-check-mv-let-call.mv-term
    (implies yes/no
             (< (pseudo-term-count mv-term)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defrulel pseudo-term-count-of-fty-check-mv-let-call.body-term-lemma
    (implies (pseudo-termp term)
             (b* (((mv yes/no & & & & & body-term) (check-mv-let-call term)))
               (implies yes/no
                        (< (pseudo-term-count body-term)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable check-mv-let-call
    :prep-lemmas
    ((defrule lemma
       (implies (and (pseudo-termp term)
                     (consp (car term)))
                (< (pseudo-term-count (caddr (car term)))
                   (pseudo-term-count term)))
       :rule-classes :linear
       :expand (pseudo-term-count term)
       :enable (pseudo-term-lambda->body
                pseudo-term-kind))))

  (defret pseudo-term-count-of-fty-check-mv-let-call.body-term
    (implies yes/no
             (< (pseudo-term-count body-term)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Java:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-string-ascii-java-identifier-p ((string stringp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 string is a valid ASCII Java identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string must be non-empty,
     start with a letter or underscore or dollar sign,
     and continue with zero or more
     letters, digits, underscores, and dollar signs.
     It must also be different
     from Java keywords and from the boolean and null literals.")
   (xdoc::p
    "Here for simplicity we disallow ignorable characters.
     See "
    (xdoc::seetopic "identifiers" "the formalization of identifiers")
    " for more details.
     It is expected that (perhaps an extension of) that formalization
     will replace this function here,
     but for now this function is adequate to ATJ's needs."))
  (and (not (member-equal string *jkeywords*))
       (not (member-equal string *boolean-literals*))
       (not (equal string *null-literal*))
       (b* ((chars (explode string)))
         (and (consp chars)
              (alpha/uscore/dollar-char-p (car chars))
              (alpha/digit/uscore/dollar-charlist-p (cdr chars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atj-string-ascii-java-identifier-listp (x)
  (atj-string-ascii-java-identifier-p x)
  :guard (string-listp x)
  :short "Check if a list of ACL2 strings includes only ASCII Java identifiers."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-string-ascii-java-package-name-p ((string stringp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 string is a valid ASCII Java package name."
  :long
  (xdoc::topstring-p
   "The string must consist of one or more ASCII Java identifiers
    separated by dots.")
  (b* ((identifiers (str::strtok! string (list #\.))))
    (and (consp identifiers)
         (atj-string-ascii-java-identifier-listp identifiers))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-lang-class-names*
  :short "Class names in the Java @('java.lang') package."
  (list
   ;; interfaces:
   "Appendable"
   "AutoCloseable"
   "CharSequence"
   "Cloneable"
   "Comparable"
   "Iterable"
   "ProcessHandle"
   "Readable"
   "Runnable"
   ;; classes:
   "Boolean"
   "Byte"
   "Character"
   "Class"
   "ClassLoader"
   "ClassValue"
   "Compiler"
   "Double"
   "Enum"
   "Float"
   "InheritableThreadLocal"
   "Integer"
   "Long"
   "Math"
   "Module"
   "ModuleLayer"
   "Number"
   "Object"
   "Package"
   "Process"
   "ProcessBuilder"
   "Runtime"
   "RuntimePermission"
   "SecurityManager"
   "Short"
   "StackTraceElement"
   "StackWalker"
   "StrictMath"
   "String"
   "StringBuffer"
   "StringBuilder"
   "System"
   "Thread"
   "ThreadGroup"
   "ThreadLocal"
   "Throwable"
   "Void"
   ;; exceptions:
   "ArithmeticException"
   "ArrayIndexOutOfBoundsException"
   "ArrayStoreException"
   "ClassCastException"
   "ClassNotFoundException"
   "CloneNotSupportedException"
   "EnumConstantNotPresentException"
   "Exception"
   "IllegalAccessException"
   "IllegalArgumentException"
   "IllegalCallerException"
   "IllegalMonitorStateException"
   "IllegalStateException"
   "IllegalThreadStateException"
   "IndexOutOfBoundsException"
   "InstantiationException"
   "InterruptedException"
   "LayerInstantiationException"
   "NegativeArraySizeException"
   "NoSuchFieldException"
   "NoSuchMethodException"
   "NullPointerException"
   "NumberFormatException"
   "ReflectiveOperationException"
   "RuntimeException"
   "SecurityException"
   "StringIndexOutOfBoundsException"
   "TypeNotPresentException"
   "UnsupportedOperationException"
   ;; errors:
   "AbstractMethodError"
   "AssertionError"
   "BootstrapMethodError"
   "ClassCircularityError"
   "ClassFormatError"
   "Error"
   "ExceptionInInitializerError"
   "IllegalAccessError"
   "IncompatibleClassChangeError"
   "InstantiationError"
   "InternalError"
   "LinkageError"
   "NoClassDefFoundError"
   "NoSuchFieldError"
   "NoSuchMethodError"
   "OutOfMemoryError"
   "StackOverflowError"
   "ThreadDeath"
   "UnknownError"
   "UnsatisfiedLinkError"
   "UnsupportedClassVersionError"
   "VerifyError"
   "VirtualMachineError"
   ;; annotations:
   "Deprecated"
   "FunctionalInterface"
   "Override"
   "SafeVarargs"
   "SuppressWarnings"))
