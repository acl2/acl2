; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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
(include-book "kestrel/std/system/dumb-occur-var-open" :dir :system)
(include-book "kestrel/utilities/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/utilities/strings/char-kinds" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-library-extensions atj)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Std/system:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (indices nat-listp)
               (vars symbol-listp)
               (mv-term pseudo-termp)
               (body-term pseudo-termp))
  :short "Check if a term is a (translated) call of @(tsee mv-let)
          with some possibly missing @(tsee mv-nth) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee acl2::check-mv-let-call),
     except that it allows some of the @(tsee mv-nth) calls to be missing.
     Initially a translated @(tsee mv-let) has all those calls,
     but ATJ's pre-translation step that removes unused variables
     may remove some of them.
     Thus, we cannot use @(tsee acl2::check-mv-let-call) here,
     and instead create a custom version here
     (which may be moved to a more general library at some point,
     since it is not really ATJ-specific).
     This version also returns the indices of the @(tsee mv-nth) calls
     that are present, in increasing order
     (if they appear in a different order,
     this function returns @('nil') as first result)."))
  (b* ((term (if (mbt (pseudo-termp term)) term nil))
       ((when (variablep term)) (mv nil nil nil nil nil))
       ((when (fquotep term)) (mv nil nil nil nil nil))
       (lambda-mv (ffn-symb term))
       ((unless (flambdap lambda-mv)) (mv nil nil nil nil nil))
       (list-mv (lambda-formals lambda-mv))
       ((unless (equal list-mv (list 'mv))) (mv nil nil nil nil nil))
       (mv-term (fargn term 1))
       (lambda-vars-of-mv-nths (lambda-body lambda-mv))
       ((when (variablep lambda-vars-of-mv-nths)) (mv nil nil nil nil nil))
       ((when (fquotep lambda-vars-of-mv-nths)) (mv nil nil nil nil nil))
       (lambda-vars (ffn-symb lambda-vars-of-mv-nths))
       ((unless (flambdap lambda-vars)) (mv nil nil nil nil nil))
       (vars (lambda-formals lambda-vars))
       (body-term (lambda-body lambda-vars))
       ((when (dumb-occur-var-open 'mv body-term)) (mv nil nil nil nil nil))
       (mv-nths (fargs lambda-vars-of-mv-nths))
       ((mv mv-nths-okp indices) (atj-check-mv-let-call-aux mv-nths 0))
       ((unless mv-nths-okp) (mv nil nil nil nil nil)))
    (mv t indices vars mv-term body-term))

  :prepwork
  ((define atj-check-mv-let-call-aux ((terms pseudo-term-listp)
                                      (min-next-index natp))
     :returns (mv (yes/no booleanp)
                  (indices nat-listp))
     (b* (((when (endp terms)) (mv t nil))
          (term (car terms))
          ((unless (and (ffn-symb-p term 'mv-nth)
                        (= (len (fargs term)) 2))) (mv nil nil))
          ((unless (quotep (fargn term 1))) (mv nil nil))
          (index (cadr (fargn term 1)))
          ((unless (and (natp index)
                        (>= index min-next-index))) (mv nil nil))
          ((unless (eq (fargn term 2) 'mv)) (mv nil nil))
          ((mv rest-okp rest-indices)
           (atj-check-mv-let-call-aux (cdr terms) (1+ index)))
          ((unless rest-okp) (mv nil nil)))
       (mv t (cons index rest-indices)))
     ///
     (defret len-of-atj-check-mv-let-call-aux.indices
       (implies yes/no
                (equal (len indices)
                       (len terms))))))

  ///

  (defret len-of-atj-check-mv-let-call.indices/vars
    (implies yes/no
             (equal (len indices)
                    (len vars)))
    :hyp :guard)

  (defret atj-check-mv-let-call-mv-term-smaller
    (implies yes/no
             (< (acl2-count mv-term)
                (acl2-count term)))
    :rule-classes :linear)

  (defret atj-check-mv-let-call-body-term-smaller
    (implies yes/no
             (< (acl2-count body-term)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-make-mv-let-call ((indices nat-listp)
                              (vars symbol-listp)
                              (mv-term pseudo-termp)
                              (body-term pseudo-termp))
  :guard (= (len indices) (len vars))
  :returns (term pseudo-termp :hyp :guard)
  :short "Build a translated call of @(tsee mv-let)
          with some possibly missing @(tsee mv-nth) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is somewhat the opposite of @(tsee atj-check-mv-let-call).
     It is similar to @(tsee acl2::make-mv-let-call),
     which we cannot quite use here because in ATJ
     the unused variable removal pre-translation step
     may remove some @(tsee mv-nth) calls from a translated @(tsee mv-let).
     Thus, this function takes the list of indices present as argument."))
  `((lambda (mv)
      ((lambda ,vars ,body-term)
       ,@(atj-make-mv-let-call-aux indices)))
    ,mv-term)

  :prepwork
  ((define atj-make-mv-let-call-aux ((indices nat-listp))
     :returns (terms pseudo-term-listp)
     (cond ((endp indices) nil)
           (t (cons `(mv-nth ',(car indices) mv)
                    (atj-make-mv-let-call-aux (cdr indices)))))
     ///
     (defret len-of-atj-make-mv-let-call-aux
       (equal (len terms) (len indices))))))

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
