; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STD")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection tuple
  :parents (returns-specifiers)
  :short "A way to use @(tsee mv)-like return specifiers for tuples."
  :long
  (xdoc::topstring
   (xdoc::p
    (xdoc::seetopic "returns-specifiers" "Return specifiers")
    " support individual names and types (and hypothes, etc.)
     for components of @(tsee mv) results.
     However, when a function returns an "
    (xdoc::seetopic "acl2::error-triple" "error triple")
    " whose value (i.e. middle component) consists of multiple results,
     given that the error triple already consists of multiple results
     (three: the error, the value, and the state),
     it is not possible to use the @(tsee mv) return specifier notation
     for the value of the error triple.")
   (xdoc::p
    "So here we provide a macro, called @('tuple'),
     to mimic the @(tsee mv) return specifier notation
     for a single value, such as the middle component of an error triple.")
   (xdoc::p
    "The macro call")
   (xdoc::codeblock
    "(tuple (var1 type1)"
    "       ..."
    "       (varn typen)"
    "       x)")
   (xdoc::p
    "where each @('vari') is a variable symbol,
     each @('typei') is a predicate symbol or a term over @('vari'),
     and @('x') is a variable symbol,
     expands to")
   (xdoc::codeblock
    "(and (tuplep n x)"
    "     (b* (((list var1 ... varn) x))"
    "       (and (type1 var1)"
    "            ..."
    "            (typen varn))))")
   (xdoc::p
    "where each @('(typei vari)') is as shown if @('typei') is a symbol,
     otherwise we use the term @('typei') instead.")
   (xdoc::p
    "This lets us write return specifiers of the form")
   (xdoc::codeblock
    ":returns (mv erp"
    "             (val (tuple (var1 type1) ... (varn typen) val))"
    "             state)")
   (xdoc::p
    "where we can use the call @('(tuple ...)') as the type of @('val'),
     so that the expansion will express that @('val') is an @('n')-tuple
     whose components have the specified types.")
   (xdoc::p
    "We may extend this macro with support for
     @(':hyp') and other features of return specifiers.")
   (xdoc::p
    "The macro is in the @('STD') package,
     but we also add a synonym in the @('ACL2') package.")
   (xdoc::@def "tuple")
   (xdoc::@def "acl2::tuple"))

  (define tuple-fn ((args true-listp))
    :returns (mv vars conjuncts)
    (b* (((when (endp args)) (mv nil nil))
         (arg (car args))
         ((unless (tuplep 2 arg)) (mv nil nil))
         (var (first arg))
         (type (second arg))
         (conjunct (if (symbolp type)
                       (list type var)
                     type))
         ((mv vars conjuncts) (tuple-fn (cdr args))))
      (mv (cons var vars)
          (cons conjunct conjuncts))))

  (defmacro tuple (&rest args)
    (b* ((var (car (last args)))
         (comps (butlast args 1))
         ((mv vars conjuncts) (tuple-fn comps)))
      `(and (tuplep ,(len comps) ,var)
            (b* (((list ,@vars) ,var))
              (and ,@conjuncts)))))

  (defmacro acl2::tuple (&rest args)
    `(tuple ,@args)))
