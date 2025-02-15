; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../representation/integer-operations")

(include-book "std/system/check-and-call" :dir :system)
(include-book "std/system/check-or-call" :dir :system)
(include-book "std/system/check-list-call" :dir :system)
(include-book "std/system/check-mv-let-call" :dir :system)
(include-book "std/system/irecursivep-plus" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-term-recognizers
  :parents (atc-implementation)
  :short "Recognizers of ACL2 terms for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "The user documentation of ATC
     defines various kinds of ACL2 terms
     that represent various C constructs.
     ATC checks these various kinds of terms
     as part of translating them to C.")
   (xdoc::p
    "Here we provide utilities to recognize these terms.
     While these utilities are not needed, and are not part of,
     ATC's C code generation code,
     they may be useful for external tools,
     such as APT transformations that work in synergy with ATC.")
   (xdoc::p
    "For now we provide shallow recognizers,
     which do not thoroughly check the terms and their subterms,
     but that suffice to distinguish the various kinds of terms.
     We only provide these recognizers for some kinds of terms for now."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-boolean-from-type-fns*
  :short "List of the @('boolean-from-<type>') functions
          described in the user documentation."
  (atc-boolean-from-type-fns-gen *nonchar-integer-types*)

  :prepwork
  ((defun atc-boolean-from-type-fns-gen (types)
     (cond ((endp types) nil)
           (t (cons (pack 'boolean-from- (type-kind (car types)))
                    (atc-boolean-from-type-fns-gen (cdr types))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-type-base-const-fns*
  :short "List of the @('<type>-<base>-const') functions
          described in the user documentation."
  (atc-type-base-const-fns-gen *nonchar-integer-types*)

  :prepwork

  ((defun atc-type-base-const-fns-gen-aux (type bases)
     (cond ((endp bases) nil)
           (t (cons (pack (type-kind type) '- (car bases) '-const)
                    (atc-type-base-const-fns-gen-aux type (cdr bases))))))

   (defun atc-type-base-const-fns-gen (types)
     (cond ((endp types) nil)
           (t (append (atc-type-base-const-fns-gen-aux (car types)
                                                       '(dec
                                                         oct
                                                         hex))
                      (atc-type-base-const-fns-gen (cdr types))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-op-type-fns*
  :short "List of the @('<op>-<type>') functions
          described in the user documentation."
  (atc-op-type-fns-gen *nonchar-integer-types*)

  :prepwork

  ((defun atc-op-type-fns-gen-aux (type ops)
     (cond ((endp ops) nil)
           (t (cons (pack (car ops) '- (type-kind type))
                    (atc-op-type-fns-gen-aux type (cdr ops))))))

   (defun atc-op-type-fns-gen (types)
     (cond ((endp types) nil)
           (t (append (atc-op-type-fns-gen-aux (car types)
                                               '(plus
                                                 minus
                                                 bitnot
                                                 lognot))
                      (atc-op-type-fns-gen (cdr types))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-op-type1-type2-fns*
  :short "List of the @('<op>-<type1>-<type2>') functions
          described in the user documentation."
  (atc-op-type1-type2-fns-gen *nonchar-integer-types*)

  :prepwork

  ((defun atc-op-type1-type2-fns-gen-aux-aux (type1 type2 ops)
     (cond ((endp ops) nil)
           (t (cons (pack (car ops) '- (type-kind type1) '- (type-kind type2))
                    (atc-op-type1-type2-fns-gen-aux-aux type1
                                                        type2
                                                        (cdr ops))))))

   (defun atc-op-type1-type2-fns-gen-aux (type1 type2s)
     (cond ((endp type2s) nil)
           (t (append (atc-op-type1-type2-fns-gen-aux-aux type1
                                                          (car type2s)
                                                          '(add
                                                            sub
                                                            mul
                                                            div
                                                            rem
                                                            shl
                                                            shr
                                                            lt
                                                            gt
                                                            le
                                                            ge
                                                            eq
                                                            ne
                                                            bitand
                                                            bitxor
                                                            bitior))
                      (atc-op-type1-type2-fns-gen-aux type1
                                                      (cdr type2s))))))

   (defun atc-op-type1-type2-fns-gen (type1s)
     (cond ((endp type1s) nil)
           (t (append (atc-op-type1-type2-fns-gen-aux
                       (car type1s)
                       *nonchar-integer-types*)
                      (atc-op-type1-type2-fns-gen (cdr type1s))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-type1-from-type2-fns*
  :short "List of the @('<type1>-from-<type2>') functions
          described in the user documentation."
  (atc-type1-from-type2-fns-gen *nonchar-integer-types*)

  :prepwork

  ((defun atc-type1-from-type2-fns-gen-aux (type1 type2s)
     (cond ((endp type2s) nil)
           (t (append (and (not (equal type1 (car type2s)))
                           (list (pack (type-kind type1)
                                       '-from-
                                       (type-kind (car type2s)))))
                      (atc-type1-from-type2-fns-gen-aux type1 (cdr type2s))))))

   (defun atc-type1-from-type2-fns-gen (type1s)
     (cond ((endp type1s) nil)
           (t (append (atc-type1-from-type2-fns-gen-aux
                       (car type1s)
                       *nonchar-integer-types*)
                      (atc-type1-from-type2-fns-gen (cdr type1s))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-boolean-termp ((term pseudo-termp))
  :returns (yes/no booleanp)
  :short "Recognize expression terms returning booleans."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just check whether the term is
     a call of a @('boolean-from-<type>') function
     or a call of @(tsee and) or @(tsee or)."))
  (b* (((mv andp & &) (check-and-call term))
       ((when andp) t)
       ((mv orp & &) (check-or-call term))
       ((when orp) t))
    (case-match term
      ((fn . &) (if (member-eq fn *atc-boolean-from-type-fns*)
                    t
                  nil))
      (& nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-pure-c-valued-termp ((term pseudo-termp))
  :returns (yes/no booleanp)
  :short "Recognize pure expression terms returning C values terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just check that the term is either a variable
     or a call of one of the functions
     listed in the user documentation for
     pure expression terms returning C values."))
  (b* (((when (variablep term)) t))
    (case-match term
      ((fn . &)
       (if (or (member-eq fn *atc-type-base-const-fns*)
               (member-eq fn *atc-op-type-fns*)
               (member-eq fn *atc-op-type1-type2-fns*)
               (member-eq fn *atc-type1-from-type2-fns*)
               (eq fn 'uchar-array-read-sint)
               (eq fn 'sint-from-boolean)
               (eq fn 'condexpr))
           t
         nil))
      (& nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-c-valued-termp ((term pseudo-termp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "Recognize expression terms returning C values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just check whether the term is
     either a pure expression term returning a C value
     or is a call of a non-recursive function,
     which we therefore assume to be a target function."))
  (b* (((when (atc-pure-c-valued-termp term)) t))
    (case-match term
      ((fn . &) (and (symbolp fn)
                     (not (irecursivep+ fn wrld))))
      (& nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-stmt-noncval-termp ((term pseudo-termp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "Recognize statement terms that are not
          expression terms returning C values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just check if the term is
     an @(tsee if), an @(tsee mv), a @(tsee let), an @(tsee mv-let),
     or a call of a recursive function,
     which we therefore assume to be a target function."))
  (b* (((mv ifp & & &) (check-if-call term))
       ((when ifp) t)
       ((mv mvp &) (check-list-call term))
       ((when mvp) t)
       ((mv mv-letp & & & & & &) (check-mv-let-call term))
       ((when mv-letp) t))
    (case-match term
      ((fn . &) (or (consp fn) ; lambda
                    (consp (irecursivep+ fn wrld))))
      (& nil)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))
