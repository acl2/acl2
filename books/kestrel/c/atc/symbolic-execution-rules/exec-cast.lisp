; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../execution")
(include-book "../types")

(include-book "syntaxp")
(include-book "integers")
(include-book "value-integer-get")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-cast-rules-generation
  :short "Code to generate the rules for executing cast operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The hints expand
     @(tsee exec-cast),
     @(tsee convert-integer-value),
     @(tsee value-integer), and
     @(tsee value-integer->get),
     which produces something like @('(value-<dst> (value-<src>->get ...))'),
     where @('<src>') is the source type and @('<dst>') is the destination type,
     with an intervening @(tsee mod) when the destination type is unsigned.
     We use the bridge rules to turn those constructor and destructors
     into the shallowly embedded ones (i.e. @('(<dst> (<src>->get ...))'),
     which are the ones used in the definitions of
     the shallowly embedded conversion functions,
     which we also open (unless source and destination types are equal),
     along with the @('okp') predicates if applicable.
     We also need open @('u...-mod') to expose the @(tsee mod)
     in the shallowly embedded conversions to unsigned type,
     thus matching the @(tsee mod) in @(tsee convert-integer-value).
     We open the @('<dst>-integerp') functions
     to show that the ACL2 integer is in range,
     i.e. that @(tsee convert-integer-value) does not return an error;
     for this, we also need (locally included) rules about @(tsee mod),
     to show that it is never negative as required for an unsigned range."))

  (define atc-exec-cast-rules-gen ((dtype typep) (stype typep))
    :guard (and (type-nonchar-integerp dtype)
                (type-nonchar-integerp stype))
    :returns (mv (name symbolp) (event pseudo-event-formp))
    :parents nil
    (b* ((dfixtype (integer-type-to-fixtype dtype))
         (sfixtype (integer-type-to-fixtype stype))
         (spred (pack sfixtype 'p))
         (name (pack 'exec-cast-of- dfixtype '-when- spred))
         (dtyname (type-to-tyname dtype))
         (dtype-from-stype (pack dfixtype '-from- sfixtype))
         (dtype-from-stype-okp (pack dtype-from-stype '-okp))
         (guardp (and
                  (not (equal dtype stype))
                  (or (type-case dtype :schar)
                      (and (type-case dtype :sshort)
                           (not (member-eq (type-kind stype)
                                           '(:schar))))
                      (and (type-case dtype :sint)
                           (not (member-eq (type-kind stype)
                                           '(:schar :sshort))))
                      (and (type-case dtype :slong)
                           (not (member-eq (type-kind stype)
                                           '(:schar :sshort :sint))))
                      (and (type-case dtype :sllong)
                           (not (member-eq (type-kind stype)
                                           '(:schar :sshort :sint :slong)))))))
         (hyps `(and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                     (,spred x)
                     ,@(and guardp `((,dtype-from-stype-okp x)))))
         (rhs (if (equal dtype stype)
                  'x
                `(,dtype-from-stype x)))
         (formula `(implies ,hyps
                            (equal (exec-cast ',dtyname x)
                                   ,rhs)))
         (hints `(:enable
                  (exec-cast
                   convert-integer-value
                   value-integer
                   ,@*atc-value-integer->get-rules*
                   integer-type-rangep
                   integer-type-min
                   integer-type-max
                   value-schar-to-schar
                   value-uchar-to-uchar
                   value-sshort-to-sshort
                   value-ushort-to-ushort
                   value-sint-to-sint
                   value-uint-to-uint
                   value-slong-to-slong
                   value-ulong-to-ulong
                   value-sllong-to-sllong
                   value-ullong-to-ullong
                   uchar-mod
                   ushort-mod
                   uint-mod
                   ulong-mod
                   ullong-mod
                   schar-integerp-alt-def
                   uchar-integerp-alt-def
                   sshort-integerp-alt-def
                   ushort-integerp-alt-def
                   sint-integerp-alt-def
                   uint-integerp-alt-def
                   slong-integerp-alt-def
                   ulong-integerp-alt-def
                   sllong-integerp-alt-def
                   ullong-integerp-alt-def
                   ,@(and (not (equal dtype stype))
                          (list dtype-from-stype))
                   ,@(and guardp
                          (list dtype-from-stype-okp)))
                  :disable
                  ((:e integer-type-rangep)
                   (:e integer-type-max)
                   (:e integer-type-min))))
         (event `(defruled ,name
                   ,formula
                   ,@hints)))
      (mv name event)))

  (define atc-exec-cast-rules-gen-loop-stypes ((dtype typep)
                                               (stypes type-listp))
    :guard (and (type-nonchar-integerp dtype)
                (type-nonchar-integer-listp stypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp stypes)) (mv nil nil))
         ((mv name event) (atc-exec-cast-rules-gen dtype
                                                   (car stypes)))
         ((mv names events) (atc-exec-cast-rules-gen-loop-stypes dtype
                                                                 (cdr stypes))))
      (mv (cons name names) (cons event events))))

  (define atc-exec-cast-rules-gen-loop-dtypes ((dtypes type-listp)
                                               (stypes type-listp))
    :guard (and (type-nonchar-integer-listp dtypes)
                (type-nonchar-integer-listp stypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp dtypes)) (mv nil nil))
         ((mv names events) (atc-exec-cast-rules-gen-loop-stypes (car dtypes)
                                                                 stypes))
         ((mv names1 events1) (atc-exec-cast-rules-gen-loop-dtypes (cdr dtypes)
                                                                   stypes)))
      (mv (append names names1) (append events events1))))

  (define atc-exec-cast-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-cast-rules-gen-loop-dtypes
           *nonchar-integer-types**
           *nonchar-integer-types**)))
      `(progn
         (defsection atc-exec-cast-rules
           :short "Rules for executing casts."
           ,@events
           (defval *atc-exec-cast-rules*
             '(,@names)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-cast-rules-gen-all))
