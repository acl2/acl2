; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../representation/integer-operations")

(include-book "../arrays")

(local (include-book "kestrel/typed-lists-light/true-list-listp" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-ops-1-return-rewrite-rules*
  :short "List of rewrite rules for the return types of
          models of C integer operations that involve one C integer type."
  (b* ((ops '(plus minus bitnot lognot)))
    (atc-integer-ops-1-return-names-loop-ops ops
                                             *nonchar-integer-types*))

  :prepwork

  ((define atc-integer-ops-1-return-names-loop-types ((op symbolp)
                                                      (types type-listp))
     :guard (and (member-eq op '(plus minus bitnot lognot))
                 (type-nonchar-integer-listp types))
     :returns (names symbol-listp)
     :parents nil
     (cond
      ((endp types) nil)
      (t (b* ((type (car types))
              (argfixtype (integer-type-to-fixtype type))
              (restype (if (eq op 'lognot) (type-sint) (promote-type type)))
              (resfixtype (integer-type-to-fixtype restype))
              (respred (pack resfixtype 'p)))
           (cons (pack respred '-of- op '- argfixtype)
                 (atc-integer-ops-1-return-names-loop-types op (cdr types))))))
     :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                              type-realp))))

   (define atc-integer-ops-1-return-names-loop-ops ((ops symbol-listp)
                                                    (types type-listp))
     :guard (and (subsetp-eq ops '(plus minus bitnot lognot))
                 (type-nonchar-integer-listp types))
     :returns (names symbol-listp)
     :parents nil
     (cond ((endp ops) nil)
           (t (append
               (atc-integer-ops-1-return-names-loop-types (car ops) types)
               (atc-integer-ops-1-return-names-loop-ops (cdr ops) types)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-ops-2-return-rewrite-rules*
  :short "List of rewrite rules for the return types of
          models of C integer operations that involve two C integer types."
  (b* ((ops (list 'add 'sub 'mul 'div 'rem
                  'shl 'shr
                  'lt 'gt 'le 'ge 'eq 'ne
                  'bitand 'bitxor 'bitior)))
    (atc-integer-ops-2-return-names-loop-ops ops
                                             *nonchar-integer-types*
                                             *nonchar-integer-types*))

  :prepwork

  ((define atc-integer-ops-2-return-names-loop-right-types ((op symbolp)
                                                            (ltype typep)
                                                            (rtypes type-listp))
     :guard (and (member-eq op (list 'add 'sub 'mul 'div 'rem
                                     'shl 'shr
                                     'lt 'gt 'le 'ge 'eq 'ne
                                     'bitand 'bitxor 'bitior))
                 (type-nonchar-integerp ltype)
                 (type-nonchar-integer-listp rtypes))
     :returns (names symbol-listp)
     :parents nil
     (cond
      ((endp rtypes) nil)
      (t (b* ((rtype (car rtypes))
              (type (cond ((member-eq op '(lt gt le ge eq ne)) (type-sint))
                          ((member-eq op '(shl shr)) (promote-type ltype))
                          (t (uaconvert-types ltype rtype))))
              (lfixtype (integer-type-to-fixtype ltype))
              (rfixtype (integer-type-to-fixtype rtype))
              (fixtype (integer-type-to-fixtype type))
              (pred (pack fixtype 'p)))
           (cons
            (pack pred '-of- op '- lfixtype '- rfixtype)
            (atc-integer-ops-2-return-names-loop-right-types op
                                                             ltype
                                                             (cdr rtypes))))))
     :guard-hints (("Goal" :in-theory (enable type-arithmeticp type-realp))))

   (define atc-integer-ops-2-return-names-loop-left-types ((op symbolp)
                                                           (ltypes type-listp)
                                                           (rtypes type-listp))
     :guard (and (member-eq op (list 'add 'sub 'mul 'div 'rem
                                     'shl 'shr
                                     'lt 'gt 'le 'ge 'eq 'ne
                                     'bitand 'bitxor 'bitior))
                 (type-nonchar-integer-listp ltypes)
                 (type-nonchar-integer-listp rtypes))
     :returns (names symbol-listp)
     :parents nil
     (cond ((endp ltypes) nil)
           (t (append
               (atc-integer-ops-2-return-names-loop-right-types op
                                                                (car ltypes)
                                                                rtypes)
               (atc-integer-ops-2-return-names-loop-left-types op
                                                               (cdr ltypes)
                                                               rtypes)))))

   (define atc-integer-ops-2-return-names-loop-ops ((ops symbol-listp)
                                                    (ltypes type-listp)
                                                    (rtypes type-listp))
     :guard (and (subsetp-eq ops (list 'add 'sub 'mul 'div 'rem
                                       'shl 'shr
                                       'lt 'gt 'le 'ge 'eq 'ne
                                       'bitand 'bitxor 'bitior))
                 (type-nonchar-integer-listp ltypes)
                 (type-nonchar-integer-listp rtypes))
     :returns (names symbol-listp)
     :parents nil
     (cond ((endp ops) nil)
           (t (append
               (atc-integer-ops-2-return-names-loop-left-types (car ops)
                                                               ltypes
                                                               rtypes)
               (atc-integer-ops-2-return-names-loop-ops (cdr ops)
                                                        ltypes
                                                        rtypes)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-convs-return-rewrite-rules*
  :short "List of rewrite rules for the return types of
          models of C integer conversions."
  (atc-integer-convs-return-names-loop-src-types
   *nonchar-integer-types*
   *nonchar-integer-types*)

  :prepwork

  ((define atc-integer-convs-return-names-loop-dst-types ((stype typep)
                                                          (dtypes type-listp))
     :guard (and (type-nonchar-integerp stype)
                 (type-nonchar-integer-listp dtypes))
     :returns (names symbol-listp)
     :parents nil
     (cond
      ((endp dtypes) nil)
      ((equal stype (car dtypes))
       (atc-integer-convs-return-names-loop-dst-types stype
                                                      (cdr dtypes)))
      (t (b* ((sfixtype (integer-type-to-fixtype stype))
              (dfixtype (integer-type-to-fixtype (car dtypes)))
              (pred (pack dfixtype 'p)))
           (cons
            (pack pred '-of- dfixtype '-from- sfixtype)
            (atc-integer-convs-return-names-loop-dst-types stype
                                                           (cdr dtypes)))))))

   (define atc-integer-convs-return-names-loop-src-types ((stypes type-listp)
                                                          (dtypes type-listp))
     :guard (and (type-nonchar-integer-listp stypes)
                 (type-nonchar-integer-listp dtypes))
     :returns (names symbol-listp)
     :parents nil
     (cond ((endp stypes) nil)
           (t (append
               (atc-integer-convs-return-names-loop-dst-types (car stypes)
                                                              dtypes)
               (atc-integer-convs-return-names-loop-src-types (cdr stypes)
                                                              dtypes)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-array-read-return-rewrite-rules*
  :short "List of rewrite rules for the return types of
          models of C array read operations."
  '(ucharp-of-uchar-array-read
    scharp-of-schar-array-read
    ushortp-of-ushort-array-read
    sshortp-of-sshort-array-read
    uintp-of-uint-array-read
    sintp-of-sint-array-read
    ulongp-of-ulong-array-read
    slongp-of-slong-array-read
    ullongp-of-ullong-array-read
    sllongp-of-sllong-array-read))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-array-write-return-rewrite-rules*
  :short "List of rewrite rules for the return types of
          models of C array write operations."
  '(uchar-arrayp-of-uchar-array-write
    schar-arrayp-of-schar-array-write
    ushort-arrayp-of-ushort-array-write
    sshort-arrayp-of-sshort-array-write
    uint-arrayp-of-uint-array-write
    sint-arrayp-of-sint-array-write
    ulong-arrayp-of-ulong-array-write
    slong-arrayp-of-slong-array-write
    ullong-arrayp-of-ullong-array-write
    sllong-arrayp-of-sllong-array-write))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-ops-1-type-prescription-rules*
  :short "List of type prescription rules for the
          models of C integer operations that involve one C integer type."
  (b* ((ops '(plus minus bitnot lognot)))
    (atc-integer-ops-1-type-presc-rules-loop-ops
     ops
     *nonchar-integer-types*))

  :prepwork

  ((define atc-integer-ops-1-type-presc-rules-loop-types ((op symbolp)
                                                          (types type-listp))
     :guard (and (member-eq op '(plus minus bitnot lognot))
                 (type-nonchar-integer-listp types))
     :returns (rules true-list-listp)
     :parents nil
     (cond
      ((endp types) nil)
      (t (b* ((type (car types))
              (fixtype (integer-type-to-fixtype type)))
           (cons
            (list :t (pack op '- fixtype))
            (atc-integer-ops-1-type-presc-rules-loop-types op (cdr types)))))))

   (define atc-integer-ops-1-type-presc-rules-loop-ops ((ops symbol-listp)
                                                        (types type-listp))
     :guard (and (subsetp-eq ops '(plus minus bitnot lognot))
                 (type-nonchar-integer-listp types))
     :returns (rule true-list-listp)
     :parents nil
     (cond
      ((endp ops) nil)
      (t (append
          (atc-integer-ops-1-type-presc-rules-loop-types (car ops) types)
          (atc-integer-ops-1-type-presc-rules-loop-ops (cdr ops) types)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-ops-2-type-prescription-rules*
  :short "List of type prescription rules for the
          models of C integer operations that involve two C integer types."
  (b* ((ops (list 'add 'sub 'mul 'div 'rem
                  'shl 'shr
                  'lt 'gt 'le 'ge 'eq 'ne
                  'bitand 'bitxor 'bitior)))
    (atc-integer-ops-2-type-presc-rules-loop-ops
     ops
     *nonchar-integer-types*
     *nonchar-integer-types*))

  :prepwork

  ((define atc-integer-ops-2-type-presc-rules-loop-right-types
     ((op symbolp)
      (ltype typep)
      (rtypes type-listp))
     :guard (and (member-eq op (list 'add 'sub 'mul 'div 'rem
                                     'shl 'shr
                                     'lt 'gt 'le 'ge 'eq 'ne
                                     'bitand 'bitxor 'bitior))
                 (type-nonchar-integerp ltype)
                 (type-nonchar-integer-listp rtypes))
     :returns (rules true-list-listp)
     :parents nil
     (cond
      ((endp rtypes) nil)
      (t (b* ((rtype (car rtypes))
              (lfixtype (integer-type-to-fixtype ltype))
              (rfixtype (integer-type-to-fixtype rtype)))
           (cons
            (list :t (pack op '- lfixtype '- rfixtype))
            (atc-integer-ops-2-type-presc-rules-loop-right-types
             op
             ltype
             (cdr rtypes))))))
     :guard-hints (("Goal" :in-theory (enable type-arithmeticp type-realp))))

   (define atc-integer-ops-2-type-presc-rules-loop-left-types
     ((op symbolp)
      (ltypes type-listp)
      (rtypes type-listp))
     :guard (and (member-eq op (list 'add 'sub 'mul 'div 'rem
                                     'shl 'shr
                                     'lt 'gt 'le 'ge 'eq 'ne
                                     'bitand 'bitxor 'bitior))
                 (type-nonchar-integer-listp ltypes)
                 (type-nonchar-integer-listp rtypes))
     :returns (rules true-list-listp)
     :parents nil
     (cond ((endp ltypes) nil)
           (t (append
               (atc-integer-ops-2-type-presc-rules-loop-right-types op
                                                                    (car ltypes)
                                                                    rtypes)
               (atc-integer-ops-2-type-presc-rules-loop-left-types op
                                                                   (cdr ltypes)
                                                                   rtypes)))))

   (define atc-integer-ops-2-type-presc-rules-loop-ops ((ops symbol-listp)
                                                        (ltypes type-listp)
                                                        (rtypes type-listp))
     :guard (and (subsetp-eq ops (list 'add 'sub 'mul 'div 'rem
                                       'shl 'shr
                                       'lt 'gt 'le 'ge 'eq 'ne
                                       'bitand 'bitxor 'bitior))
                 (type-nonchar-integer-listp ltypes)
                 (type-nonchar-integer-listp rtypes))
     :returns (rules true-list-listp)
     :parents nil
     (cond ((endp ops) nil)
           (t (append
               (atc-integer-ops-2-type-presc-rules-loop-left-types (car ops)
                                                                   ltypes
                                                                   rtypes)
               (atc-integer-ops-2-type-presc-rules-loop-ops (cdr ops)
                                                            ltypes
                                                            rtypes)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-convs-type-prescription-rules*
  :short "List of type prescription rules for the
          models of C integer conversions."
  (atc-integer-convs-type-presc-rules-loop-src-types
   *nonchar-integer-types*
   *nonchar-integer-types*)

  :prepwork

  ((define atc-integer-convs-type-presc-rules-loop-dst-types
     ((stype typep)
      (dtypes type-listp))
     :guard (and (type-nonchar-integerp stype)
                 (type-nonchar-integer-listp dtypes))
     :returns (rules true-list-listp)
     :parents nil
     (cond
      ((endp dtypes) nil)
      ((equal stype (car dtypes))
       (atc-integer-convs-type-presc-rules-loop-dst-types stype
                                                          (cdr dtypes)))
      (t (b* ((sfixtype (integer-type-to-fixtype stype))
              (dfixtype (integer-type-to-fixtype (car dtypes))))
           (cons
            (list :t (pack dfixtype '-from- sfixtype))
            (atc-integer-convs-type-presc-rules-loop-dst-types
             stype
             (cdr dtypes)))))))

   (define atc-integer-convs-type-presc-rules-loop-src-types
     ((stypes type-listp)
      (dtypes type-listp))
     :guard (and (type-nonchar-integer-listp stypes)
                 (type-nonchar-integer-listp dtypes))
     :returns (rules true-list-listp)
     :parents nil
     (cond ((endp stypes) nil)
           (t (append
               (atc-integer-convs-type-presc-rules-loop-dst-types (car stypes)
                                                                  dtypes)
               (atc-integer-convs-type-presc-rules-loop-src-types (cdr stypes)
                                                                  dtypes)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-array-read-type-prescription-rules*
  :short "List of type prescription rules for the
          models of C array read operations."
  '((:t uchar-array-read)
    (:t schar-array-read)
    (:t ushort-array-read)
    (:t sshort-array-read)
    (:t uint-array-read)
    (:t sint-array-read)
    (:t ulong-array-read)
    (:t slong-array-read)
    (:t ullong-array-read)
    (:t sllong-array-read)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-array-write-type-prescription-rules*
  :short "List of type prescription rules for the
          models of C array write operations."
  '((:t uchar-array-write)
    (:t schar-array-write)
    (:t ushort-array-write)
    (:t sshort-array-write)
    (:t uint-array-write)
    (:t sint-array-write)
    (:t ulong-array-write)
    (:t slong-array-write)
    (:t ullong-array-write)
    (:t sllong-array-write)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-pointed-integers-type-prescription-rules*
  :short "List of type prescription rules for the
          readers and writers of integers by pointer."
  '((:t schar-read)
    (:t uchar-read)
    (:t sshort-read)
    (:t ushort-read)
    (:t sint-read)
    (:t uint-read)
    (:t slong-read)
    (:t ulong-read)
    (:t sllong-read)
    (:t ullong-read)
    (:t schar-write)
    (:t uchar-write)
    (:t sshort-write)
    (:t ushort-write)
    (:t sint-write)
    (:t uint-write)
    (:t slong-write)
    (:t ulong-write)
    (:t sllong-write)
    (:t ullong-write)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-boolean-from-integer-return-rules
  :short "Rules about the return types of @('boolean-from-<type>')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also include the type prescription rules for these functions.
     The reason is that we have observed that,
     in the presence of the non-strict operators @('&&') and @('||'),
     the symbolic execution may produce
     equalities between @('t') and calls of these functions,
     under a hypothesis that the call holds (i.e. is not @('nil')).
     This situation arises because of the case splits engendered by
     the rules for @(tsee exec-expr-pure) on @('&&') and @('||')
     and the rules for @(tsee test-value)."))

  (defval *atc-boolean-from-integer-return-rules*
    '(booleanp-of-boolean-from-uchar
      booleanp-of-boolean-from-schar
      booleanp-of-boolean-from-ushort
      booleanp-of-boolean-from-sshort
      booleanp-of-boolean-from-uint
      booleanp-of-boolean-from-sint
      booleanp-of-boolean-from-ulong
      booleanp-of-boolean-from-slong
      booleanp-of-boolean-from-ullong
      booleanp-of-boolean-from-sllong
      (:t boolean-from-uchar)
      (:t boolean-from-schar)
      (:t boolean-from-ushort)
      (:t boolean-from-sshort)
      (:t boolean-from-uint)
      (:t boolean-from-sint)
      (:t boolean-from-ulong)
      (:t boolean-from-slong)
      (:t boolean-from-ullong)
      (:t boolean-from-sllong))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-constructors-return-rules
  :short "Rules about the return types of the integer constructors."

  (defval *atc-integer-constructors-return-rules*
    '(scharp-of-schar-from-integer
      ucharp-of-uchar-from-integer
      sshortp-of-sshort-from-integer
      ushortp-of-ushort-from-integer
      sintp-of-sint-from-integer
      uintp-of-uint-from-integer
      slongp-of-slong-from-integer
      ulongp-of-ulong-from-integer
      sllongp-of-sllong-from-integer
      ullongp-of-ullong-from-integer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-computation-state-return-rules
  :short "Rules about return types of
          functions related to the computation state."

  (defval *atc-computation-state-return-rules*
    '(compustatep-of-add-frame
      compustatep-of-enter-scope
      compustatep-of-add-var
      compustatep-of-update-var
      compustatep-of-update-static-var
      compustatep-of-update-object
      compustatep-when-compustate-resultp-and-not-errorp
      compustate-resultp-of-write-var
      heapp-of-compustate->heap
      scopep-of-update)))
