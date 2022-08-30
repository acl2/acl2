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

(include-book "../integer-operations")
(include-book "../arrays")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-ops-1-return-rewrite-rules*
  :short "List of rewrite rules for the return types of
          models of C integer operations that involve one C integer type."
  (b* ((ops '(plus minus bitnot lognot)))
    (atc-integer-ops-1-return-names-loop-ops ops
                                             *nonchar-integer-types**))

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
                                             *nonchar-integer-types**
                                             *nonchar-integer-types**))

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
   *nonchar-integer-types**
   *nonchar-integer-types**)

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
  (atc-array-read-return-names-loop-array-types *nonchar-integer-types**
                                                *nonchar-integer-types**)

  :prepwork

  ((define atc-array-read-return-names-loop-index-types ((atype typep)
                                                         (itypes type-listp))
     :guard (and (type-nonchar-integerp atype)
                 (type-nonchar-integer-listp itypes))
     :returns (names symbol-listp)
     :parents nil
     (cond
      ((endp itypes) nil)
      (t (b* ((afixtype (integer-type-to-fixtype atype))
              (ifixtype (integer-type-to-fixtype (car itypes)))
              (pred (pack afixtype 'p)))
           (cons
            (pack pred '-of- afixtype '-array-read- ifixtype)
            (atc-array-read-return-names-loop-index-types atype
                                                          (cdr itypes)))))))

   (define atc-array-read-return-names-loop-array-types ((atypes type-listp)
                                                         (itypes type-listp))
     :guard (and (type-nonchar-integer-listp atypes)
                 (type-nonchar-integer-listp itypes))
     :returns (names symbol-listp)
     :parents nil
     (cond ((endp atypes) nil)
           (t (append
               (atc-array-read-return-names-loop-index-types (car atypes)
                                                             itypes)
               (atc-array-read-return-names-loop-array-types (cdr atypes)
                                                             itypes)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-array-write-return-rewrite-rules*
  :short "List of rewrite rules for the return types of
          models of C array write operations."
  (atc-array-write-return-names-loop-array-types
   *nonchar-integer-types**
   *nonchar-integer-types**)

  :prepwork

  ((define atc-array-write-return-names-loop-index-types ((atype typep)
                                                          (itypes type-listp))
     :guard (and (type-nonchar-integerp atype)
                 (type-nonchar-integer-listp itypes))
     :returns (names symbol-listp)
     :parents nil
     (cond
      ((endp itypes) nil)
      (t (b* ((afixtype (integer-type-to-fixtype atype))
              (ifixtype (integer-type-to-fixtype (car itypes)))
              (pred (pack afixtype '-arrayp)))
           (cons
            (pack pred '-of- afixtype '-array-write- ifixtype)
            (atc-array-write-return-names-loop-index-types atype
                                                           (cdr itypes)))))))

   (define atc-array-write-return-names-loop-array-types ((atypes type-listp)
                                                          (itypes type-listp))
     :guard (and (type-nonchar-integer-listp atypes)
                 (type-nonchar-integer-listp itypes))
     :returns (names symbol-listp)
     :parents nil
     (cond ((endp atypes) nil)
           (t (append
               (atc-array-write-return-names-loop-index-types (car atypes)
                                                              itypes)
               (atc-array-write-return-names-loop-array-types (cdr atypes)
                                                              itypes)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-integer-ops-1-type-prescription-rules*
  :short "List of type prescription rules for the
          models of C integer operations that involve one C integer type."
  (b* ((ops '(plus minus bitnot lognot)))
    (atc-integer-ops-1-type-presc-rules-loop-ops
     ops
     *nonchar-integer-types**))

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
     *nonchar-integer-types**
     *nonchar-integer-types**))

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
   *nonchar-integer-types**
   *nonchar-integer-types**)

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
  (atc-array-read-type-presc-rules-loop-array-types
   *nonchar-integer-types**
   *nonchar-integer-types**)

  :prepwork

  ((define atc-array-read-type-presc-rules-loop-index-types
     ((atype typep) (itypes type-listp))
     :guard (and (type-nonchar-integerp atype)
                 (type-nonchar-integer-listp itypes))
     :returns (rules true-listp)
     :parents nil
     (cond
      ((endp itypes) nil)
      (t (b* ((afixtype (integer-type-to-fixtype atype))
              (ifixtype (integer-type-to-fixtype (car itypes))))
           (cons
            (list :t (pack afixtype '-array-read- ifixtype))
            (atc-array-read-type-presc-rules-loop-index-types atype
                                                              (cdr itypes)))))))

   (define atc-array-read-type-presc-rules-loop-array-types
     ((atypes type-listp) (itypes type-listp))
     :guard (and (type-nonchar-integer-listp atypes)
                 (type-nonchar-integer-listp itypes))
     :returns (rules true-listp)
     :parents nil
     (cond ((endp atypes) nil)
           (t (append
               (atc-array-read-type-presc-rules-loop-index-types (car atypes)
                                                                 itypes)
               (atc-array-read-type-presc-rules-loop-array-types (cdr atypes)
                                                                 itypes)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-boolean-from-integer-return-rules
  :short "Rules about the return types of @('boolean-from-<type>')."

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
      booleanp-of-boolean-from-sllong)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-constructors-return-rules
  :short "Rules about the return types of the integer constructors."

  (defval *atc-integer-constructors-return-rules*
    '(scharp-of-schar
      ucharp-of-uchar
      sshortp-of-sshort
      ushortp-of-ushort
      sintp-of-sint
      uintp-of-uint
      slongp-of-slong
      ulongp-of-ulong
      sllongp-of-sllong
      ullongp-of-ullong)))
