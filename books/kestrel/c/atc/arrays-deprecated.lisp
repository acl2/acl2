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

(include-book "arrays")

(local (include-book "std/typed-lists/atom-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Deprecated operations.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays-indices ((etype typep) (itype typep))
  :guard (and (type-nonchar-integerp etype)
              (type-nonchar-integerp itype))
  :returns (event pseudo-event-formp)

  (b* ((<etype> (integer-type-to-fixtype etype))
       (<itype> (integer-type-to-fixtype itype))
       (<etype>p (pack <etype> 'p))
       (<itype>p (pack <itype> 'p))
       (<etype>-array (pack <etype> '-array))
       (<etype>-arrayp (pack <etype>-array 'p))
       (<etype>-array->elements (pack <etype>-array '->elements))
       (<etype>-array-length (pack <etype>-array '-length))
       (<etype>-array-integer-index-okp (pack <etype>
                                              '-array-integer-index-okp))
       (<etype>-array-integer-read (pack <etype>-array '-integer-read))
       (<etype>-array-integer-write (pack <etype>-array '-integer-write))
       (integer-from-<itype> (pack 'integer-from- <itype>))
       (<etype>-array-<itype>-index-okp (pack
                                         <etype> '-array- <itype> '-index-okp))
       (<etype>-array-read-<itype> (pack <etype> '-array-read- <itype>))
       (<etype>-array-write-<itype> (pack <etype> '-array-write- <itype>))
       (<etype>-array-index-okp (pack <etype> '-array-index-okp))
       (<etype>-array-read (pack <etype> '-array-read))
       (<etype>-array-write (pack <etype> '-array-write))
       (len-of-<etype>-array->elements-of-<etype>-array-write-<itype>
        (pack
         'len-of- <etype>-array->elements '-of- <etype>-array-write-<itype>))
       (<etype>-array-length-of-<etype>-array-write-<itype>
        (pack <etype> '-array-length-of- <etype>-array-write-<itype>)))

    `(progn

       ,@(and (type-case etype :char)
              (raise "Type ~x0 not supported." etype))

       ,@(and (type-case itype :char)
              (raise "Type ~x0 not supported." itype))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<etype>-array-<itype>-index-okp ((array ,<etype>-arrayp)
                                                 (index ,<itype>p))
         :returns (yes/no booleanp)
         (,<etype>-array-integer-index-okp array (,integer-from-<itype> index))
         :hooks (:fix)
         ///

         (defruled ,(pack <etype>-array-<itype>-index-okp '-alt-def)
           (implies (,<itype>p index)
                    (equal (,<etype>-array-<itype>-index-okp array index)
                           (,<etype>-array-index-okp array index)))
           :enable (,<etype>-array-<itype>-index-okp
                    ,<etype>-array-integer-index-okp
                    ,<etype>-array-index-okp
                    integer-from-cinteger-alt-def
                    ifix)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<etype>-array-read-<itype> ((array ,<etype>-arrayp)
                                            (index ,<itype>p))
         :guard (,<etype>-array-<itype>-index-okp array index)
         :returns (element ,<etype>p)
         (,<etype>-array-integer-read array (,integer-from-<itype> index))
         :guard-hints (("Goal"
                        :in-theory (enable ,<etype>-array-<itype>-index-okp)))
         :hooks (:fix)
         ///

         (defruled ,(pack <etype>-array-read-<itype> '-alt-def)
           (implies (,<itype>p index)
                    (equal (,<etype>-array-read-<itype> array index)
                           (,<etype>-array-read array index)))
           :enable (,<etype>-array-read-<itype>
                    ,<etype>-array-integer-read
                    ,<etype>-array-read
                    integer-from-cinteger-alt-def)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<etype>-array-write-<itype> ((array ,<etype>-arrayp)
                                             (index ,<itype>p)
                                             (element ,<etype>p))
         :guard (,<etype>-array-<itype>-index-okp array index)
         :returns (new-array ,<etype>-arrayp)
         (,<etype>-array-integer-write array
                                       (,integer-from-<itype> index)
                                       element)
         :guard-hints (("Goal"
                        :in-theory (enable ,<etype>-array-<itype>-index-okp)))
         :hooks (:fix)

         ///

         (defrule ,len-of-<etype>-array->elements-of-<etype>-array-write-<itype>
           (equal
            (len (,<etype>-array->elements
                  (,<etype>-array-write-<itype> array index element)))
            (len (,<etype>-array->elements array))))

         (defrule ,<etype>-array-length-of-<etype>-array-write-<itype>
           (equal (,<etype>-array-length
                   (,<etype>-array-write-<itype> array index element))
                  (,<etype>-array-length array)))

         (defruled ,(pack <etype>-array-write-<itype> '-alt-def)
           (implies (,<itype>p index)
                    (equal (,<etype>-array-write-<itype> array index element)
                           (,<etype>-array-write array index element)))
           :enable (,<etype>-array-write-<itype>
                    ,<etype>-array-integer-write
                    ,<etype>-array-write
                    integer-from-cinteger-alt-def
                    ,<etype>-array-index-okp
                    ,<etype>-array-integer-index-okp
                    ifix)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays-loop-inner ((etype typep) (itypes type-listp))
  :guard (and (type-nonchar-integerp etype)
              (type-nonchar-integer-listp itypes))
  :returns (events pseudo-event-form-listp)
  (cond ((endp itypes) nil)
        (t (cons (atc-def-integer-arrays-indices etype (car itypes))
                 (atc-def-integer-arrays-loop-inner etype (cdr itypes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays-loop-outer ((etypes type-listp)
                                           (itypes type-listp))
  :guard (and (type-nonchar-integer-listp etypes)
              (type-nonchar-integer-listp itypes))
  :returns (events pseudo-event-form-listp)
  (cond ((endp etypes) nil)
        (t (append (atc-def-integer-arrays-loop-inner (car etypes) itypes)
                   (atc-def-integer-arrays-loop-outer (cdr etypes) itypes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(progn ,@(atc-def-integer-arrays-loop-outer *nonchar-integer-types*
                                              *nonchar-integer-types*)))
