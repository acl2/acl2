; Macro generating theorems and rewrite rules for native C array code generation
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Karthik Nukala (nukala@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/c/atc/arrays" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)

;; All the integer types except the plain 'char' type.
;; Note that these are in the ACL2 package
;; TODO: Redo this to use the new constant, but those names are in the C package.
(defconst *non-char-integer-type-names*
  '(schar uchar sshort ushort sint uint slong ulong sllong ullong))

(defmacro pack-c (&rest args)
  `(acl2::pack-in-package "C" ,@args))

(defun def-array-support-fn (type)
  (declare (xargs :guard (member-eq type *non-char-integer-type-names*)))
  (b* (;; (type-p (acl2::pack$ type 'p))
       (c-type-constructor (pack-c type '-from-integer))
       ;; (c-type-p (pack-c type-p))
       (c-type-fix (pack-c type '-fix))
       (c-type-listp (pack-c type '-listp))
       (c-type-list-fix (pack-c type '-list-fix))
       (c-type-arrayp (pack-c type '-arrayp))
       (c-type-array-of (pack-c type '-array-of))
       (c-type-array->elemtype (pack-c type '-array->elemtype))
       (c-type-array->elements (pack-c type '-array->elements))
       (c-type-array-length (pack-c type '-array-length))
       ;; (c-type-array-read-sint (pack-c type '-array-read-sint))
       (c-type-array-read (pack-c type '-array-read))
       (c-type-array-write (pack-c type '-array-write))
       ;; (c-type-array-integer-write (pack-c type '-array-integer-write))
       (c-type-array-integer-index-okp (pack-c type '-array-integer-index-okp))
       (c-type-array-index-okp (pack-c type '-array-index-okp))
       ;; (c-type-list-from-integer-list (pack-c type '-list-from-integer-list))
       )
    `(encapsulate
       ()

       (local (include-book "kestrel/lists-light/len" :dir :system))
       (local (in-theory (disable update-nth))) ; prevent induction

       ;; We always want these enabled:
       ;; See also what's done in theories.lisp
       (in-theory (enable ,c-type-array-integer-index-okp
                          ,c-type-array-index-okp
                          ;; ,(pack-c type '-array-schar-index-okp)
                          ;; ,(pack-c type '-array-sshort-index-okp)
                          ;; ,(pack-c type '-array-sint-index-okp)
                          ;; ,(pack-c type '-array-slong-index-okp)
                          ;; ,(pack-c type '-array-sllong-index-okp)
                          ;; ,(pack-c type '-array-uchar-index-okp)
                          ;; ,(pack-c type '-array-ushort-index-okp)
                          ;; ,(pack-c type '-array-uint-index-okp)
                          ;; ,(pack-c type '-array-ulong-index-okp)
                          ;; ,(pack-c type '-array-ullong-index-okp)

                          ;; Let's treat this as an abbreviation and keep it
                          ;; enabled, to expose things like
                          ;; uchar-array->elements, since we use such functions
                          ;; (currently) to convert between lists and arrays.
                          ,(pack-c type '-array-length)))

       ;; (defthmd ,(pack-c 'nth-of- c-type-list-from-integer-list)
       ;;   (implies (and (natp n)
       ;;                 (< n (len x)))
       ;;            (equal (nth n (,c-type-list-from-integer-list x))
       ;;                   (,c-type-constructor (nth n x))))
       ;;   :hints (("Goal" :in-theory (enable ,c-type-list-from-integer-list))))

       ;; Converts the NTH into an array-read.  Chooses to make the index a sint.
       (defthmd ,(pack-c 'nth-of- c-type-array->elements '-becomes- c-type-array-read)
          (implies (and (,c-type-arrayp array)
                        (natp x)
                        (sint-integerp x)
                        (> (len (,c-type-array->elements array)) x))
                   (equal (nth x (,c-type-array->elements array))
                          (,c-type-array-read array (sint-from-integer x))))
          :hints (("Goal" :in-theory (enable ,c-type-array-read
                                             integer-from-cinteger-alt-def))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defthmd ,(pack-c c-type-list-fix '-of-update-nth)
         (implies (and (natp n)
                       (< n (len list)))
                  (equal (,c-type-list-fix (update-nth n value list))
                         (update-nth n (,c-type-fix value) (,c-type-list-fix list))))
         :hints (("Goal" :in-theory (enable ,c-type-list-fix update-nth))))

       ;; ;; Turns the C array write into an UPDATE-NTH and pushes the conversion inward.
       ;; (defthmd ,(pack-c c-type-array->elements '-of- c-type-array-integer-write)
       ;;   (implies (and (,c-type-arrayp array)
       ;;                 (natp index)
       ;;                 (< index (len (,c-type-array->elements array))))
       ;;            (equal (,c-type-array->elements (,c-type-array-integer-write array index element))
       ;;                   (update-nth index (,c-type-fix element) (,c-type-array->elements array))))
       ;;   :hints (("Goal" :in-theory (enable ,c-type-array-integer-write
       ;;                                      ,c-type-array-integer-index-okp
       ;;                                      ,c-type-array-length
       ;;                                      ,c-type-array-of))))

       ;; ;; Turns the UPDATE-NTH into a C array write and pushes the conversion inward.
       ;; (defthmd ,(pack-c c-type-array-of '-of-update-nth-becomes- c-type-array-integer-write)
       ;;   (implies (and (,c-type-listp x)
       ;;                 (natp n)
       ;;                 (< n (len x)))
       ;;            (equal (,c-type-array-of (update-nth n y x))
       ;;                   (,c-type-array-integer-write (,c-type-array-of x) n y)))
       ;;   :hints (("Goal" :in-theory (enable ,(pack-c c-type-list-fix '-of-update-nth)
       ;;                                      ,c-type-array-integer-write
       ;;                                      ,c-type-array-integer-index-okp
       ;;                                      ,c-type-array-length
       ;;                                      ,c-type-array-of))))

       ;; (theory-invariant (incompatible (:rewrite ,(pack-c c-type-array-of '-of-update-nth-becomes- c-type-array-integer-write))
       ;;                                 (:definition ,c-type-array-integer-write)))

       ;; Turns the UPDATE-NTH into a C array write.  This chooses to make the index a SINT.
       ;; Could also make a rule for (sint-array (type-sint) (update-nth ...)) but let's
       ;; try to always use the "array-of" function.
       (defthmd ,(pack-c c-type-array-of '-of-update-nth-becomes- c-type-array-write)
         (implies (and (,c-type-listp x)
                       (natp n)
                       (< n (len x))
                       (sint-integerp n))
                  (equal (,c-type-array-of (update-nth n y x))
                         (,c-type-array-write (,c-type-array-of x) (sint-from-integer n) y)))
         :hints (("Goal" :in-theory (enable ,(pack-c c-type-list-fix '-of-update-nth)
                                            ,c-type-array-integer-index-okp
                                            ,c-type-array-write
                                            ,c-type-array-of
                                            ,c-type-array->elemtype
                                            ;; ,(pack-c 'update-nth-> type '-array-write)
                                            integer-from-cinteger-alt-def
                                            ,c-type-array-length
                                            ))))

       ;; Already in books/kestrel/c/atc/arrays.lisp
       ;; (defthm ,(pack-c 'len-of- type '-array->elements-of- type '-array-integer-write)
       ;;   (equal (len (,c-type-array->elements (,c-type-array-integer-write array i x)))
       ;;          (len (,c-type-array->elements array)))
       ;;   :hints (("Goal" :in-theory (enable ,c-type-array-integer-index-okp
       ;;                                      ,c-type-array-length))))

       ;; Already in books/kestrel/c/atc/arrays.lisp
       ;; (defthm ,(pack-c 'len-of- type '-array->elements-of- type '-array-write)
       ;;   (equal (len (,c-type-array->elements (,c-type-array-write array i x)))
       ;;          (len (,c-type-array->elements array)))
       ;;   :hints (("Goal" :in-theory (enable ,c-type-array-integer-index-okp
       ;;                                      ,c-type-array-length))))

       ;; Basically an inversion theorem
       (defthm ,(pack-c c-type-array->elements '-of- c-type-array-of)
         (equal (,c-type-array->elements (,c-type-array-of elements))
                (if (consp elements)
                    (,c-type-list-fix elements)
                  ;; unusual case:
                  (list (,c-type-constructor 0))))
         :hints (("Goal" :in-theory (enable ,c-type-array-of ,c-type-array-length))))

       ;; This theory can be enabled to cause C array functions to be introduced.
       (deftheory ,(pack-c type '-array-intro-rules)
           '(,(pack-c 'nth-of- c-type-array->elements '-becomes- c-type-array-read)
             ,(pack-c c-type-array-of '-of-update-nth-becomes- c-type-array-write))))))

(defmacro def-array-support (type)
  (declare (xargs :guard (member-eq type *non-char-integer-type-names*)))
  (def-array-support-fn type))
