; Support for proofs about R1CSes
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system)
(include-book "kestrel/prime-fields/rules2" :dir :system) ;reduce?
(include-book "kestrel/utilities/def-constant-opener" :dir :system) ;reduce?
(include-book "kestrel/lists-light/append-with-key" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system) ;for fe-listp, todo: reduce
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/bv/rules4" :dir :system))

;; TODO: Oraganize this material

;; For when the constant is negative.  Not sure which normal form is better.
(defthmd pfield::mul-when-constant-becomes-neg-of-mul
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (integerp k)
                (posp p))
           (equal (mul k x p)
                  (neg (mul (neg k p) x p) p)
                  ))
  :hints (("Goal" :in-theory (enable mul neg sub))))

;(acl2::def-constant-opener neg)
;(acl2::def-constant-opener pfield::pos-fix)
(acl2::def-constant-opener unsigned-byte-p) ;todo: built into basic evaluator!
(acl2::def-constant-opener acl2::integer-range-p)

;;todo: use an axe-bind-free rule?
(defthm pfield::move-negation-1
  (implies (and (fep lhs p) ;gen?
                (integerp x2)
                (integerp x3)
                (integerp y)
                (integerp lhs)
                (posp p))
           (equal (equal lhs (add x1 (add x2 (add (neg y p) x3 p) p) p))
                  (equal (add lhs y p) (add x1 (add x2 x3 p) p)))))

;; Not sure which form is better
(defthmd pfield::add-of-neg-and-neg
  (implies (and (posp p)
                ;(integerp x)
                ;(integerp y)
                )
           (equal (add (neg x p) (neg y p) p)
                  (neg (add x y p) p))))

(defthmd acl2::if-of-t-and-nil-when-booleanp
  (implies (booleanp x)
           (equal (if x t nil)
                  x)))

(defthm pfield::neg-of-mod
  (equal (neg (mod x p) p)
         (neg x p)))

;for axe
(defthm acl2::not-<-of-bvcat-and-0
  (not (< (acl2::bvcat highsize highval lowsize lowval) 0)))

;mixes prime fields and bvs
(defthm acl2::fep-of-bvcat
  (implies (and (< (expt 2 (+ highsize lowsize)) p)
                (natp highsize)
                (natp lowsize)
                (posp p))
           (fep (acl2::bvcat highsize highval lowsize lowval)
                p)))

; Split off the sign bit (often not used?) and turn add into bvplus
(defthmd acl2::adding-8-idiom
  (implies (and (bitp x)
                (unsigned-byte-p 8 y)
                (unsigned-byte-p 8 w)
                (unsigned-byte-p 8 z)
                ;;(natp w)
                ;;(natp z)
                (posp p)
                (< 512 p) ;tight?
                )
           (equal (equal (acl2::bvcat 1 x 8 y) (add w z p))
                  (and (equal x (acl2::getbit 8 (acl2::bvplus 9 w z)))
                       (equal y (acl2::bvplus 8 w z)))))
  :hints (("Goal" :in-theory (enable add acl2::bvplus))))

(defthm acl2::adding-8-idiom-alt
  (implies (and (bitp x)
                (unsigned-byte-p 8 y)
                (unsigned-byte-p 8 w)
                (unsigned-byte-p 8 z)
                ;;(natp w)
                ;;(natp z)
                (posp p)
                (< 512 p) ;tight?
                )
           (equal (equal (add w z p) (acl2::bvcat 1 x 8 y))
                  (and (equal x (acl2::getbit 8 (acl2::bvplus 9 w z)))
                       (equal y (acl2::bvplus 8 w z)))))
  :hints (("Goal" :use (:instance acl2::adding-8-idiom))))

(defthm pfield::fep-when-fe-listp-and-member-equal
  (implies (and (fe-listp free p)
                (member-equal x free))
           (fep x p)))

(defun gen-fe-listp-assumption (vars)
  (declare (xargs :guard (and (symbol-listp vars)
                              (consp vars))))
  `(fe-listp ,(acl2::make-append-with-key-nest vars)))

;; test: (gen-fe-listp-assumption '(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))

(local (include-book "kestrel/lists-light/member-equal" :dir :system)) ;for member-equal-of-cons

;test
(thm
 (implies (fe-listp
           (acl2::append-with-key
            'x5
            (acl2::append-with-key 'x2
                             (acl2::append-with-key 'x10
                                              (cons x1 nil)
                                              (cons x10 nil))
                             (acl2::append-with-key 'x3
                                              (cons x2 nil)
                                              (acl2::append-with-key 'x4
                                                               (cons x3 nil)
                                                               (cons x4 nil))))
            (acl2::append-with-key 'x7
                             (acl2::append-with-key 'x6
                                              (cons x5 nil)
                                              (cons x6 nil))
                             (acl2::append-with-key 'x8
                                              (cons x7 nil)
                                              (acl2::append-with-key 'x9
                                                               (cons x8 nil)
                                                               (cons x9 nil)))))
           prime)
          (and (fep x1 prime)
               (fep x2 prime)
               (fep x3 prime)
               (fep x4 prime)
               (fep x5 prime)
               (fep x6 prime)
               (fep x7 prime)
               (fep x8 prime)
               (fep x9 prime)
               (fep x10 prime)))
 :hints (("Goal" :in-theory (disable member-equal
                                     ;;acl2::member-equal-becomes-memberp
                                     ))))

(include-book "kestrel/axe/dag-arrays" :dir :system)
(include-book "kestrel/axe/axe-syntax" :dir :system)

(defun var-less-than-unquoted-keyp (var-darg key-darg dag-array)
  (declare (xargs :guard (and (or (acl2::myquotep var-darg)
                                  (and (natp var-darg)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 var-darg))))
                              (or (acl2::myquotep key-darg)
                                  (and (natp key-darg)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 key-darg)))))))
  (and (consp key-darg) ;checks for quotep
       (let ((unquoted-key (unquote key-darg)))
         (and (symbolp unquoted-key)
              (natp var-darg)
              (let ((var-expr (aref1 'dag-array dag-array var-darg)))
                (and (symbolp var-expr)
                     (symbol-< var-expr unquoted-key)))))))

(defun var-not-less-than-unquoted-keyp (var-darg key-darg dag-array)
  (declare (xargs :guard (and (or (acl2::myquotep var-darg)
                                  (and (natp var-darg)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 var-darg))))
                              (or (acl2::myquotep key-darg)
                                  (and (natp key-darg)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 key-darg)))))))
  (and (consp key-darg) ;checks for quotep
       (let ((unquoted-key (unquote key-darg)))
         (and (symbolp unquoted-key)
              (natp var-darg)
              (let ((var-expr (aref1 'dag-array dag-array var-darg)))
                (and (symbolp var-expr)
                     (not (symbol-< var-expr unquoted-key))))))))

;; Restrict the search for VAR to the branch (namely, X) where we know it is.
(defthm member-equal-of-append-with-key-first-half-axe
  (implies (and (acl2::axe-syntaxp (var-less-than-unquoted-keyp var key dag-array))
                (member-equal var x))
           (member-equal var (acl2::append-with-key key x y)))
  :hints (("Goal" :in-theory (enable acl2::append-with-key))))

;; Restrict the search for VAR to the branch (namely, Y) where we know it is.
(defthm member-equal-of-append-with-key-second-half-axe
  (implies (and (acl2::axe-syntaxp (var-not-less-than-unquoted-keyp var key dag-array))
                (member-equal var y))
           (member-equal var (acl2::append-with-key key x y)))
  :hints (("Goal" :in-theory (enable acl2::append-with-key))))
