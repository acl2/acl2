; An simple evaluator supporting a basic set of functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A simple version of the Axe evaluator with verified guards and without skip-proofs.
;; This evaluator knows about a "basic" set of functions, hence the name.

(include-book "unguarded-primitives")
(include-book "unguarded-built-ins")
(include-book "unguarded-defuns")
(include-book "make-evaluator-simple")
(include-book "kestrel/lists-light/repeat-tail" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)

;; TODO: Add more functions!  Add more bv functions.
(defconst *axe-evaluator-basic-fns-and-aliases*
  '(;; note that IF (a primitive) is built into all evaluators
    (car car-unguarded) ; primitive
    (cdr cdr-unguarded) ; primitive
    cons ; primitive
    consp ; primitive
    equal ; primitive
    atom
    integerp ; primitive
    rationalp ; primitive
    complex-rationalp ; primitive
    acl2-numberp ; primitive
    stringp ; primitive
    symbolp ; primitive
    characterp ; primitive
    (complex complex-unguarded) ; primitive
    (realpart realpart-unguarded) ; primitive
    (imagpart imagpart-unguarded) ; primitive
    (intern-in-package-of-symbol intern-in-package-of-symbol-unguarded) ; primitive
    (pkg-imports pkg-imports-unguarded) ; primitive
    (pkg-witness pkg-witness-unguarded) ; primitive
    ;; todo: BAD-ATOM<= ?
    natp
    posp
    booleanp
    boolor
    booland
    bool-fix$inline
    true-listp
    (denominator denominator-unguarded) ; primitive
    (numerator numerator-unguarded) ; primitive
    (coerce coerce-unguarded) ; primitive
    all-natp
    all-unsigned-byte-p
    (acons acons-unguarded)
    (endp endp-unguarded)
    (take take-unguarded)
    (char-code char-code-unguarded) ; primitive
    (code-char code-char-unguarded) ; primitive
    (nthcdr nthcdr-unguarded)
    (reverse-list reverse-list-unguarded)
    repeat-tail
    (repeat repeat-unguarded)
    (binary-append binary-append-unguarded)
    (member-equal member-equal-unguarded)
    (unary-- unary---unguarded) ; primitive
    (expt expt-unguarded)
    (= =-unguarded)
    (unary-/ unary-/-unguarded) ; primitive
    (binary-+ binary-+-unguarded) ; primitive
    (binary-* binary-*-unguarded) ; primitive
    (mod mod-unguarded)
    (floor floor-unguarded)
    (ceiling ceiling-unguarded)
    (lg lg-unguarded)
    (eql eql-unguarded) ; not strictly needed if we turn EQL into EQUAL
    (eq eq-unguarded) ; not strictly needed if we turn EQ into EQUAL
    (< <-unguarded) ; primitive
    (zp zp-unguarded)
    not
    len
    (assoc-equal assoc-equal-unguarded)
    (lookup-equal lookup-equal-unguarded)
    (symbol< symbol<-unguarded)
    (symbol-name symbol-name-unguarded) ; primitive
    (symbol-package-name symbol-package-name-unguarded) ; primitive
    unsigned-byte-p
    unsigned-byte-p-forced
    fix
    ifix
    nfix
    (nth nth-unguarded)
    (mv-nth mv-nth-unguarded)
    (min min-unguarded)
    (max max-unguarded)
    (integer-length integer-length-unguarded)
    ;; (return-last return-last-unguarded) ;we don't want to execute this normally, because that would mean executing the eager-arg
    (width-of-widest-int width-of-widest-int-unguarded)

    ;; bv functions:

    (bvchop bvchop-unguarded)
    (getbit getbit-unguarded)
    (slice slice-unguarded)
    (bvcat bvcat-unguarded)
    (trim trim-unguarded)
    (bvsx bvsx-unguarded)
    (bvshl bvshl-unguarded)
    (bvshr bvshr-unguarded)
    (bvashr bvashr-unguarded)

    (bvplus bvplus-unguarded)
    (bvuminus bvuminus-unguarded)
    (bvminus bvminus-unguarded)
    (bvmult bvmult-unguarded)

    (bvmod bvmod-unguarded)
    (bvdiv bvdiv-unguarded)

    (bvand bvand-unguarded)
    (bvor bvor-unguarded)
    (bvxor bvxor-unguarded)
    (bvnot bvnot-unguarded)

    (bitand bitand-unguarded)
    (bitor bitor-unguarded)
    (bitxor bitxor-unguarded)
    (bitnot bitnot-unguarded)

    (leftrotate32 leftrotate32-unguarded)
    ;; todo; leftrotate
    ;; todo; rightrotate
    ;; todo; rightrotate32

    (bvlt bvlt-unguarded)
    (bvle bvle-unguarded)
    (sbvlt sbvlt-unguarded)

    ;; bv-array functions:

    (bv-array-read bv-array-read-unguarded)
    (bv-array-write bv-array-write-unguarded)))

;; Makes the evaluator:
(make-evaluator-simple basic *axe-evaluator-basic-fns-and-aliases*)
