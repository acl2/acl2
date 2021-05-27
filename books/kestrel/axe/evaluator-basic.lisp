; An simple evaluator supporting a basic set of functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A simple version of the Axe evaluator with verified guards and without skip-proofs.

(include-book "unguarded-primitives")
(include-book "unguarded-built-ins")
(include-book "unguarded-defuns")
(include-book "make-evaluator-simple")
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-write" :dir :system)
(include-book "kestrel/lists-light/repeat-tail" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; TODO: Add more functions!  Add more bv functions.
(defconst *axe-evaluator-basic-fns-and-aliases*
  '((car car-unguarded)
    (cdr cdr-unguarded)
    cons
    consp
    atom
    integerp
    rationalp
    acl2-numberp
    stringp
    symbolp
    characterp
    natp
    posp
    booleanp
    true-listp
    all-natp
    all-unsigned-byte-p
    (endp endp-unguarded)
    (take take-unguarded)
    (nthcdr nthcdr-unguarded)
    (reverse-list reverse-list-unguarded)
    repeat-tail
    (repeat repeat-unguarded)
    (binary-append binary-append-unguarded)
    (unary-- unary---unguarded)
    (expt expt-unguarded)
    (= =-unguarded)
    (unary-/ unary-/-unguarded)
    (binary-+ binary-+-unguarded)
    (binary-* binary-*-unguarded)
    (mod mod-unguarded)
    (floor floor-unguarded)
    (ceiling ceiling-unguarded)
    equal
    (< <-unguarded)
    (zp zp-unguarded)
    not
    len
    (assoc-equal assoc-equal-unguarded)
    (symbol-< symbol-<-unguarded)
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
;    (width-of-widest-int width-of-widest-int-unguarded)

    ;; bv functions:
    (trim trim-unguarded)
    (bvchop bvchop-unguarded)
    (bvplus bvplus-unguarded)
    (bvxor bvxor-unguarded)
    (leftrotate32 leftrotate32-unguarded)

    ;; bv-array functions:
    (bv-array-read bv-array-read-unguarded)
    (bv-array-write bv-array-write-unguarded)))

;; Make the evaluator:
(make-evaluator-simple axe-evaluator-basic *axe-evaluator-basic-fns-and-aliases*)
