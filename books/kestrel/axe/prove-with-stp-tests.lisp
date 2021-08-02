; Tests of prove-with-stp
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

; cert_param: (uses-stp)

(include-book "prove-with-stp" :ttags :all)
(include-book "kestrel/bv/bv-tests" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;If Axe ever tries to call STP and you don't have it, you may get an inscrutable error.

;TODO: Distinguish between STP failure to prove and a translation error

(must-prove-with-stp test1 '(equal (bvxor 32 x y) (bvxor 32 y x)))
(must-not-prove-with-stp test2 '(equal (bvxor 32 x y) (bvxor 32 x x)))
(defstub foo (x) t)
(must-prove-with-stp test3 '(equal (bvxor 32 (foo x) y) (bvxor 32 y (foo x)))) ;cuts out (foo x)
(must-not-prove-with-stp test4 '(equal (bvxor 32 (foo x) y) (bvxor 32 y (foo z))))
(must-not-prove-with-stp test5 'x)
(must-prove-with-stp test6 *t*)
(must-prove-with-stp test7 ''3) ;3 is non-nil
(must-prove-with-stp test7b '3) ;3 is non-nil
(must-not-prove-with-stp test8 *nil*)
(must-prove-with-stp test9 '(implies x x)) ;this now proves
(must-prove-with-stp test10 '(implies (and x (booleanp x)) x))
(must-prove-with-stp test11 '(implies (equal x y) (equal x y)))
(must-not-prove-with-stp test12 '(implies (equal y x) (equal x y))) ;no type for x and y
(must-not-prove-with-stp test12b '(equal x x)) ;no type for x; of course this will rewrite to t
(must-prove-with-stp test13 '(implies (and (equal y x) (unsigned-byte-p 8 x) (unsigned-byte-p 8 y)) (equal x y)))
(must-prove-with-stp test14 '(implies (and (equal y x) (unsigned-byte-p 8 x) (unsigned-byte-p 7 y)) (equal x y)))
(must-prove-with-stp test14b '(implies (and (equal y x) (unsigned-byte-p 8 x)) (equal x y)))
(must-prove-with-stp test15 '(implies (and (equal y x) (booleanp x) (booleanp y)) (equal x y)))
(must-prove-with-stp test15b '(implies (and (equal y x) (booleanp x)) (equal x y)))


(must-prove-with-stp test16 '(implies (and (equal y x) (booleanp x) (unsigned-byte-p 8 y)) (equal x y))) ;assumptions contradict
(must-not-prove-with-stp test17 '(implies (and (booleanp x) (unsigned-byte-p 8 y)) (equal x y))) ;i suppose the equal could be translated to false (now is replaced with a boolean var)

(must-not-prove-with-stp test18 '(implies (not (equal 1 x)) (equal (getbit 0 x) 0)))
(must-prove-with-stp test19 '(equal (bvmod 32 x 0) (bvchop ;$inline
                                                    32 x)))
(must-prove-with-stp test20 '(equal (bvmod 32 x 1) 0))
;(must-prove-with-stp test '(equal (bvmod 32 x 'x) 0)) ;;this was an error - note the quote on the x... fixme should we catch that?
(must-prove-with-stp test21 '(equal (bvmod 32 x x) 0))
(must-prove-with-stp test22 '(equal (bvdiv 32 x 0) 0))
(must-not-prove-with-stp test23 '(equal (bvdiv 32 x 1) 'x))
(must-prove-with-stp test24 '(equal (bvdiv 32 x 1) (bvchop ;$inline
                                                    32 x)))
;(must-prove-with-stp test '(equal (bvdiv 32 x x) 1)) ;think about this (not true for 0)
;(must-prove-with-stp test24b '(implies (not (equal 0 x)) (equal (bvdiv 32 x x) 1))) ;this was an error - forget to quote the 0
(must-not-prove-with-stp test24b '(implies (not (equal 0 x)) (equal (bvdiv 32 x x) 1))) ;false for x=t
(must-prove-with-stp test24c '(implies (not (equal 0 (bvchop ;$inline
                                                      32 x))) (equal (bvdiv 32 x x) 1))) ;fixme mentioned lgohead by mistake - could check that all fns are defined (and in logic mode)
(must-not-prove-with-stp test25 '(binary-+ x y)) ;fails, since binary-+ is not a boolean (fixme bit we know it's not nil. right?)
;(must-not-prove-with-stp test26 '(binary-+ 3 4)) ;fails, since binary-+ is not a boolean -- this now proves since the ground term is evaluated
(must-not-prove-with-stp test27 '(bvplus 32 x y)) ;fails, since bvplus is not a boolean

;relies on getting the type of x from its equality with 4:
(must-prove-with-stp test-equality-chain '(implies (equal 4 x) (equal 5 (bvplus 32 x 1))))
(must-prove-with-stp test-equality-chain2 '(implies (equal x (bvplus 4 y z)) (bvlt 32 x 16)))
(must-prove-with-stp test-equality-chain3 '(implies (equal (bvplus 32 x1 x2) (bvplus 4 y z)) (bvlt 32 (bvplus 32 x1 x2) 16)))

;here we write a 7 into the array at spot 15, but that spot is out of-bounds (the array length is 10)
;the behavior should be that the write has no effect and the read returns 0 (rather than the 7).
;previously, Axe would report this as valid, but that was wrong
(must-not-prove-with-stp array-out-of-bounds-test '(equal (bv-array-read 8 10 15 (bv-array-write 8 10 15 7 '(0 0 0 0 0 0 0 0 0 0))) 7))
(must-prove-with-stp array-padding-test '(equal (bv-array-read 8 10 0 (bv-array-write 5 10 0 7 '(0 0 0 0 0 0 0 0 0 0))) 7))
(must-not-prove-with-stp array-padding-test2 '(equal (bv-array-read 8 10 13 (bv-array-write 5 10 0 7 '(0 0 0 0 0 0 0 0 0 0))) 7))

;test of extensional arrays:
(must-prove-with-stp array-test-1 '(implies (and (true-listp x)
                                                 (true-listp y)
                                                 (equal 2 (len x))
                                                 (equal 2 (len y))
                                                 (all-unsigned-byte-p 32 x)
                                                 (all-unsigned-byte-p 32 y)
                                                 (equal (bv-array-read 32 2 0 x)
                                                        (bv-array-read 32 2 0 y))
                                                 (equal (bv-array-read 32 2 1 x)
                                                        (bv-array-read 32 2 1 y)))
                                            (equal x y)))

;; fails because it doesn't say that y is a true-list
(must-not-prove-with-stp array-test-2 '(implies (and (true-listp x)
                                                     (equal 2 (len x))
                                                     (equal 2 (len y))
                                                     (all-unsigned-byte-p 32 x)
                                                     (all-unsigned-byte-p 32 y)
                                                     (equal (bv-array-read 32 2 0 x)
                                                            (bv-array-read 32 2 0 y))
                                                     (equal (bv-array-read 32 2 1 x)
                                                            (bv-array-read 32 2 1 y)))
                                                (equal x y)))

;; Try to prove that reading element 5 of an array always gives 77 (which is of
;; course nonsense).  Interesting: The counterexample only assigns values to
;; the relevant array elements.
(must-not-prove-with-stp array-var-test
                         '(implies (and (true-listp x)
                                       (equal 10 (len x))
                                       (all-unsigned-byte-p 8 x))
                                  (equal (bv-array-read 8 10 5 x) ;read elem #5
                                         77)))

;fixme think about arrays with length 0 or 1
;; gives an error:
;; (must-not-prove-with-stp array-test-3 '(implies (and (true-listp x)
;;                                                      (true-listp y)
;;                                                      (equal 1 (len x))
;;                                                      (equal 1 (len y))
;;                                                      (all-unsigned-byte-p 32 x)
;;                                                      (all-unsigned-byte-p 32 y)
;;                                                      (equal (bv-array-read 32 2 0 x)
;;                                                             (bv-array-read 32 2 0 y)))
;;                                                 (equal x y)))

;; ;also gives an error:
;; (must-not-prove-with-stp array-test-4 '(implies (and (true-listp x) (true-listp y)
;;                                                      (equal 1 (len x))
;;                                                      (equal 1 (len y))
;;                                                      (all-unsigned-byte-p 32 x)
;;                                                      (all-unsigned-byte-p 32 y)
;;                                                      (equal (bv-array-read 32 1 0 x)
;;                                                             (bv-array-read 32 1 0 y)))
;;                                                 (equal x y)))

(must-not-prove-with-stp thesis-example1 '(boolor (equal 0 (len x)) (equal 1 (len x))))
(must-prove-with-stp thesis-example2 '(implies (unsigned-byte-p 1 (len x)) (boolor (equal 0 (len x)) (equal 1 (len x)))))

(must-prove-with-stp leftrotate-example '(implies (unsigned-byte-p 32 x) (equal (leftrotate32 0 x) x)))
(must-not-prove-with-stp leftrotate-example2 '(equal (leftrotate32 0 x) x)) ;x may not be a number
(must-prove-with-stp leftrotate-example3 '(equal (leftrotate32 1 x) (leftrotate32 33 x)))
(must-prove-with-stp leftrotate-example4 '(equal (leftrotate32 0 x) (leftrotate32 32 x)))
(must-prove-with-stp leftrotate-example5 '(implies (unsigned-byte-p 32 x) (equal x (leftrotate32 32 x))))

;; (prove-clause-with-stp '((not (not (equal (bvplus 32 x y) (bvplus 32 y x))))))



;; (equal (bvplus 32 0 0) 0)

(must-prove-with-stp test28 '(equal (sbvdiv 32 5 3) 1))
;; TODO: Add a rewriting pass to get tests like this working again?
;; (must-prove-with-stp test29 `(equal (sbvdiv 32 5 -3) ,(bvchop 32 -1)))
;; (must-prove-with-stp test30 `(equal (sbvdiv 32 -5 3) ,(bvchop 32 -1)))
;; (must-prove-with-stp test31 `(equal (sbvdiv 32 -5 -3) 1))
;; (must-prove-with-stp test32 `(equal (sbvdiv 32 -1 -1) 1))
(must-prove-with-stp test33 '(equal (sbvrem 32 5 3) 2))
;; (must-prove-with-stp test34 `(equal (sbvrem 32 5 -3) 2))
;; (must-prove-with-stp test35 `(equal (sbvrem 32 -5 3) ,(bvchop 32 -2)))
;; (must-prove-with-stp test36 `(equal (sbvrem 32 -5 -3) ,(bvchop 32 -2)))
;; (must-prove-with-stp test37 `(equal (sbvrem 32 -1 -1) 0))

;; Tests for division by 0 (these are enforced by special code in the
;; translation to STP):

(must-prove-with-stp bvdiv-by-0 '(equal (bvdiv 32 x 0) 0))
(must-not-prove-with-stp bvmod-by-0-false '(equal (bvmod 32 x 0) x)) ;not true when x is not a usb32
(must-prove-with-stp bvmod-by-0 '(equal (bvmod 32 x 0) (bvchop 32 x)))

(must-prove-with-stp sbvdiv-by-0 '(equal (sbvdiv 32 x 0) 0))
(must-not-prove-with-stp sbvrem-by-0-false '(equal (sbvrem 32 x 0) x)) ;not true when x is not a usb32
(must-prove-with-stp sbvrem-by-0 '(equal (sbvrem 32 x 0) (bvchop 32 x)))

;; Tests for division of x by x:

(must-not-prove-with-stp bvdiv-same-false '(equal (bvdiv 32 x x) 1)) ;false for x=0
(must-prove-with-stp bvdiv-same '(implies (not (equal 0 (bvchop 32 x))) (equal (bvdiv 32 x x) 1)))
(must-not-prove-with-stp sbvdiv-same-false '(equal (sbvdiv 32 x x) 1)) ;false for x=0
(must-prove-with-stp sbvdiv-same '(implies (not (equal 0 (bvchop 32 x))) (equal (sbvdiv 32 x x) 1)))

;; Tricky case for signed division
(must-prove-with-stp sbvdiv-tricky-case '(equal (sbvdiv 32 *min-sint-32* 4294967295) *min-sint-32*))
(must-prove-with-stp sbvrem-tricky-case '(equal (sbvrem 32 *min-sint-32* 4294967295) 0))

;; Relationship between div and mod:

;; This is slow for 32 bits, so we prove it for 8 bits:
(must-prove-with-stp div-and-mod-8 '(equal (bvplus 8 (bvmult 8 y (bvdiv 8 x y)) (bvmod 8 x y))
                                           (bvchop 8 x)))

;; This is slow for 32 bits, so we prove it for 8 bits:
(must-prove-with-stp signed-div-and-mod-8 '(equal (bvplus 8 (bvmult 8 y (sbvdiv 8 x y)) (sbvrem 8 x y))
                                                  (bvchop 8 x)))

;; tests with array size mismatches:

;todo: can we handle this somehow?
;; (must-prove-with-stp bad-array-length '(equal (bv-array-write 8 2 0 255 (bv-array-write 8 16 1 0 '(0 0)))
;;                                               (bv-array-write 8 2 1 0 '(0 0))))

;todo: can we handle this somehow?
;; (must-prove-with-stp bad-array-length2 '(equal (bv-array-write 8 2  0 255 '(0 0))
;;                                                (bv-array-write 8 16 0 255 '(0 0))))

;; bad array element width (8 vs 16)
(must-fail
 (must-prove-with-stp bad-array-width '(equal (bv-array-write 8 2 0 255 (bv-array-write 16 2 1 0 '(0 0)))
                                              (bv-array-write 8 2 1 0 '(0 0)))))

;;; tests for bv-array-if (TODO: add more):

;; ;;equality of constant array
;; (must-prove-with-stp constant-array1 '(equal (bv-array-write '8 '2 '0 '77 '(0 0))
;;                                              '(0 1)))

;; (must-prove-with-stp constant-array1 '(equal x
;;                                              '(0 1)))

;; ;todo
;; (must-prove-with-stp constant-array1 '(implies (and (equal (len x) '2) ;this is the issue (reorder the equality)
;;                                                     (all-unsigned-byte-p '8 x)
;;                                                     (true-listp x))
;;                                                (equal x
;;                                                       '(0 1))))


(must-not-prove-with-stp constant-array1 '(implies (and (equal '2 (len x))
                                                        (all-unsigned-byte-p '8 x)
                                                        (true-listp x))
                                                   (equal x
                                                          '(0 1))))

(must-prove-with-stp constant-array2 '(implies (and (equal 2 (len x))
                                                    (all-unsigned-byte-p 8 x)
                                                    (true-listp x)
                                                    (equal 0 (bv-array-read 8 2 0 x))
                                                    (equal 1 (bv-array-read 8 2 1 x))
                                                    )
                                               (equal x
                                                      '(0 1))))

;; here, the length equality is oriented the other way:
(must-prove-with-stp constant-array2-alt '(implies (and (equal (len x) 2)
                                                        (all-unsigned-byte-p 8 x)
                                                        (true-listp x)
                                                        (equal 0 (bv-array-read 8 2 0 x))
                                                        (equal 1 (bv-array-read 8 2 1 x))
                                                        )
                                                   (equal x
                                                          '(0 1))))

;; ;todo: no counterexample printed?
;; (must-not-prove-with-stp constant-array1 '(implies (bv-arrayp '8 '2 x)
;;                                                (equal x
;;                                                       '(0 1))))

;todo array length 1 may be a problem
;; (must-prove-with-stp constant-array1 '(implies (and (unsigned-byte-p '8 x))
;;                                                (equal (bv-array-write '8 '1 '0 x '(0))
;;                                                       ...)))

(must-prove-with-stp bv-array-if-test1
                     '(implies (unsigned-byte-p 1 x)
                               (equal (bv-array-read 8 2 0 (bv-array-if 8 2 (equal x 0) '(0 255) '(1 255)))
                                      x)))

(must-prove-with-stp bv-array-if-test2
                     '(implies (and (equal 4 (len x))
                                    (equal 4 (len y))
                                    (all-unsigned-byte-p 8 x)
                                    (all-unsigned-byte-p 8 y)
                                    (true-listp x)
                                    (true-listp y))
                               (equal (bv-array-read 8 4 0 (bv-array-if 8 4 test x y))
                                      (bvif 8 test
                                            (bv-array-read 8 4 0 x)
                                            (bv-array-read 8 4 0 y)))))

;; test for bv of size 0:

(must-fail
 (must-prove-with-stp width-0-test1
                      '(equal (bvchop 0 x) 0)))


;; tests of not:

(must-fail
 ;; may be false if x is not a boolean
 (must-prove-with-stp not-test1
                      '(equal (not (not x))
                              x)))

(must-prove-with-stp not-test2
                      '(equal (not (not (not x)))
                              (not x)))


(must-prove-with-stp sbvle-test
                     '(equal (sbvle 32 x y)
                             (not (sbvlt 32 y x))))

;; TODO: Make these into tests:
;; (prove-clause-with-stp (list *nil*) t nil t "/tmp/foo" state)
;; (prove-clause-with-stp (list *nil* *t*) t nil t "/tmp/foo" state)

;;TODO: Should this work?  The (+ x y) should be replaced by a boolean var
;;;(prove-with-stp '(or (+ x y) (not (+ x y))))

(must-prove-with-stp bool-test1 '(if var t (not var)))
(must-prove-with-stp bool-test2 '(if (not var) t var))

;todo:
;(must-prove-with-stp bool-test3 '(or x (not x)))

;; Not true, since x may be a non-boolean:
(must-not-prove-with-stp bool-test4 '(or (not x) (equal t x)))

;;todo: get this to work: (prove-with-stp '(if var t (equal x (bvif 32 var x y))))

;todo: (prove-clause-with-stp '((not (true-listp a)) (not (equal '5 (len a))) (not (all-unsigned-byte-p '8 a)) (equal x (bvif '32 (true-listp a) x y)))  t nil t "tmp/foo" state)

;; TODO: Get this to work?
;; This is true.  This question is whether the BV node should get cut out, given that it has a bad constant argument.
;;(must-prove-with-stp irrel-node '(equal 3 (bvif 8 test (bvif 8 test 3 :irrel) 3)))

;; the BVPLUS nodes are too narrow for the BVXOR parents, but padding is inserted automatically:
(must-prove-with-stp pad-test '(equal (bvxor 8 (bvplus 4 x y) z) (bvxor 8 (bvplus 4 y x) z)))

;bad boolean constant:
;(must-not-prove-with-stp testbad '(equal '0 (bvif '32 (boolor '7 '8) '0 '1)))

;; Type mismatch (x is used as a boolean in the BVIF and as a bv in the BVXOR):
(must-fail
 (must-prove-with-stp test1 '(equal (bvif 32 x y z) (bvxor 32 x w))))

;; ;; TODO: Why didn't this work?
;; (must-fail-with-hard-error
;;  (must-prove-with-stp test1 '(equal (bvif 32 x y z) (bvxor 32 x w))))
