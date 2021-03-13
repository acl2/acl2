; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book tests the add-io-pairs utility.

(in-package "ACL2")

; These are in the .acl2 file.
; (include-book "kestrel/crypto/primes/top" :dir :system)
; (include-book "kestrel/crypto/primes/baby-jubjub-subgroup-prime" :dir :system)

(include-book "add-io-pairs")
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simple examples from :doc add-io-pair
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f (x)
  (declare (xargs :guard t))
  (cons x x))

; Equivalent to (add-io-pairs (((f 3) '(3 . 3)))):
(add-io-pair (f 3) '(3 . 3) :debug t)

(assert-event (equal (f 3) '(3 . 3))) ; prints debug message

(assert-event (equal (f 4) '(4 . 4))) ; does not print debug message

(remove-io-pairs f)

(assert-event (equal (f 3) '(3 . 3))) ; no longer prints debug message

(defun g (x y)
  (declare (xargs :guard (and (natp x) (natp y))))
  (mv (non-exec (* 10 x)) (* 10 y)))

(add-io-pair (g 3 4) (mv 30 40))

; Succeeds because original g is bypassed
(assert-event (equal (mv-let (a b) (g 3 4) (list a b))
                     '(30 40)))

; Fails due to non-executability (no bypass for these args):
(must-fail (g 5 4)
           :expected :hard)

; Now let's add some more pairs, this time using terms that need to be
; evaluated rather than just constants.

(add-io-pairs (((g 3 6) (mv (* 3 10) (* 6 10)))
               ((g (/ 40 10) (/ 50 10)) (mv 40 50))))

; Something to try:
#||
ACL2 !>(show-io-pairs)

Verified I/O pairs ((fn arg1 .. argn) result):

((G '4 '5) (MV '40 '50))
((G '3 '6) (MV '30 '60))
((G '3 '4) (MV '30 '40))
((F '3) '(3 . 3))
ACL2 !>(get-io-pairs :all)
(((G 4 5) (MV 40 50))
 ((G 3 6) (MV 30 60))
 ((G 3 4) (MV 30 40)))
ACL2 !>
||#

; Still works:
(assert-event (equal (mv-let (a b) (g 3 4) (list a b))
                     '(30 40)))
; Also works:
(assert-event (equal (mv-let (a b) (g 3 6) (list a b))
                     '(30 60)))
; Also works:
(assert-event (equal (mv-let (a b) (g 4 5) (list a b))
                     '(40 50)))

; Something to try:
#||
ACL2 !>:u
          40:x(ADD-IO-PAIR (G 3 4) (MV 30 40))
ACL2 !>(assert-event (equal (mv-let (a b) (g 3 4) (list a b))
                     '(30 40)))
 :PASSED
ACL2 !>(g 3 6)


ACL2 Error in TOP-LEVEL:  ACL2 has been instructed to cause an error
because of an attempt to evaluate the following form (see :DOC non-
exec):

  (* 10 X).

To debug see :DOC print-gv, see :DOC trace, and see :DOC wet.

ACL2 !>
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; More complex example:
;;; using memoize directly
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section illustrates what is really going on when we teach ACL2 how to
; execute a function efficiently by using results from previously-proved
; theorems.

(defun primep-exec-1 (n)
  (declare (xargs :guard t))
  (if (member n '(#.primes::*secp256k1-field-prime*
                  #.primes::*baby-jubjub-subgroup-prime*
                  #.primes::*bn-254-group-prime*))
      t
    (rtl::primep n)))

(defthm primep-is-primep-exec-1
  (equal (rtl::primep n)
         (primep-exec-1 n))
  :rule-classes nil)

(memoize 'rtl::primep :invoke 'primep-exec-1)

(local (in-theory (disable
                   primes::primep-of-baby-jubjub-subgroup-prime-constant
                   primes::primep-of-bn-254-group-prime-constant
                   primes::primep-of-secp256k1-field-prime-constant)))

(thm (rtl::primep #.primes::*bn-254-group-prime*)
     :hints (("Goal" :in-theory '((:e rtl::primep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Continuing more complex example:
;;; this time, using add-io-pair
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Restore slow execution for now.

; Add io-pair for bn-254-group-prime.

(add-io-pair
 (rtl::primep (primes::bn-254-group-prime)) t
 :test eql
 :hints (("Goal"
          :in-theory
          (enable primes::primep-of-bn-254-group-prime-constant))))

(thm (rtl::primep (primes::bn-254-group-prime))
     :hints (("Goal" :in-theory '((:e rtl::primep)
                                  (:e primes::bn-254-group-prime)))))

; Add io-pair for each of the other two primes under consideration.

(add-io-pairs
 (((rtl::primep (primes::secp256k1-field-prime)) t)
  ((rtl::primep (primes::bn-254-group-prime)) t) ; already above; that's OK
  ((rtl::primep (primes::baby-jubjub-subgroup-prime)) t))
 :debug t
 :hints (("Goal"
          :in-theory
          (enable primes::primep-of-baby-jubjub-subgroup-prime-constant
                  primes::primep-of-bn-254-group-prime-constant
                  primes::primep-of-secp256k1-field-prime-constant))))

(thm (rtl::primep (primes::secp256k1-field-prime))
     :hints (("Goal" :in-theory '((:e rtl::primep)
                                  (:e primes::secp256k1-field-prime)))))

(thm (rtl::primep (primes::bn-254-group-prime))
     :hints (("Goal" :in-theory '((:e rtl::primep)
                                  (:e primes::bn-254-group-prime)))))

(thm (rtl::primep (primes::baby-jubjub-subgroup-prime))
     :hints (("Goal" :in-theory '((:e rtl::primep)
                                  (:e primes::baby-jubjub-subgroup-prime)))))

; Trivial, without debug printing since the original rtl::primep is run:
(thm (rtl::primep 7)
     :hints (("Goal" :in-theory '((:e rtl::primep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Using ec-call to sidestep guard verification
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun h (x)
  (declare (xargs :guard t))
  (ec-call (car x)))

(add-io-pairs (((h 3) nil) ((h '(a b c)) 'a)) :debug t)

(assert-event (equal (h 3) nil)) ; debug printing

(assert-event (equal (h '(a b c)) 'a)) ; debug printing

(assert-event (equal (h '(e f)) 'e)) ; no debug printing (lookup fails)

; Fails
; (assert-event (equal (h 7) nil))

(add-io-pair (h 7) nil)

(assert-event (equal (h 7) nil)) ; no debug printing since :debug was omitted

; Note that debug printing is based on the most recent add-io-pair(s) for the
; function.
(assert-event (equal (h '(a b c)) 'a)) ; still no debug printing

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Check that we can remove and then add with different debug
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(remove-io-pairs h)

; Here is the initial add-io-pairs call for h above, but without :debug.  This
; fails if the new function name is the same as before, which explains why the
; implementation uses the maximum absolute-event-number of the world.
(add-io-pairs (((h 3) nil) ((h '(a b c)) 'a)))

(assert-event (equal (h 3) nil))

; Fails, as it should:
(must-fail (equal (h 7) nil)
           :expected :hard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Check use of a list of tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-io-pairs (((g 2 5) (mv (* 2 10) (* 5 10)))
               ((g (/ 400 10) (/ 500 10)) (mv 400 500)))
              :test (eql equal))

; Test an I/O pair for g from earlier in this book:
(assert-event (equal (mv-let (a b) (g 3 4) (list a b))
                     '(30 40)))

(assert-event (equal (mv-let (a b) (g 2 5) (list a b))
                     '(20 50)))

; Fails guard verification because of eq:
; (add-io-pairs (((g 2 8) (mv (* 2 10) (* 8 10))))
;               :test (eql eq)
;               :verbose t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Including a book
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following include-book fails, as noted in the error message, because the
; existing I/O pairs for g at the point of failure are different at
; include-book time than they were at certify-book time.
(must-fail (include-book "add-io-pairs-tests-sub"))

; Readers should probably ignore this encapsulate.  The point of it is to
; illustrate the workings of merge-io-pairs in terms of lower-level macros
; push-io-pairs-lenience, install-io-pairs, and pop-io-pairs-lenience.  Most
; users should never have reason to think about those lower-level macros.
(encapsulate
  ()

  (local (push-io-pairs-lenience g))

  (local (include-book "add-io-pairs-tests-sub"))

; Succeeds because original g is bypassed:
  (local (assert-event (equal (mv-let (a b) (g 100 200) (list a b))
                              '(1000 2000))))

; Earlier success was defeated by new call of add-io-pair(s) in sub-book.
  (local (must-fail (equal (mv-let (a b) (g 3 4) (list a b))
                           '(30 40))
                    :expected :hard))

  (local (install-io-pairs g))

; The following pop-io-pairs-lenience is not necessary here since the earlier
; push-io-pairs-lenience in this encapsulate is local.  But we include it
; anyhow for illustrative purposes.
  (local (pop-io-pairs-lenience g))

; Succeeds because of add-io-pair in sub-book:
  (local (assert-event (equal (mv-let (a b) (g 100 200) (list a b))
                              '(1000 2000))))

; Still succeeds (original g is still bypassed) because of the "merge" done by
; the call of install-io-pairs, above:
  (local (assert-event (equal (mv-let (a b) (g 3 4) (list a b))
                              '(30 40))))
  )

; Still fails outside the encapsulate above just as it did before that
; encapsulate:
(must-fail (include-book "add-io-pairs-tests-sub"))

(merge-io-pairs g (include-book "add-io-pairs-tests-sub"))

; Succeeds because of add-io-pair in sub-book:
(assert-event (equal (mv-let (a b) (g 100 200) (list a b))
                     '(1000 2000)))

; Still succeeds (original g is still bypassed) because of the "merge" done
; above.
(assert-event (equal (mv-let (a b) (g 3 4) (list a b))
                     '(30 40)))

(add-io-pair (g 100 300) (mv 1000 3000))

; Still succeeds:
(assert-event (equal (mv-let (a b) (g 100 200) (list a b))
                     '(1000 2000)))
; Still succeeds:
(assert-event (equal (mv-let (a b) (g 3 4) (list a b))
                     '(30 40)))

(assert-event (equal (mv-let (a b) (g 100 300) (list a b))
                     '(1000 3000)))

(deinstall-io-pairs g)

(must-fail (equal (mv-let (a b) (g 3 4) (list a b))
                  '(30 40))
           :expected :hard)

(install-io-pairs g)

; These succeed again:
(assert-event (and (equal (mv-let (a b) (g 100 200) (list a b))
                          '(1000 2000))
                   (equal (mv-let (a b) (g 3 4) (list a b))
                          '(30 40))
                   (equal (mv-let (a b) (g 100 300) (list a b))
                          '(1000 3000))))

; The second pass of the encapsulate below causes a failure.
(must-fail
 (encapsulate
   ()
   (local (add-io-pair (g 100 400) (mv 1000 4000)))
   (add-io-pair (g 100 500) (mv 1000 5000))))

(must-fail (include-book "add-io-pairs-tests-sub-1"))
(must-fail (include-book "add-io-pairs-tests-sub-2"))

(merge-io-pairs
 (g g2) ; Note that g2 isn't yet defined, but that's OK.
 (include-book "add-io-pairs-tests-sub-1")
 (include-book "add-io-pairs-tests-sub-2"))
