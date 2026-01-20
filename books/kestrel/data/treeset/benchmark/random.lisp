; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "kestrel/utilities/shuffle-list" :dir :system)

(include-book "../set-defs")
(include-book "../in-defs")
(include-book "../cardinality-defs")
(include-book "../insert-defs")
(include-book "../to-oset-defs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some functions in this book do not terminate on all inputs.
;; Some function have insufficiently strong guards.
(program)

(make-event (er-progn (set-check-invariant-risk nil)
                      (value '(value-triple :success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define random-boolean
  ((prob rationalp) ;; prob = chance of t
   state)
  :guard (and (<= 0 prob)
              (<= prob 1))
  :returns (mv (bool booleanp)
               state)
  (b* (((when (= prob 0))
        (mv nil state))
       ((when (= prob 1))
        (mv t state))
       (numer (numerator prob))
       (denom (denominator prob))
       ((mv rand-val state)
        (random$ denom state)))
    (mv (< rand-val numer)
        state)))

(define random-u-fixnum
  (state)
  :returns (mv (word (unsigned-byte-p acl2::*fixnum-bits* word))
               state)
  (b* (((mv word state)
        (random$ (expt 2 acl2::*fixnum-bits*) state)))
    (mv word
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-shuffled-elements
  ((set setp)
   state)
  :returns (mv (list true-listp)
               state)
  (b* ((list (to-oset set)))
    (acl2::shuffle-list list state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-random-u-fixnum-set-acc
  ((count natp)
   (acc acl2-number-setp)
   state)
  :returns (mv (set acl2-number-setp)
               state)
  ;; Oh, this cardinality check is probably what is taking so long
  (b* (((when (int= count 0))
        (mv acc state))
       ((mv word state)
        (random-u-fixnum state)))
    (mk-random-u-fixnum-set-acc (- count 1)
                                (insert word acc :test =)
                                state)))

(define mk-random-u-fixnum-set
  ((cardinality natp)
   state)
  :returns (mv (set acl2-number-setp)
               state)
  (mk-random-u-fixnum-set-acc cardinality (empty) state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; MOVE down
(define mk-random-u-fixnum-oset
  ((cardinality natp)
   state)
  :returns (mv (oset set::setp)
               state)
  (b* (((mv set state)
        (mk-random-u-fixnum-set cardinality state)))
    (mv (to-oset set)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-u-fixnum-not-in
  ((set acl2-number-setp)
   state)
  :returns (mv (word (word (unsigned-byte-p acl2::*fixnum-bits* word)))
               state)
  (b* (((mv word state)
        (random-u-fixnum state)))
    (if (in word set :test =)
        (get-u-fixnum-not-in set state)
      (mv word
          state))))

(define get-u-fixnum-in
  ((shuffled nat-listp))
  :guard (consp shuffled)
  :returns (mv (word (word (unsigned-byte-p acl2::*fixnum-bits* word)))
               (shuffled$ nat-listp))
  (mv (first shuffled)
      (rest shuffled)))

(define mk-u-fixnum-list-in-prob-acc
  ((count natp)
   (prob rationalp)
   (set acl2-number-setp)
   (shuffled nat-listp)
   (acc nat-listp)
   state)
  :guard (and (<= count (- (cardinality set) (len acc)))
              (<= 0 prob)
              (<= prob 1))
  :returns (mv (list nat-listp)
               state)
  (b* (((when (int= count 0))
        (mv acc state))
       ((mv in state) (random-boolean prob state))
       ((mv word shuffled state)
        (if in
            (b* (((mv word shuffled) (get-u-fixnum-in shuffled)))
              (mv word shuffled state))
          (b* (((mv word state) (get-u-fixnum-not-in set state)))
            (mv word shuffled state)))))
    (mk-u-fixnum-list-in-prob-acc (- count 1)
                                  prob
                                  set
                                  shuffled
                                  (cons word acc)
                                  state)))

(define big-set-shuffle
  ((length integerp)
   (set setp)
   (set-cardinality natp)
   (acc true-listp)
   state)
  :returns (mv (shuffled true-listp)
               state)
  (b* (((when (<= length 0))
        (mv acc state))
       ((mv shuffled state)
        (set-shuffled-elements set state))
       (acc (revappend shuffled acc))
       (length (- length set-cardinality)))
    (big-set-shuffle length
                     set
                     set-cardinality
                     acc
                     state)))

(define mk-u-fixnum-list-in-prob
  ((length natp)
   (prob rationalp)
   (set acl2-number-setp)
   state)
  :guard (and (<= length (cardinality set))
              (<= 0 prob)
              (<= prob 1))
  :returns (mv (list nat-listp)
               state)
  (b* (((mv shuffled state)
        (big-set-shuffle length set (cardinality set) nil state)))
    (mk-u-fixnum-list-in-prob-acc length prob set shuffled nil state)))
