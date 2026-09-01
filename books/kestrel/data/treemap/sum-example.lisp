; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "defs")

(local (include-book "top"))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An example of walking a @(see treemap) with an @(see iterator): summing the
;; keys and the values together. Both halves of each entry are read, so the
;; walk exercises @(tsee entry-key) and @(tsee entry-val) rather than just one
;; of them.
;;
;; The two sides are the two branches of one @(tsee mbe). The logical branch
;; recurses on @(tsee min-key) and @(tsee delete), which is what a proof about
;; @(tsee sum) gets to induct on; the executable branch walks the map once with
;; @(tsee next). Their equality is the @(tsee mbe) proof obligation, so it is
;; discharged by guard verification rather than stated as a separate theorem.
;;
;; That obligation mentions @(tsee sum), which does not exist until the
;; definition is admitted, so the definition defers it with @(':verify-guards
;; nil') and the @(tsee verify-guards) at the end of this book discharges it.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Deleting a key which is there makes the map smaller. TREEMAP has no size
;; law for delete, so read it off the key set, where TREESET has one.

(defrulel in-of-keys-of-min-key-when-not-emptyp
  (implies (not (emptyp map))
           (treeset::in (min-key map) (keys map)))
  :enable (min-key$inline
           treeset::in-of-min
           emptyp-of-keys))

(defrulel size-of-delete-when-in-of-keys
  (implies (treeset::in key (keys map))
           (< (size (delete key map))
              (size map)))
  :rule-classes :linear
  :enable (size$inline
           treeset::cardinality-of-delete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The walk. It runs forward, so it maintains @(tsee before-firstp) as false:
;; @(tsee iter-min) never lands there and neither does @(tsee next). Under that
;; invariant having an entry and not being at the end are the same condition,
;; which is what the @(tsee mbe) below records: the logical branch is the one
;; the measure wants, and the executable branch is the cheap test.

(define sum-loop
  ((iter iterp)
   (acc acl2-numberp))
  :guard (not (before-firstp iter))
  :returns (result acl2-numberp :rule-classes :type-prescription)
  :parents (sum)
  :short "Accumulate the entries from an @(see iterator) onward."
  :measure (nexts iter)
  (if (mbe :logic (not (has-valuep iter))
           :exec (after-lastp iter))
      (acl2::fix acc)
    (sum-loop (next iter)
              (+ (acl2::fix (entry-key iter))
                 (acl2::fix (entry-val iter))
                 acc))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t sum-loop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sum ((map mapp))
  :returns (result acl2-numberp :rule-classes :type-prescription)
  :parents (treemap)
  :short "The sum of the keys and values of a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Non-numeric keys and values contribute nothing.")
   (xdoc::p
     "Logically this repeatedly takes the least entry and deletes it, which is
      the form a proof wants. It executes as a single forward walk with an
      @(see iterator), at @($O(n)$) rather than @($O(n \\log(n))$)."))
  :measure (size map)
  ;; Keep `size' and `min-key' folded, so the linear rule above fires on the
  ;; measure conjecture rather than the goal dropping to the key set.
  :hints (("Goal" :in-theory (disable size$inline min-key$inline)
                  :use (:instance size-of-delete-when-in-of-keys
                                  (key (min-key map)))))
  ;; Deferred: the mbe obligation is the correctness of the walk, which is
  ;; stated in terms of sum itself. See the verify-guards at the end.
  :verify-guards nil
  (mbe :logic (if (emptyp map)
                  0
                (+ (acl2::fix (min-key map))
                   (acl2::fix (min-val map))
                   (sum (delete (min-key map) map))))
       :exec (sum-loop (iter-min map) 0)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t sum)))

(defruled sum-when-emptyp
  (implies (emptyp (double-rewrite map))
           (equal (sum map)
                  0))
  :enable sum)

(defrule sum-when-emptyp-cheap
  (implies (emptyp (double-rewrite map))
           (equal (sum map)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by sum-when-emptyp)

(defrule sum-of-empty
  (equal (sum (empty))
         0)
  :enable sum-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The map an iterator has yet to walk. Where the loop stops there is nothing
;; left, and that is exactly the position which has no entry and is not the
;; rewound end.

(defruled after-when-not-has-valuep-and-not-before-firstp
  (implies (and (not (has-valuep iter))
                (not (before-firstp iter)))
           (equal (after iter)
                  (empty)))
  :use has-valuep-when-neither-end
  :disable has-valuep-when-neither-end)

;; The library's @('after-of-iter-min') supplies the other connection a
;; walk's start needs: what a fresh iterator has left is everything but the
;; entry it is at.

;; The loop invariant. What the loop returns is what it has already
;; accumulated, plus the entry it is at, plus the sum of what is left.
;;
;; The step case is where the two branches of the mbe meet: @(tsee
;; entry-key-of-next) says the key stepped onto is the least of what lay
;; ahead, and @(tsee after-of-next-when-has-valuep) says what lies ahead loses
;; exactly that entry. Those are the logical branch's @(tsee min-key) and
;; @(tsee delete).

(defruled sum-loop-becomes-sum
  (implies (not (before-firstp iter))
           (equal (sum-loop iter acc)
                  (+ (acl2::fix acc)
                     (if (has-valuep iter)
                         (+ (acl2::fix (entry-key iter))
                            (acl2::fix (entry-val iter)))
                       0)
                     (sum (after iter)))))
  :induct (sum-loop iter acc)
  :enable (sum-loop
           sum-when-emptyp
           after-when-not-has-valuep-and-not-before-firstp)
  :expand ((sum (after iter))))

;;;;;;;;;;;;;;;;;;;;

;; The walk computes the sum. This is what the mbe obligation reduces to.

(defrule sum-loop-of-iter-min
  (equal (sum-loop (iter-min map) 0)
         (sum map))
  :enable (sum-when-emptyp
           sum-loop-becomes-sum
           ;; Over the empty map the expansion still deletes the (degenerate)
           ;; least key, which is not there to delete.
           delete-when-not-in-of-keys
           treeset::in-of-arg1-and-empty)
  :expand ((sum map)))

;;;;;;;;;;;;;;;;;;;;

(verify-guards sum
  :hints (("Goal" :expand ((sum map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
  (and (equal (sum (update 1 10 (update 2 20 (empty)))) 33)
       (equal (sum (empty)) 0)
       (equal (sum (update 'a 5 (update 3 "x" (empty)))) 8)
       (equal (sum (from-alist (list (cons 1 2) (cons 3 4)))) 10)))

