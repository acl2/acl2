; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "top"))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An example of walking a @(see tmap) with a @(see cursor): summing the
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

;; Deleting a key which is there makes the map smaller. TMAP has no size
;; law for delete, so read it off the key set, where TSET has one.

(defrulel in-of-min-of-keys-when-not-emptyp
  (implies (not (emptyp map))
           (tset::in (tset::min (keys map)) (keys map)))
  :enable (tset::in-of-min
           emptyp-of-keys))

(defrulel size-of-delete-when-in-of-keys
  (implies (tset::in key (keys map))
           (< (size (delete key map))
              (size map)))
  :rule-classes :linear
  :enable (size$inline
           tset::cardinality-of-delete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The walk. It tests for an entry, and its guard says that any hole it is at
;; is the end, which a walk from @(tsee seek-min) with @(tsee next) maintains.

(define sum-loop
  ((cursor cursorp)
   (acc acl2-numberp))
  :guard (or (entryp cursor)
             (endp cursor))
  :returns (result acl2-numberp :rule-classes :type-prescription)
  :parents (sum)
  :short "Accumulate the entries from a @(see cursor) onward."
  :measure (nexts cursor)
  (if (not (entryp cursor))
      (acl2::fix acc)
    (sum-loop (next cursor)
              (+ (acl2::fix (entry-key cursor))
                 (acl2::fix (entry-val cursor))
                 acc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sum ((map mapp))
  :returns (result acl2-numberp :rule-classes :type-prescription)
  :parents (tmap)
  :short "The sum of the keys and values of a @(see tmap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Non-numeric keys and values contribute nothing.")
   (xdoc::p
     "Logically this repeatedly takes the least entry and deletes it, which is
      the form a proof wants. It executes as a single forward walk with a
      @(see cursor), at @($O(n)$) rather than @($O(n \\log(n))$)."))
  :measure (size map)
  ;; Keep `size' folded, so the linear rule above fires on the measure
  ;; conjecture rather than the goal dropping to the key set.
  :hints (("Goal" :in-theory (disable size$inline)
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
       :exec (sum-loop (seek-min map) 0)))

;;;;;;;;;;;;;;;;;;;;

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

;; The loop invariant. What the loop returns is what it has already
;; accumulated, plus the entry it is at, plus the sum of what is after it.
;;
;; The step case is where the two branches of the mbe meet: @(tsee
;; entry-key-of-next) says the key stepped onto is the least of what lay
;; ahead, and @(tsee after-of-next) says what lies ahead loses exactly that
;; entry. Those are the logical branch's @(tsee min-key) and @(tsee delete).

(defruled sum-loop-becomes-sum
  (equal (sum-loop cursor acc)
         (+ (acl2::fix acc)
            (if (entryp cursor)
                (+ (acl2::fix (entry-key cursor))
                   (acl2::fix (entry-val cursor))
                   (sum (after cursor)))
              0)))
  :induct (sum-loop cursor acc)
  :enable (sum-loop
           sum-when-emptyp
           acl2::fix
           default-+-1)
  :expand ((sum (after cursor))))

;;;;;;;;;;;;;;;;;;;;

;; The walk computes the sum. This is what the mbe obligation reduces to.

(defrule sum-loop-of-seek-min
  (equal (sum-loop (seek-min map) 0)
         (sum map))
  :enable (sum-when-emptyp
           sum-loop-becomes-sum)
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

