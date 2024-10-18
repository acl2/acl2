; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "system-states")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-faults-and-quora
  :parents (operations)
  :short "Operations for
          numbers of tolerated faulty validators and of validator quora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the maximum number of faulty validators
     for which the system remains Byzantine-fault-tolerant.
     We also define the quorum number for validators.")
   (xdoc::p
    "Both of these numbers are derived from the total number of validators,
     which is known to each validator, and so those numbers are known as well.
     Indeed, they are used to define certain state transitions,
     which model the computations that validators perform."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-faulty-for-total ((total natp))
  :returns (max natp
                :hints (("Goal" :in-theory (enable natp zp))))
  :short "Maximum number of faulty validators, out of a total,
          for the protocol to be fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "The classic BFT condition for fault tolerance is that
     the number of faulty validators is (strictly) less than
     one third of the total number of validators:
     @($f < n/3$), using the common symbols
     @($f$) and @($n$) for the two numbers.
     This relation works for every positive @($n$),
     whether it is a multiple of 3 or not.
     Multiplying both sides by 3, we get @($3f < n$),
     and taking @($f$) as the maximum value that satisfies the inequality
     (as opposed to potentially smaller values than the maximum),
     we get to the sometimes stated condition @($n = 3f + 1$),
     although this condition is less general for @($n$),
     because it forces @($n$) to be one more than a multiple of 3.
     The other possibilities are @($n = 3f + 2$) and @($n = 3f + 3$).")
   (xdoc::p
    "The distinction between the maximum @($f$)
     and possibly smaller values of @($f$)
     is worth emphasizing,
     because recent BFT literature
     does not always state things clearly in this respect.
     The actual number of faulty validators
     is not something that (correct) validators know.
     In contrast, the total number @($n$) of validators is known,
     and thus the maximum @($f$) satisfying @($f < n/3$)
     can be calculated from @($n$).
     So when a validator needs to use @($f$) in some computation,
     it is the maximum such @($f$), calculable from @($n$),
     not the (unknowable to the validator) number of faulty validators.
     In the documentation of our model, for clarity,
     we use @($f$) for the actual number of faulty validators,
     and @($F$) for the maximum number of faulty validators.
     This ACL2 function returns @($F$).")
   (xdoc::p
    "We return @($F$), i.e. the maximum @($f$)
     that satisfies the relation for a given @($n$).
     We define the function to return 0 if @($n = 0$),
     although @($n = 0$) does not correspond to a practical situation.
     So consider the normal case @($n > 0$)
     (we could strengthen the guard of this function
     to require a positive integer as input).
     If @($n$) is a multiple of 3,
     @($F$) is one less than the integer @($n/3$);
     if @($n$) is not a multiple of 3,
     @($F$) is the floor of @($n/3$).
     We can put the two cases together by noting that
     the ceiling of an integer is the integer (i.e. a no-op)
     and that the floor of a non-integer is
     one less than the ceiling of the non-integer.
     So we define @($F$) as
     one less than the ceiling of @($n/3$),
     or equivalently as the floor of @($(n-1)/3$).")
   (xdoc::p
    "If @($n$) is 1 or 2 or 3, no failures are tolerated:
     @($F$), and hence @($f$), must be 0.
     The case @($n = 1$) is a degenerate one,
     but the protocol could probably still work in a degenerate way.
     The cases @($n = 2$) and @($n = 3$) could make sense,
     but since they tolerate no failures,
     they are not used in practice.
     If @($n$) is 4 or more, we can tolerate
     an increasing number of faulty validators,
     any number @($f \\leq F$),
     so that is usually the practical minimum for @($n$).")
   (xdoc::p
    "We prove below that the result of this function is less than @($n/3$)
     (assuming positive @($n$)),
     and that incrementing the result of this function by one
     does not satisfy the condition:
     that is, @($F$) is the maximum @($f$) satisfying @($f < n/3$).
     We also prove the equivalence of defining @($F$)
     via ceiling or floor, as mentioned above.")
   (xdoc::p
    "We also prove that @($n \\geq 3F + 1$)."))
  (if (zp total)
      0
    (1- (ceiling total 3)))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))
  ///

  (defret max-faulty-for-total-alt-def
    (equal (max-faulty-for-total n)
           (if (zp n)
               0
             (floor (1- n) 3))))
  (in-theory (disable max-faulty-for-total-alt-def))

  (theory-invariant (incompatible (:definition max-faulty-for-total)
                                  (:rewrite max-faulty-for-total-alt-def)))

  (defret max-faulty-for-total-upper-bound
    (< max (/ total 3))
    :hyp (not (zp total))
    :rule-classes :linear)
  (in-theory (disable max-faulty-for-total-upper-bound))

  (defret max-faulty-for-total-upper-bound-tight
    (>= (1+ max) (/ total 3))
    :hyp (natp total)
    :hints (("Goal" :in-theory (enable natp))))
  (in-theory (disable max-faulty-for-total-upper-bound-tight))

  (defruled total-lower-bound-wrt-max-faulty
    (implies (not (zp total))
             (>= total
                 (1+ (* 3 (max-faulty-for-total total)))))
    :rule-classes :linear)

  (assert-event (= (max-faulty-for-total 0) 0))
  (assert-event (= (max-faulty-for-total 1) 0))
  (assert-event (= (max-faulty-for-total 2) 0))
  (assert-event (= (max-faulty-for-total 3) 0))
  (assert-event (= (max-faulty-for-total 4) 1))
  (assert-event (= (max-faulty-for-total 5) 1))
  (assert-event (= (max-faulty-for-total 6) 1))
  (assert-event (= (max-faulty-for-total 7) 2))
  (assert-event (= (max-faulty-for-total 8) 2))
  (assert-event (= (max-faulty-for-total 9) 2))
  (assert-event (= (max-faulty-for-total 10) 3))
  (assert-event (= (max-faulty-for-total 11) 3))
  (assert-event (= (max-faulty-for-total 12) 3))
  (assert-event (= (max-faulty-for-total 13) 4))
  (assert-event (= (max-faulty-for-total 14) 4))
  (assert-event (= (max-faulty-for-total 15) 4))
  (assert-event (= (max-faulty-for-total 15) 4))
  (assert-event (= (max-faulty-for-total 16) 5))
  (assert-event (= (max-faulty-for-total 17) 5))
  (assert-event (= (max-faulty-for-total 18) 5))
  (assert-event (= (max-faulty-for-total 19) 6))
  (assert-event (= (max-faulty-for-total 20) 6))
  (assert-event (= (max-faulty-for-total 25) 8))
  (assert-event (= (max-faulty-for-total 100) 33)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-faulty ((systate system-statep))
  :returns (max natp)
  :short "Maximum number of faulty validators tolerated by the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @($F$): see the discussion in @(tsee max-faulty-for-total)."))
  (max-faulty-for-total (number-validators systate))
  :hooks (:fix)
  ///

  (defruled number-validators-lower-bound-wrt-max-faulty
    (implies (> (number-validators systate) 0)
             (>= (number-validators systate)
                 (1+ (* 3 (max-faulty systate)))))
    :rule-classes :linear
    :enable total-lower-bound-wrt-max-faulty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define quorum ((systate system-statep))
  :returns (quorum natp
                   :hints (("Goal" :in-theory (enable natp
                                                      max-faulty
                                                      max-faulty-for-total))))
  :short "Quorum number for the protocol."
  :long
  (xdoc::topstring
   (xdoc::p
    "The execution of the protocol (i.e. the transitions in our system)
     involves checking conditions that certain numbers reach quorum,
     which is defined as @($n - F$).
     This is equivalent to @($2F + 1$) only when @($n = 3F + 1$),
     as we also prove here;
     it is not when @($n = 3F + 2$) or @($n = 3F + 3$).")
   (xdoc::p
    "Some BFT literature is not always clear about
     the distinction between @($n - F$) and @($2F + 1$):
     for instance, both the Narwhal and the Bullshark papers
     use @($2F + 1$) in their description of the protocol,
     even though the description should be for all values of @($n$).
     Sometimes the BFT literature makes the @($n = 3F + 1$) assumption,
     but such assumption does not seem to appear (clearly or at all)
     in the aforementioned papers,
     and it seems indeed strange to use @($2F + 1$)
     in the description of what should be a general protocol,
     when using @($n - F$) would be much clearer and correct."))
  (- (number-validators systate)
     (max-faulty systate))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))
  :hooks (:fix)
  ///

  (defruled posp-of-quorum-when-there-are-validators
    (implies (not (set::emptyp (all-addresses systate)))
             (posp (quorum systate)))
    :rule-classes (:rewrite :type-prescription)
    :enable (posp
             max-faulty
             max-faulty-for-total
             number-validators))

  (defruled quorum-when-3f+1
    (implies (equal (number-validators systate)
                    (1+ (* 3 (max-faulty systate))))
             (equal (quorum systate)
                    (1+ (* 2 (max-faulty systate)))))))
