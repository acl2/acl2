; Poseidon Library
;
;    Copyright 2024 Provable Inc.
;
;    Licensed under the Apache License, Version 2.0 (the "License");
;    you may not use this file except in compliance with the License.
;    You may obtain a copy of the License at
;
;      http://www.apache.org/licenses/LICENSE-2.0
;
;    Unless required by applicable law or agreed to in writing, software
;    distributed under the License is distributed on an "AS IS" BASIS,
;    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;    See the License for the specific language governing permissions and
;    limitations under the License.

; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "POSEIDON")

(include-book "kestrel/number-theory/prime" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/utilities/lists/all-len-equal-p" :dir :system)
(include-book "projects/pfcs/pfield-lib-ext" :dir :system)
(include-book "std/typed-lists/nat-listp" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/std/basic/ifix" :dir :system))
(local (include-book "kestrel/std/basic/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/take" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod param
  :parents (poseidon)
  :short "Fixtype of Poseidon parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our definition of Poseidon is parameterized
     over the following aspects:")
   (xdoc::ul
    (xdoc::li
     "A prime number @($p$), which defines the prime field @($\\mathbb{F}_p$).")
    (xdoc::li
     "The rate @($r$), i.e. the number of the elements in the state vector
      against which inputs and outputs are absorbed or squeezed.
      This is a positive integer.")
    (xdoc::li
     "The capacity @($c$), i.e. the number of the elements in the state vector
      that participate in the permutations
      but against which inputs and output are not absorbed or squeezed.
      This is a positive integer.")
    (xdoc::li
     "The exponent @($\\alpha$) used in the S-boxes.
      This is normally taken from a small set of integers,
      all positive except for -1,
      also based on the prime @($p$).
      Mathematically, S-boxes can be defined with any integer @($\\alpha$),
      and thus we allow any integer.
      For negative integers, we map 0 to 0,
      as done for the choice of -1 described in the paper.")
    (xdoc::li
     "The number @($R_f$) of full rounds before and after the partial rounds,
      which is half of the total number of full rounds @($R_F$).
      This should be a positive integer,
      but mathematically we can define Poseidon even if this is 0
      (i.e. no full rounds),
      so we allow any natural number.")
    (xdoc::li
     "The number @($R_P$) of partial rounds.
      This should be a positive integer,
      but mathematically we can define Poseidon even if this is 0
      (i.e. no partial rounds),
      so we allow any natural number.")
    (xdoc::li
     "The constants to add to the state vector as part of the permutation.
      These are organized as a list of lists of field elements.
      Each element of the outer list corresponds to a round,
      so the length of the outer list is @($R_F + R_P$) (i.e. @($2 R_f + R_P$)).
      Each inner list has @($r + c$) elements,
      which matches the length of the state vector.")
    (xdoc::li
     "The MDS matrix, which is organized as a list of lists of field elements.
      (MDS stands for Maximum Distance Separable, but we do not describe here
      how the matrix is constructed.)
      This is a square matrix, so the length of the outer list is @($r + c$)
      and each inner list has also length @($r + c$).
      We can equivalently view this as a list of rows or columns;
      if rows, we must view the state as a column vector;
      if columns, we must the state as a row vector.
      The multiplication between the matrix and the vector
      gives the same result (viewed either as column or row vector).")
    (xdoc::li
     "The state is represented as a list in ACL2.
      The state has two parts, corresponding to the @($r$) and @($c$) elements.
      Looking at the ACL2 list, we could have
      either the former before the latter
      or the latter before the former:"
     (xdoc::@{}
      "+------------------+--------------+"
      "|    r elements    |  c elements  |"
      "+------------------+--------------+"
      ""
      "+--------------+------------------+"
      "|  c elements  |    r elements    |"
      "+--------------+------------------+")
     "So we include a boolean parameter that says whether, in the ACL2 list,
      the rate elements come before the capacity elements or vice versa.")
    (xdoc::li
     "Regardless of the choice described just above, there is another choice,
      namely the direction in which inputs or outputs
      are absorbed or squeezed against the @($r$) elements of the state,
      which also form an ACL2 list (sublist of the state vector).
      We can either absorb or squeeze them with ascending list indices,
      or with descending list indices.
      In other words, in the illustrations above,
      we either go rightward (if ascending) or leftward (if descending).
      So we introduce a parameter for this choice.")
    (xdoc::li
     "In a partial round, the S-box is applied only to one element of the state.
      The element is at one end of the state vector,
      but it could be either the first or the last element in the ACL2 list.
      So we introduce a parameter for this choice.
      Mathematically, we could generalize this to
      an arbitrary position within the state vector;
      we could even generalize full and partial rounds
      to sets of indices;
      however, at this time this generality seems unnecessary.")))
  ((prime prime)
   (rate pos)
   (capacity pos)
   (alpha int)
   (full-rounds-half nat)
   (partial-rounds nat)
   (constants :reqfix (if (and (fe-list-listp constants prime)
                               (all-len-equal-p constants (+ rate capacity))
                               (equal (len constants) (+ (* 2 full-rounds-half)
                                                         partial-rounds)))
                          constants
                        (repeat (+ (* 2 full-rounds-half) partial-rounds)
                                (repeat (+ rate capacity) 0))))
   (mds :reqfix (if (and (fe-list-listp mds prime)
                         (all-len-equal-p mds (+ rate capacity))
                         (equal (len mds) (+ rate capacity)))
                    mds
                  (repeat (+ rate capacity) (repeat (+ rate capacity) 0))))
   (rate-then-capacity-p bool)
   (ascending-p bool)
   (partial-first-p bool))
  :require (and (fe-list-listp constants prime)
                (all-len-equal-p constants (+ rate capacity))
                (equal (len constants) (+ (* 2 full-rounds-half)
                                          partial-rounds))
                (fe-list-listp mds prime)
                (all-len-equal-p mds (+ rate capacity))
                (equal (len mds) (+ rate capacity)))
  :pred paramp
  :prepwork
  ((local (in-theory (enable pfield::true-list-listp-when-fe-list-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param->capacity-then-rate-p ((param paramp))
  :returns (yes/no booleanp)
  :parents (poseidon)
  :short "Negation of the @(tsee param->rate-then-capacity-p) parameter."
  (not (param->rate-then-capacity-p param))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param->descending-p ((param paramp))
  :returns (yes/no booleanp)
  :parents (poseidon)
  :short "Negation of the @(tsee param->ascending-p) parameter."
  (not (param->ascending-p param))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param->partial-last-p ((param paramp))
  :returns (yes/no booleanp)
  :parents (poseidon)
  :short "Negation of the @(tsee param->partial-first-p) parameter."
  (not (param->partial-first-p param))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param->size ((param paramp))
  :returns (r+c posp)
  :parents (poseidon)
  :short "Size of the state vector, i.e. @($r + c$)."
  (+ (param->rate param)
     (param->capacity param))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param->rounds ((param paramp))
  :returns (rounds natp)
  :parents (poseidon)
  :short "Total number of rounds, i.e. @($2 R_f + R_P = R_F + R_P$)."
  (+ (param->full-rounds-half param)
     (param->partial-rounds param)
     (param->full-rounds-half param))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection param-additional-theorems
  :parents (poseidon)
  :short "Additional theorems about the parameters in @(tsee param)."

  (defrule posp-of-param->prime
    (posp (param->prime param)))

  (defrule all-len-equal-p-of-param->constants
    (all-len-equal-p (param->constants param)
                     (param->size param))
    :enable param->size)

  (defrule all-len-equal-p-of-param->mds
    (all-len-equal-p (param->mds param)
                     (param->size param))
    :enable param->size)

  (defrule len-of-param->constants
    (equal (len (param->constants param))
           (param->rounds param))
    :enable param->rounds)

  (defrule len-of-param->mds
    (equal (len (param->mds param))
           (param->size param))
    :enable param->size)

  (defrule param->rate-less-than-size
    (< (param->rate param)
       (param->size param))
    :rule-classes :linear
    :enable param->size)

  (defrule param->capacity-less-than-size
    (< (param->capacity param)
       (param->size param))
    :rule-classes :linear
    :enable param->size)

  (defrule param->size-equal-rate+capacity
    (equal (param->size param)
           (+ (param->rate param)
              (param->capacity param)))
    :rule-classes :linear
    :enable param->size))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-round-constants ((stat (fe-listp stat prime))
                             (constants (fe-listp constants prime))
                             (prime primep))
  :guard (equal (len constants) (len stat))
  :returns (new-stat (fe-listp new-stat prime)
                     :hyp (posp prime)
                     :name fe-listp-of-add-round-constants)
  :parents (poseidon)
  :short "Add round constants to the state vector."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the @($\\mathit{AddRoundConstants}$) function in the paper.")
   (xdoc::p
    "Besides the state, it needs the constants for the round,
     in number that matches the state vector.")
   (xdoc::p
    "This could be a more general ACL2 function
     to add two vectors of field elements."))
  (cond ((endp stat) nil)
        (t (cons (add (car stat) (car constants) prime)
                 (add-round-constants (cdr stat) (cdr constants) prime))))
  ///

  (defret len-of-add-round-constants
    (equal (len new-stat)
           (len stat))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pow-by-alpha ((elem (fep elem prime))
                      (alpha integerp)
                      (prime primep))
  :returns (new-elem (fep new-elem prime)
                     :hyp (primep prime)
                     :name fep-of-pow-by-alpha)
  :parents (poseidon)
  :short "Raise a field element to the @($\\alpha$) power."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the exponent is negative,
     we map 0 to 0 and
     we map non-zero elements to the inverses of their positive powers.
     Note that raising a non-zero field element to a power
     yields a non-zero element."))
  (if (< alpha 0)
      (if (= elem 0)
          0
        (inv (pow elem (- alpha) prime) prime))
    (pow elem alpha prime))
  :guard-hints (("Goal" :in-theory (enable pfield::pow-0-equiv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sub-words-full ((stat (fe-listp stat prime))
                        (alpha integerp)
                        (prime primep))
  :returns (new-stat (fe-listp new-stat prime)
                     :hyp (primep prime)
                     :name fe-listp-of-sub-wordsfull)
  :parents (poseidon)
  :short "Apply the full S-box substitution to the state vector."
  :long
  (xdoc::topstring
   (xdoc::p
    "We raise to the @($\\alpha$) power every element of the state vector."))
  (cond ((endp stat) nil)
        (t (cons (pow-by-alpha (car stat) alpha prime)
                 (sub-words-full (cdr stat) alpha prime))))
  ///

  (defret len-of-sub-words-full
    (equal (len new-stat)
           (len stat))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sub-words-partial ((stat (fe-listp stat prime))
                           (alpha integerp)
                           (partial-first-p booleanp)
                           (prime primep))
  :returns (new-stat (fe-listp new-stat prime)
                     :hyp (and (primep prime)
                               (fe-listp stat prime))
                     :name fe-listp-of-sub-words-partial)
  :parents (poseidon)
  :short "Apply the partial S-box substitution to the state vector."
  :long
  (xdoc::topstring
   (xdoc::p
    "We raise to the @($\\alpha$) power either the first or the last element
     of the state vector, depending on the @('partial-first-p') parameter.
     If the state vector is empty, we return the empty state vector;
     this does not happen in Poseidon because @($r + c > 0$),
     but in this function definition we do not need that requirement."))
  (if (consp stat)
      (if partial-first-p
          (cons (pow-by-alpha (car stat) alpha prime)
                (cdr stat))
        (append (butlast stat 1)
                (list (pow-by-alpha (car (last stat)) alpha prime))))
    nil)
  ///

  (defret len-of-sub-words-partial
    (equal (len new-stat)
           (len stat))
    :hints (("Goal" :in-theory (enable butlast fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sub-words ((stat (fe-listp stat prime))
                   (alpha integerp)
                   (partial-first-p booleanp)
                   (prime primep)
                   (full-p booleanp))
  :returns (new-stat (fe-listp new-stat prime)
                     :hyp (and (primep prime)
                               (fe-listp stat prime))
                     :name fe-listp-of-sub-words)
  :parents (poseidon)
  :short "Apply the S-box substitution to the state vector."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the @($\\mathit{SubWords}$) function in the paper.")
   (xdoc::p
    "The substitution is full or partial,
     depending on the @('full-p') parameter."))
  (if full-p
      (sub-words-full stat alpha prime)
    (sub-words-partial stat alpha partial-first-p prime))
  ///

  (defret len-of-sub-words
    (equal (len new-stat)
           (len stat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dot-product ((row (fe-listp row prime))
                     (stat (fe-listp stat prime))
                     (prime primep))
  :guard (equal (len stat) (len row))
  :returns (elem (fep elem prime)
                 :hyp (posp prime)
                 :name fep-of-dot-product)
  :parents (poseidon)
  :short "Dot product of a matrix row and the state vecor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This views the state as a column vector.
     However, as explained in @(tsee param),
     we could equivalently view the matrix row as a matrix column
     and the state as a row vector.")
   (xdoc::p
    "This could be a more general ACL2 function
     to perform the dot product of two vectors of field elements."))
  (cond ((endp row) 0)
        (t (add (mul (car row) (car stat) prime)
                (dot-product (cdr row) (cdr stat) prime)
                prime)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mix-layer ((rows (fe-list-listp rows prime))
                   (stat (fe-listp stat prime))
                   (prime primep))
  :guard (all-len-equal-p rows (len stat))
  :returns (elems (fe-listp elems prime)
                  :hyp (posp prime)
                  :name fe-listp-of-mix-layer)
  :parents (poseidon)
  :short "Multiply the MDS matrix and the state vector."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the @($\\mathit{MixLayer}$) function in the paper.")
   (xdoc::p
    "This views the matrix as a list of rows and the state as a column vector,
     but as explained in @(tsee param) and mentioned in @(tsee dot-product)
     we could equivalently view the matrix rows as matrix columns
     and the state as a row vector."))
  (cond ((endp rows) nil)
        (t (cons (dot-product (car rows) stat prime)
                 (mix-layer (cdr rows) stat prime))))
  :guard-hints
  (("Goal" :in-theory (enable pfield::true-list-listp-when-fe-list-listp)))
  ///

  (defret len-of-mix-layer
    (equal (len elems)
           (len rows))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define round ((stat (fe-listp stat prime))
               (constants (fe-listp constants prime))
               (alpha integerp)
               (partial-first-p booleanp)
               (mds (fe-list-listp mds prime))
               (prime primep)
               (full-p booleanp))
  :guard (and (equal (len constants) (len stat))
              (all-len-equal-p mds (len stat)))
  :returns (new-stat (fe-listp new-stat prime)
                     :hyp (primep prime)
                     :name fe-listp-of-round)
  :parents (poseidon)
  :short "Perform a round."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add the round constants,
     we apply the S-box substitution,
     and we multiply by the MDS matrix.
     The round may be full or partial,
     which affects only the S-box substitution."))
  (b* ((stat (add-round-constants stat constants prime))
       (stat (sub-words stat alpha partial-first-p prime full-p))
       (stat (mix-layer mds stat prime)))
    stat)
  :guard-hints
  (("Goal" :in-theory (enable pfield::true-list-listp-when-fe-list-listp)))
  ///

  (defret len-of-round
    (equal (len new-stat)
           (len stat))
    :hyp (equal (len mds) (len stat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full-rounds ((stat (fe-listp stat prime))
                     (constants (fe-list-listp constants prime))
                     (alpha integerp)
                     (partial-first-p booleanp)
                     (mds (fe-list-listp mds prime))
                     (prime primep))
  :guard (and (all-len-equal-p constants (len stat))
              (all-len-equal-p mds (len stat))
              (equal (len mds) (len stat)))
  :returns (new-stat (fe-listp new-stat prime)
                     :hyp (and (primep prime)
                               (fe-listp stat prime))
                     :name fe-listp-of-full-rounds)
  :parents (poseidon)
  :short "Perform a sequence of full rounds."
  :long
  (xdoc::topstring
   (xdoc::p
    "The number of full rounds in the sequence is determined by
     the length of the list of lists of constants passed as input."))
  (b* (((when (endp constants)) stat)
       (stat (round stat (car constants) alpha partial-first-p mds prime t)))
    (full-rounds stat (cdr constants) alpha partial-first-p mds prime))
  :guard-hints
  (("Goal" :in-theory (enable pfield::true-list-listp-when-fe-list-listp)))
  ///

  (defret len-of-full-rounds
    (equal (len new-stat)
           (len stat))
    :hyp (equal (len mds) (len stat))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define partial-rounds ((stat (fe-listp stat prime))
                        (constants (fe-list-listp constants prime))
                        (alpha integerp)
                        (partial-first-p booleanp)
                        (mds (fe-list-listp mds prime))
                        (prime primep))
  :guard (and (all-len-equal-p constants (len stat))
              (all-len-equal-p mds (len stat))
              (equal (len mds) (len stat)))
  :returns (new-stat (fe-listp new-stat prime)
                     :hyp (and (primep prime)
                               (fe-listp stat prime))
                     :name fe-listp-of-partial-rounds)
  :parents (poseidon)
  :short "Perform a sequence of partial rounds."
  :long
  (xdoc::topstring
   (xdoc::p
    "The number of full rounds in the sequence is determined by
     the length of the list of lists of constants passed as input."))
  (b* (((when (endp constants)) stat)
       (stat (round stat (car constants) alpha partial-first-p mds prime nil)))
    (partial-rounds stat (cdr constants) alpha partial-first-p mds prime))
  :guard-hints
  (("Goal" :in-theory (enable pfield::true-list-listp-when-fe-list-listp)))
  ///

  (defret len-of-partial-rounds
    (equal (len new-stat)
           (len stat))
    :hyp (equal (len mds) (len stat))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-rounds ((stat (fe-listp stat prime))
                    (constants (fe-list-listp constants prime))
                    (alpha integerp)
                    (partial-first-p booleanp)
                    (mds (fe-list-listp mds prime))
                    (full-rounds-half natp)
                    (partial-rounds natp)
                    (prime primep))
  :guard (and (all-len-equal-p constants (len stat))
              (equal (len constants) (+ (* 2 full-rounds-half) partial-rounds))
              (all-len-equal-p mds (len stat))
              (equal (len mds) (len stat)))
  :returns (new-stat (fe-listp new-stat prime)
                     :hyp (and (primep prime)
                               (fe-listp stat prime))
                     :name fe-listp-of-all-rounds)
  :parents (poseidon)
  :short "Perform all the rounds in a permutation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the number of initial and final full rounds @($R_f$)
     and the number of partial rounds @($R_P$),
     along with a list of lists of constants
     where the outer list has length @($2 R_f + R_P$)."))
  (b* ((full-rounds-first-constants (take full-rounds-half constants))
       (partial-rounds-constants (take partial-rounds
                                       (nthcdr full-rounds-half constants)))
       (full-rounds-last-constants (nthcdr (+ full-rounds-half
                                              partial-rounds)
                                           constants))
       (stat (full-rounds stat
                          full-rounds-first-constants
                          alpha
                          partial-first-p
                          mds
                          prime))
       (stat (partial-rounds stat
                             partial-rounds-constants
                             alpha
                             partial-first-p
                             mds
                             prime))
       (stat (full-rounds stat
                          full-rounds-last-constants
                          alpha
                          partial-first-p
                          mds
                          prime)))
    stat)
  :guard-hints
  (("Goal" :in-theory (enable pfield::true-list-listp-when-fe-list-listp
                              nfix)))
  ///

  (defret len-of-all-rounds
    (equal (len new-stat)
           (len stat))
    :hyp (equal (len mds) (len stat)))

  (defret nat-listp-of-all-rounds
    (nat-listp new-stat)
    :hyp (and (primep prime)
              (fe-listp stat prime))
    :hints (("Goal"
             :use fe-listp-of-all-rounds
             :in-theory (e/d (pfield::nat-listp-when-fe-listp)
                             (all-rounds fe-listp-of-all-rounds))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define permute ((stat (fe-listp stat (param->prime param)))
                 (param paramp))
  :guard (equal (len stat) (param->size param))
  :returns (new-stat (fe-listp new-stat (param->prime param))
                     :hyp (fe-listp stat (param->prime param)))
  :parents (poseidon)
  :short "Permutation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a wrapper of @(tsee all-rounds)
     that provides a more compact interface,
     consisting of a state vector and the parameters,
     whose components are passed to @(tsee all-rounds)."))
  (all-rounds stat
              (param->constants param)
              (param->alpha param)
              (param->partial-first-p param)
              (param->mds param)
              (param->full-rounds-half param)
              (param->partial-rounds param)
              (param->prime param))
  :guard-hints (("Goal" :in-theory (enable param->rounds)))

  ///

  (defret len-of-permute
    (equal (len new-stat)
           (len stat))
    :hyp (and (equal (len stat) (param->size param))
              (paramp param))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum mode
  :parents (poseidon)
  :short "Fixtype of sponge modes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sponge is either absorbing or squeezing."))
  (:absorb ())
  (:squeeze ())
  :pred modep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod sponge
  :parents (poseidon)
  :short "Fixtype of sponge states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of a state vector,
     an absorbing or squeezing mode,
     and an index.
     The index points to an element of the sublist of the state vector
     that consists of the @($r$) elements against which
     inputs are absorbed or outputs are squeezed:
     the index indicates the next element absorbed or squeezed.")
   (xdoc::p
    "Here we just say that the state vector is a list of natural numbers,
     because we do not have the prime that defines the prime field.
     Requirements on the state vector,
     and on the absorbing or squeezing index,
     are expressed in @(tsee sponge-validp),
     since they involve the parameters."))
  ((stat nat-list)
   (mode mode)
   (index nat))
  :pred spongep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sponge-validp ((sponge spongep) (param paramp))
  :returns (yes/no booleanp)
  :parents (poseidon)
  :short "Check if a sponge state is valid with respect to given parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state vector must consist of prime field elements,
     and must have length equal to @($r + c$).
     Furthermore, the index must not exceed @($r$).
     We allow the index to be @($r$),
     which happens just after we have absorbed or squeezed
     all of the @($r$) elements of the state vector.
     If one more element is absorbed and squeezed,
     a permutation is performed and the index is reset to 0
     (see @(tsee absorb1) and @(tsee squeeze1)),
     but in case there is no next element absorbed or squeezed,
     we avoid the permutation by letting the index be @($r$)."))
  (and (fe-listp (sponge->stat sponge) (param->prime param))
       (equal (len (sponge->stat sponge)) (param->size param))
       (<= (sponge->index sponge)
           (param->rate param)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-sponge ((size natp))
  :returns (sponge spongep)
  :parents (poseidon)
  :short "Initial sponge state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state vector consists of all zeros;
     we pass @($r+ c$) to determine the size.
     The mode is absorbing.
     The index is 0."))
  (make-sponge :stat (repeat size 0)
               :mode (mode-absorb)
               :index 0)
  ///

  (defrule sponge-validp-of-init-sponge
    (sponge-validp (init-sponge (param->size param)) param)
    :enable sponge-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define absorb1 ((input (fep input (param->prime param)))
                 (sponge spongep)
                 (param paramp))
  :guard (sponge-validp sponge param)
  :returns (new-sponge spongep)
  :parents (poseidon)
  :short "Absorb one element into the sponge."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the index is @($r$) or the mode is squeezing,
     we permute the state and reset the index to 0.")
   (xdoc::p
    "If the parameters say that indices are increasing in the list,
     the index of the sponge is also
     the index in the sublist of @($r$) elements.
     Otherwise, we flip the index.")
   (xdoc::p
    "Given the index in the sublist of @($r$) elements,
     we obtain the index in the stat list as follows.
     If the @($r$) elements come before the @($c$) elements,
     it is the same index.
     Otherwise, we add @($c$) to the index.")
   (xdoc::p
    "The resulting index is the one of
     the state element to be combined with the input.
     The combination is field addition,
     whose result replaces the element in the state.")
   (xdoc::p
    "We return an updated sponge state
     with the updated state vector,
     the next index,
     and the aborbing mode
     (unchanged if the sponge was already absorbing).
     Note that the index in the sponge state is always increasing,
     regardless of the parameter about
     the ascending or descending indices in the state vector list."))
  (b* (((sponge sponge) sponge)
       ((param param) param)
       ((mv stat index)
        (if (or (equal sponge.index param.rate)
                (mode-case sponge.mode :squeeze))
            (mv (permute sponge.stat param) 0)
          (mv sponge.stat sponge.index)))
       (list-index-in-rate (if param.ascending-p
                               index
                             (- (1- param.rate) index)))
       (list-index-in-stat (if param.rate-then-capacity-p
                               list-index-in-rate
                             (+ param.capacity list-index-in-rate)))
       (stat (update-nth list-index-in-stat
                         (add (nth list-index-in-stat stat)
                              input
                              param.prime)
                         stat)))
    (make-sponge :stat stat :mode (mode-absorb) :index (1+ index)))
  :guard-hints (("Goal" :in-theory (enable permute
                                           sponge-validp
                                           fix
                                           nfix)))
  ///

  (more-returns
   (new-sponge (sponge-validp new-sponge param)
               :hyp (sponge-validp sponge param)
               :name sponge-validp-of-absorb1
               :hints (("Goal" :in-theory (enable permute
                                                  sponge-validp
                                                  max
                                                  fix
                                                  nfix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define squeeze1 ((sponge spongep) (param paramp))
  :guard (sponge-validp sponge param)
  :returns (mv (output (fep output (param->prime param))
                       :hyp (sponge-validp sponge param)
                       :name fep-of-squeeze1.output
                       :hints (("Goal" :in-theory (enable permute
                                                          sponge-validp
                                                          nfix
                                                          fix))))
               (new-sponge spongep))
  :parents (poseidon)
  :short "Squeeze one element from the sponge."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is quite analogous to @(tsee absorb1)
     (see that function's documentation),
     with the roles of the modes swapped.
     The main difference is that the state vector is unchanged,
     and instead we return the element of the state pointed to by the index."))
  (b* (((sponge sponge) sponge)
       ((param param) param)
       ((mv stat index)
        (if (or (equal sponge.index param.rate)
                (mode-case sponge.mode :absorb))
            (mv (permute sponge.stat param) 0)
          (mv sponge.stat sponge.index)))
       (list-index-in-rate (if param.ascending-p
                               index
                             (- (1- param.rate) index)))
       (list-index-in-stat (if param.rate-then-capacity-p
                               list-index-in-rate
                             (+ param.capacity list-index-in-rate)))
       (output (nth list-index-in-stat stat)))
    (mv output
        (make-sponge :stat stat :mode (mode-squeeze) :index (1+ index))))
  :guard-hints (("Goal" :in-theory (enable permute
                                           sponge-validp
                                           fix)))
  ///

  (more-returns
   (new-sponge (sponge-validp new-sponge param)
               :hyp (sponge-validp sponge param)
               :name sponge-validp-of-squeeze1
               :hints (("Goal" :in-theory (enable permute
                                                  sponge-validp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define absorb ((inputs (fe-listp inputs (param->prime param)))
                (sponge spongep)
                (param paramp))
  :guard (sponge-validp sponge param)
  :returns (new-sponge spongep)
  :parents (poseidon)
  :short "Absorb any number of elements into the sponge."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee absorb1) on each input,
     threading the sponge state through the sequence."))
  (b* (((when (endp inputs)) (sponge-fix sponge))
       (sponge (absorb1 (car inputs) sponge param)))
    (absorb (cdr inputs) sponge param))
  ///

  (more-returns
   (new-sponge (sponge-validp new-sponge param)
               :hyp (sponge-validp sponge param)
               :name sponge-validp-of-absorb
               :hints (("Goal" :induct t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define squeeze ((count natp) (sponge spongep) (param paramp))
  :guard (sponge-validp sponge param)
  :returns (mv (outputs (fe-listp outputs (param->prime param))
                        :hyp (sponge-validp sponge param)
                        :name fe-listp-of-squeeze.outputs)
               (new-sponge spongep))
  :parents (poseidon)
  :short "Squeeze any number of elements into the sponge."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee squeeze1) for each output,
     whose count is passed to this ACL2 function,
     threading the sponge state through the sequence."))
  (b* (((when (zp count)) (mv nil (sponge-fix sponge)))
       ((mv output sponge) (squeeze1 sponge param))
       ((mv outputs sponge) (squeeze (1- count) sponge param)))
    (mv (cons output outputs) sponge))
  ///

  (more-returns
   (new-sponge (sponge-validp new-sponge param)
               :hyp (sponge-validp sponge param)
               :name sponge-validp-of-squeeze
               :hints (("Goal" :induct t))))

  (defret len-of-squeeze.outputs
    (equal (len outputs)
           (nfix count))
    :hints (("Goal" :induct t :in-theory (enable nfix fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hash ((inputs (fe-listp inputs (param->prime param)))
              (param paramp)
              (count natp))
  :returns (outputs (fe-listp outputs (param->prime param))
                    :name fe-listp-of-hash)
  :parents (poseidon)
  :short "Hash any number of inputs to any number of outputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We initialize the sponge,
     we absorb all the inputs,
     and we squeeze all the outputs.")
   (xdoc::p
    "Note that inputs that only differ in
     one input having more trailing zeros than the other
     and not exceeeding a multiple of the rate length
     result in the same outputs.
     For instance, if @($r$) is 10,
     the inputs @('(17)'), @'(17 0)'), @('(17 0 0)'), etc.
     (up to @('(17 0 0 0 0 0 0 0 0 0)') yield the same output,
     because the initial state vector consists of all zeros,
     and absorbing a 0 does not change the corresponding element.
     Therefore, the ACL2 function defined here
     should not be normally used as a collision-resistant hash;
     instead, a caller of this function should use padding,
     or other techniques like domain separation,
     to supply input strings that do not lead
     to the aforementioned collisions.
     The exact nature of these techniques is application-dependent;
     Poseidon itself does not appear to prescribe particular techniques."))
  (b* ((sponge (init-sponge (param->size param)))
       (sponge (absorb inputs sponge param))
       ((mv outputs &) (squeeze count sponge param)))
    outputs)
  ///

  (more-returns
    (outputs true-listp
             :rule-classes :type-prescription
             :hints (("Goal"
                      :use fe-listp-of-hash
                      :in-theory (disable fe-listp-of-hash)))))

  (defret len-of-hash
    (equal (len outputs)
           (nfix count)))

  (defret consp-of-hash
    (equal (consp outputs)
           (< 0 (nfix count)))
    :hints (("Goal"
             :use len-of-hash
             :in-theory (disable len-of-hash hash))))
  (in-theory (disable consp-of-hash)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hashp ((inputs (fe-listp inputs (param->prime param)))
               (param paramp)
               (count natp))
  :guard (and (<= (len inputs) (param->size param))
              (<= count (param->size param)))
  :returns (outputs (fe-listp outputs (param->prime param))
                    :name fe-listp-of-hashp
                    :hyp (and (paramp param)
                              (fe-listp inputs (param->prime param))
                              (<= (len inputs) (param->size param))
                              (<= count (param->size param)))
                    :hints (("Goal" :in-theory (enable nfix))))
  :parents (poseidon)
  :short "Hash according to just the Poseidon permutation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some applications do not use the Poseidon sponge,
     but instead just use the Poseidon permutation.
     That is, given @($r + c$) or fewer field elements,
     which fit into a Poseidon state vector,
     we can apply @(tsee permute),
     obtain an output state vector of @($r + c$) field elements,
     and select possibly all or a prefix of them.
     Since a single field element may consist of hundreds of bits,
     just a few field elements (even just one)
     may well suffice as inputs and outputs for certain applications.")
   (xdoc::p
    "This ACL2 function formalizes this hash based on just the permutation;
     the @('p') in the name of @('hashp') conveys that.
     The function has guards limiting the number of inputs and outputs.
     If there are fewer than @($r + c$) inputs,
     we pad them with zeros,
     in line with the full Poseidon sponge.
     Poseidon itself prescribes no padding,
     which is application-dependent,
     and can be applied prior to calling this ACL2 function;
     if exactly @($r + c$) field elements are passed to this function,
     this function does not add any padding zeros.")
   (xdoc::p
    "Since @(tsee permute) takes as input
     the full Poseidon parameters @(tsee param),
     this @('hashp') function also takes them as input.
     However, as in @(tsee permute), not all of the parameters are needed,
     namely the ones related to the sponge like @('ascending-p').
     Additionally, the permutation only depends on @(tsee param->size),
     not on the specifics of rate @($r$) and capacity @($c$) (just their sum).
     We may consider changing @(tsee permute) and this function
     to only take the necessary parameters at some point."))
  (b* ((stat (append inputs
                     (repeat (- (param->size param) (len inputs)) 0)))
       (new-stat (permute stat param)))
    (take count new-stat))
  :guard-hints (("Goal" :in-theory (enable natp)))

  ///

  (more-returns
   (outputs true-listp
            :rule-classes :type-prescription))

  (defret len-of-hashp
    (equal (len outputs)
           (nfix count))))
