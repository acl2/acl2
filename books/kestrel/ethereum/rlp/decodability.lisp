; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "encoding")

(local (include-book "kestrel/utilities/lists/append-theorems" :dir :system))
(local (include-book "kestrel/utilities/lists/prefixp-theorems" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rlp-decodability
  :parents (rlp)
  :short "Proofs that RLP encodings can be decoded."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that the encoding functions for byte arrays, trees, and scalars
     are injective over the encodable byte arrays, trees, and scalars.
     This means that each valid encoding corresponds to exactly one entity,
     i.e. that encoding is reversible, i.e. that decoding is possible.
     If an encoding function were not injective over encodable entities,
     then two or more distinct entities would be encoded identically.")
   (xdoc::p
    "We also prove the stronger property
     that no valid encoding is a strict prefix of another valid encoding.
     This means that it is possible to unambiguously decode valid encodings
     even when these encodings are not well-delimited segments of bytes,
     but they are read from a stream of bytes (e.g. over a network connection).
     If some valid encoding were a strict prefix of another valid encoding,
     then after reading the former we would not know whether we are done
     or whether we should continue reading the longer encoding."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-encode-bytes-injectivity-proof
  :parents (rlp-decodability)
  :short "Injectivity of @(tsee rlp-encode-bytes),
          over the encodable byte arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove, as a preliminary lemma, that
     if two byte arrays are encodable
     (i.e. the error result of @(tsee rlp-encode-bytes) is @('nil') for both),
     and their encodings are the same
     (i.e. the bytes results of @(tsee rlp-encode-bytes) are identical),
     then the two byte arrays are identical.
     Then we use the lemma to prove the theorem in a form that
     omits the @(tsee byte-listp) hypotheses
     and weakens the equality to @(tsee byte-list-equiv)
     (i.e. equality of @(tsee byte-list-fix) applied to both).
     The theorem readily subsumes the lemma
     because of the fixing theorems for @(tsee byte-list),
     but attempting to prove the theorem directly
     (instead of via the lemma first) fails.")
   (xdoc::p
    "The lemma is proved automatically,
     by unfolding @(tsee rlp-encode-bytes)
     and letting ACL2 handle all the combinations of the encoding cases.
     Critically, the proof for
     the case in which both byte arrays are encoded with a big endian length
     uses the rule @('equal-of-appends-decompose')
     to reduce the equality of the two encodings
     to the equality of the parts of the encodings after the lengths
     (these parts are the byte arrays being encoded);
     the hypothesis of this rule,
     namely that the lengths of the two big endian lengths are the same,
     is relieved from the equality
     between the first byte of the two encodings."))

  (defruledl rlp-encode-bytes-injective-lemma
    (implies (and (byte-listp x)
                  (byte-listp y)
                  (not (mv-nth 0 (rlp-encode-bytes x)))
                  (not (mv-nth 0 (rlp-encode-bytes y))))
             (equal (equal (mv-nth 1 (rlp-encode-bytes x))
                           (mv-nth 1 (rlp-encode-bytes y)))
                    (equal x y)))
    :enable rlp-encode-bytes)

  (defrule rlp-encode-bytes-injective
    (implies (and (not (mv-nth 0 (rlp-encode-bytes x)))
                  (not (mv-nth 0 (rlp-encode-bytes y))))
             (equal (equal (mv-nth 1 (rlp-encode-bytes x))
                           (mv-nth 1 (rlp-encode-bytes y)))
                    (equal (byte-list-fix x)
                           (byte-list-fix y))))
    :use (:instance rlp-encode-bytes-injective-lemma
          (x (byte-list-fix x))
          (y (byte-list-fix y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-encode-trees-injectivity-proof
  :parents (rlp-decodability)
  :short "Injectivity of @(tsee rlp-encode-tree)
          and @(tsee rlp-encode-tree-list),
          over the encodable trees and lists thereof."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by induction.
     There are two theorems:
     one for @(tsee rlp-encode-tree)
     and one for @(tsee rlp-encode-tree-list).
     The theorems are formulated similarly to
     the one for @(tsee rlp-encode-bytes).")
   (xdoc::p
    "Since the theorems involve two variables (two trees or two lists of trees),
     we locally define mutually recursive functions @('tree') and @('tree-list')
     to obtain and use an induction scheme that applies to two variables;
     we use the flag theorem macro generated by this local @(tsee defines).")
   (xdoc::p
    "Attempting to induct according to the mutually recursive encoding functions
     only applies to one variable,
     leaving the other variable unchanged in the hypotheses and conclusions
     of the induction steps:
     then the same unchanged variable cannot suitably ``relate''
     to the different instances of the changing variable
     in the hypotheses and conclusions.
     Submitting the injectivity theorems
     via the flag theorem macro of the encoding functions,
     an examining the induction scheme printed by ACL2,
     should make the problem apparent.")
   (xdoc::p
    "The induction proof makes use of two helper lemmas.")
   (xdoc::p
    "The first helper lemma applies to the two cases in which
     @('x') is a leaf tree and @('y') is a leaf tree.
     Commenting out this helper lemma from the hints of the induction theorem
     shows the two corresponding subgoals,
     in which the hypothesis that @('x') or @('y') is a leaf tree
     causes @(tsee rlp-encode-tree) to expand on @('x') or @('y'),
     generating a call to @(tsee rlp-encode-bytes) on the subtrees.
     This motivates the formulation of the first helper lemma,
     whose variable @('xy') stands for @('x') or @('y')
     and whose variable @('yx') stands for @('y') or @('x'),
     i.e. the other variable whose @(tsee rlp-encode-tree) in the subgoal
     is not expanded.
     We use an expansion hint to expand that; an enable hint does not suffice.
     If @('yx') is also a leaf tree,
     @(tsee rlp-encode-tree) reduces to @(tsee rlp-encode-bytes) on the subtrees
     and the injectivity theorem of @(tsee rlp-encode-bytes) applies.
     Otherwise, the expansion starts with a byte that is at least 192 or 247,
     which is incompatible with
     the starting byte of @(tsee rlp-encode-bytes) on (the subtrees of) @('xy'):
     the linear rule @('car-of-rlp-encode-bytes-upper-bound-when-no-error')
     does not apply here,
     so we use a @(':use') hint with a suitable instantiation.")
   (xdoc::p
    "The second helper lemma applies to the case in which
     the lists of trees @('xs') and @('ys') are not empty.
     In this case, their encodings are the @(tsee append)s
     of the encodings of their @(tsee car)s and of their @(tsee cdr)s.
     Commenting out this helper lemma from the hints of the induction theorem
     shows a subgoal that involves these @(tsee append)s.
     To use the induction hypotheses,
     we need to decompose the equality of the @(tsee append)s
     into the equalities of their @(tsee car) and @(tsee cdr) encodings,
     via the rule @('equal-of-appends-decompose')
     that we also used to prove the injectivity of @(tsee rlp-encode-bytes).
     For this, we need to relieve the hypothesis of that rule
     that the lenghts of the encodings of the @(tsee car)s are equal:
     this is done by the lemma @('car-encodings-same-len').")
   (xdoc::p
    "The key to proving @('car-encodings-same-len')
     is the fact that the lengths of the encodings of the @(tsee car)s
     are completely determined by the first (few) bytes of the encodings,
     as expressed by the rule @('len-of-rlp-encode-tree-from-prefix'),
     which we therefore enable to prove @('car-encodings-same-len').
     This rule rewrites the two lengths to prove equal
     in terms of the first (few) bytes of the encodings
     of the @(tsee car)s of @('xs') and @('ys'):
     if we knew that those encodings were equal, we would be done.
     But we only know (see hypothesis in @('car-encodings-same-len'))
     that the @(tsee append)s of the encodings of the @(tsee car)s
     with something else (the encodings of the @(tsee cdr)s) are equal.
     Fortunately, the first (few) bytes of the encodings of the @(tsee car)s
     are also the first (few) bytes of the @(tsee append)s.
     So we use the rules
     @('expand-to-car-of-append') and @('expand-to-take-of-append')
     to express the first (few) bytes that describe the lengths
     in terms of the @(tsee append)s;
     note that these two rules have a strictly more complex right hand side,
     so they are generally undesirable,
     yet they are useful in this proof.
     We disable the rules
     @('acl2::car-of-append') and @('acl2::take-of-append'),
     which work ``against''
     @('expand-to-car-of-append') and @('expand-to-take-of-append'),
     to prevent the rewriter from looping.")
   (xdoc::p
    "The two helper lemmas are enabled
     in the proof by induction of the injectivity lemmas,
     along with the rule @('true-listp-when-byte-listp-rewrite'),
     which serves to prove another subgoal
     (visible by commenting out this rule in the hints),
     similar to the one proved via the second helper lemma,
     but simpler due to an extra hypothesis @('(equal (cdr xs) (cdr ys))').")
   (xdoc::p
    "Similarly to the injectivity theorem for @(tsee rlp-encode-bytes),
     the injectivity theorems
     for @(tsee rlp-encode-tree) and @(tsee rlp-encode-tree-list)
     omit the @(tsee rlp-treep) and @(tsee rlp-tree-listp) hypotheses
     and weaken the equality
     with @(tsee rlp-tree-fix) and @(tsee rlp-tree-list-fix).
     These theorems subsume the lemmas,
     but attempting to prove directly the theorems by induction fails."))

  (local
   (defines double-tree-induction
     :flag-local nil
     :verify-guards nil
     (define tree (x y)
       (if (or (rlp-tree-case x :leaf)
               (rlp-tree-case y :leaf))
           (cons x y)
         (tree-list (rlp-tree-branch->subtrees x)
                    (rlp-tree-branch->subtrees y)))
       :measure (rlp-tree-count x))
     (define tree-list (xs ys)
       (declare (xargs :measure (rlp-tree-list-count xs)))
       (if (or (atom xs) (atom ys))
           (cons xs ys)
         (cons (tree (car xs) (car ys))
               (tree-list (cdr xs) (cdr ys))))
       :measure (rlp-tree-list-count xs))))

  (defruledl helper-lemma-1
    (implies (and (rlp-treep xy)
                  (rlp-treep yx)
                  (rlp-tree-case xy :leaf)
                  (not (mv-nth 0 (rlp-encode-bytes (rlp-tree-leaf->bytes xy))))
                  (not (mv-nth 0 (rlp-encode-tree yx))))
             (equal
              (equal (mv-nth 1 (rlp-encode-bytes (rlp-tree-leaf->bytes xy)))
                     (mv-nth 1 (rlp-encode-tree yx)))
              (equal yx xy)))
    :expand (rlp-encode-tree yx)
    :use (:instance car-of-rlp-encode-bytes-upper-bound-when-no-error
          (bytes (rlp-tree-leaf->bytes xy)))
    :disable car-of-rlp-encode-bytes-upper-bound-when-no-error)

  (defruledl expand-to-car-of-append
    (implies (not (mv-nth 0 (rlp-encode-tree (car trees))))
             (equal (car (mv-nth 1 (rlp-encode-tree (car trees))))
                    (car (append
                          (mv-nth 1 (rlp-encode-tree (car trees)))
                          (mv-nth 1 (rlp-encode-tree-list (cdr trees))))))))

  (defruledl expand-to-take-of-append
    (implies (and (not (mv-nth 0 (rlp-encode-tree (car trees))))
                  (< lenlen
                     (len (mv-nth 1 (rlp-encode-tree (car trees))))))
             (equal (take lenlen
                          (cdr (mv-nth 1 (rlp-encode-tree (car trees)))))
                    (take lenlen
                          (cdr (append
                                (mv-nth 1 (rlp-encode-tree (car trees)))
                                (mv-nth 1 (rlp-encode-tree-list
                                           (cdr trees)))))))))

  (defruledl car-encodings-same-len
    (implies (and (not (mv-nth 0 (rlp-encode-tree (car xs))))
                  (not (mv-nth 0 (rlp-encode-tree (car ys))))
                  (equal (append (mv-nth 1 (rlp-encode-tree (car xs)))
                                 (mv-nth 1 (rlp-encode-tree-list (cdr xs))))
                         (append (mv-nth 1 (rlp-encode-tree (car ys)))
                                 (mv-nth 1 (rlp-encode-tree-list (cdr ys))))))
             (equal (len (mv-nth 1 (rlp-encode-tree (car xs))))
                    (len (mv-nth 1 (rlp-encode-tree (car ys))))))
    :enable (len-of-rlp-encode-tree-from-prefix
             expand-to-car-of-append
             expand-to-take-of-append)
    :disable (acl2::car-of-append acl2::take-of-append))

  (defruledl helper-lemma-2
    (implies (and (not (mv-nth 0 (rlp-encode-tree (car xs))))
                  (not (mv-nth 0 (rlp-encode-tree (car ys)))))
             (equal (equal (append (mv-nth 1 (rlp-encode-tree (car xs)))
                                   (mv-nth 1 (rlp-encode-tree-list (cdr xs))))
                           (append (mv-nth 1 (rlp-encode-tree (car ys)))
                                   (mv-nth 1 (rlp-encode-tree-list (cdr ys)))))
                    (and (equal (mv-nth 1 (rlp-encode-tree (car xs)))
                                (mv-nth 1 (rlp-encode-tree (car ys))))
                         (equal (mv-nth 1 (rlp-encode-tree-list (cdr xs)))
                                (mv-nth 1 (rlp-encode-tree-list (cdr ys)))))))
    :use car-encodings-same-len
    :enable acl2::true-listp-when-byte-listp-rewrite)

  (local
   (defthm-double-tree-induction-flag

     (defthm rlp-encode-tree-injective-lemma
       (implies (and (rlp-treep x)
                     (rlp-treep y)
                     (not (mv-nth 0 (rlp-encode-tree x)))
                     (not (mv-nth 0 (rlp-encode-tree y))))
                (equal (equal (mv-nth 1 (rlp-encode-tree x))
                              (mv-nth 1 (rlp-encode-tree y)))
                       (equal x y)))
       :flag tree)

     (defthm rlp-encode-tree-list-injective-lemma
       (implies (and (rlp-tree-listp xs)
                     (rlp-tree-listp ys)
                     (not (mv-nth 0 (rlp-encode-tree-list xs)))
                     (not (mv-nth 0 (rlp-encode-tree-list ys))))
                (equal (equal (mv-nth 1 (rlp-encode-tree-list xs))
                              (mv-nth 1 (rlp-encode-tree-list ys)))
                       (equal xs ys)))
       :flag tree-list)

     :hints (("Goal"
              :in-theory (enable rlp-encode-tree
                                 rlp-encode-tree-list
                                 helper-lemma-1
                                 helper-lemma-2
                                 acl2::true-listp-when-byte-listp-rewrite)))))

  (defrule rlp-encode-tree-injective
    (implies (and (not (mv-nth 0 (rlp-encode-tree x)))
                  (not (mv-nth 0 (rlp-encode-tree y))))
             (equal (equal (mv-nth 1 (rlp-encode-tree x))
                           (mv-nth 1 (rlp-encode-tree y)))
                    (equal (rlp-tree-fix x)
                           (rlp-tree-fix y))))
    :use (:instance rlp-encode-tree-injective-lemma
          (x (rlp-tree-fix x))
          (y (rlp-tree-fix y))))

  (defrule rlp-encode-tree-list-injective
    (implies (and (not (mv-nth 0 (rlp-encode-tree-list xs)))
                  (not (mv-nth 0 (rlp-encode-tree-list ys))))
             (equal (equal (mv-nth 1 (rlp-encode-tree-list xs))
                           (mv-nth 1 (rlp-encode-tree-list ys)))
                    (equal (rlp-tree-list-fix xs)
                           (rlp-tree-list-fix ys))))
    :use (:instance rlp-encode-tree-list-injective-lemma
          (xs (rlp-tree-list-fix xs))
          (ys (rlp-tree-list-fix ys)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-encode-scalar-injectivity-proof
  :parents (rlp-decodability)
  :short "Injectivity of @(tsee rlp-encode-scalar),
          over the encodable scalars."
  :long
  (xdoc::topstring-p
   "This is also formulated similarly to the other injectivity theorems.
    It readily follows from the injectivity of @(tsee rlp-encode-bytes).")

  (defrule rlp-encode-scalar-injective
    (implies (and (not (mv-nth 0 (rlp-encode-scalar x)))
                  (not (mv-nth 0 (rlp-encode-scalar y))))
             (equal (equal (mv-nth 1 (rlp-encode-scalar x))
                           (mv-nth 1 (rlp-encode-scalar y)))
                    (equal (nfix x)
                           (nfix y))))
    :enable rlp-encode-scalar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-encode-bytes-prefix-unambiguity-proof
  :parents (rlp-decodability)
  :short "Property that no valid RLP byte array encoding
          is a strict prefix of another one."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is expressed by saying that
     if a valid encoding is a prefix of another one,
     the two encodings must be equal.
     Thus, it is not possible for a valid encoding
     to be a strict prefix of another valid encoding.")
   (xdoc::p
    "We do a case split on whether the two encodings have the same length
     (in which case the prefix relationship implies equality),
     or not.
     In the latter case,
     we show that in fact the two encodings must have the same length
     (and therefore we get a contradiction),
     because the length of an encoding is determined
     by its first byte or few bytes:
     we thus enable the rule @('len-of-rlp-encode-bytes-from-prefix').
     We use suitable instances of
     @('acl2::same-car-when-prefixp-and-consp') and
     @('acl2::same-take-when-prefixp-and-longer')
     to establish that the first (few) bytes of the encodings are the same."))

  (defrule rlp-encode-bytes-unamb-prefix
    (implies (and (not (mv-nth 0 (rlp-encode-bytes x)))
                  (not (mv-nth 0 (rlp-encode-bytes y))))
             (equal (prefixp (mv-nth 1 (rlp-encode-bytes x))
                             (mv-nth 1 (rlp-encode-bytes y)))
                    (equal (mv-nth 1 (rlp-encode-bytes x))
                           (mv-nth 1 (rlp-encode-bytes y)))))
    :cases ((equal (len (mv-nth 1 (rlp-encode-bytes x)))
                   (len (mv-nth 1 (rlp-encode-bytes y)))))
    :enable (len-of-rlp-encode-bytes-from-prefix
             list-equiv
             acl2::true-listp-when-byte-listp-rewrite)
    :use ((:instance acl2::same-car-when-prefixp-and-consp
           (x (mv-nth 1 (rlp-encode-bytes x)))
           (y (mv-nth 1 (rlp-encode-bytes y))))
          (:instance acl2::same-take-when-prefixp-and-longer
           (x (cdr (mv-nth 1 (rlp-encode-bytes x))))
           (y (cdr (mv-nth 1 (rlp-encode-bytes y))))
           (n (+ -183 (car (mv-nth 1 (rlp-encode-bytes x)))))))
    :prep-lemmas
    ((defrule lemma
       (implies (and (integerp n)
                     (> (len encoding) n))
                (>= (len (cdr encoding)) n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-encode-tree-prefix-unambiguity-proof
  :parents (rlp-decodability)
  :short "Property that no valid RLP tree encoding
          is a strict prefix of another one."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is quite analogous to the proof for byte array encoding.")
   (xdoc::p
    "We cannot, and do not need to, prove a similar property
     for encodings of lists of trees,
     because a list of encoded trees could be extended with another one.
     However, when we decode a list of trees,
     we know the total length of their super-tree,
     because at the top level we always start by decoding a tree,
     never a list of trees."))

  (defrule rlp-encode-tree-umamb-prefix
    (implies (and (not (mv-nth 0 (rlp-encode-tree x)))
                  (not (mv-nth 0 (rlp-encode-tree y))))
             (equal (prefixp (mv-nth 1 (rlp-encode-tree x))
                             (mv-nth 1 (rlp-encode-tree y)))
                    (equal (mv-nth 1 (rlp-encode-tree x))
                           (mv-nth 1 (rlp-encode-tree y)))))
    :cases ((equal (len (mv-nth 1 (rlp-encode-tree x)))
                   (len (mv-nth 1 (rlp-encode-tree y)))))
    :enable (len-of-rlp-encode-tree-from-prefix
             list-equiv
             acl2::true-listp-when-byte-listp-rewrite)
    :use ((:instance acl2::same-car-when-prefixp-and-consp
           (x (mv-nth 1 (rlp-encode-tree x)))
           (y (mv-nth 1 (rlp-encode-tree y))))
          (:instance acl2::same-take-when-prefixp-and-longer
           (x (cdr (mv-nth 1 (rlp-encode-tree x))))
           (y (cdr (mv-nth 1 (rlp-encode-tree y))))
           (n (+ -183 (car (mv-nth 1 (rlp-encode-tree x))))))
          (:instance acl2::same-take-when-prefixp-and-longer
           (x (cdr (mv-nth 1 (rlp-encode-tree x))))
           (y (cdr (mv-nth 1 (rlp-encode-tree y))))
           (n (+ -247 (car (mv-nth 1 (rlp-encode-tree x)))))))
    :prep-lemmas
    ((defrule lemma
       (implies (and (integerp n)
                     (> (len encoding) n))
                (>= (len (cdr encoding)) n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-encode-scalar-prefix-unambiguity-proof
  :parents (rlp-decodability)
  :short "Property that no valid RLP scalar encoding
          is a strict prefix of another one."
  :long
  (xdoc::topstring
   (xdoc::p
    "This easily follows from the analogous property for byte arrays."))

  (defrule rlp-encode-scalar-unamb-prefix
    (implies (and (not (mv-nth 0 (rlp-encode-scalar x)))
                  (not (mv-nth 0 (rlp-encode-scalar y))))
             (equal (prefixp (mv-nth 1 (rlp-encode-scalar x))
                             (mv-nth 1 (rlp-encode-scalar y)))
                    (equal (mv-nth 1 (rlp-encode-scalar x))
                           (mv-nth 1 (rlp-encode-scalar y)))))
    :enable rlp-encode-scalar))
