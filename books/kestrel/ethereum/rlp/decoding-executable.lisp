; Ethereum Library -- RLP Decoding Executable Definitions
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "decoding-declarative")

(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "kestrel/utilities/lists/append-theorems" :dir :system))
(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))
(local (include-book "kestrel/utilities/lists/nthcdr-theorems" :dir :system))
(local (include-book "kestrel/utilities/lists/primitive-theorems" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rlp-decoding-executable
  :parents (rlp)
  :short "Executable definitions of RLP decoding."
  :long
  (xdoc::topapp
   (xdoc::p
    "We provide executable definitions of RLP decoding for
     trees, byte arrays, and scalars.
     We prove the correctness of these executable definitions with respect to
     the <see topic='@(url rlp-decoding-declarative)'>declarative
     definitions</see>.")
   (xdoc::p
    "We start with an executable RLP parser for trees
     that accepts extra bytes after the encoding
     and that returns those extra bytes as additional result;
     this is a natural approach for this kind of recursive parsing.
     We prove that this parser is both left and right inverse,
     modulo the extra bytes,
     of the RLP tree encoder.")
   (xdoc::p
    "Then we define executable RLP decoders for trees, bytes, and scalars
     based on the parser.
     These decoders return an error
     if there are extra bytes after the encodings.
     We prove these decoders equal to the
     <see topic='@(url rlp-decoding-declarative)'>declaratively defined
     ones</see>,
     using the left and right inverse properties of the parser."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rlp-parse-tree
  :parents (rlp-decoding-executable)
  :short "Parse the RLP encoding of a tree,
          returning any extra bytes for further parsing."
  :long
  (xdoc::topapp
   (xdoc::p
    "This function returns a boolean error flag,
     the decoded tree,
     and the remaining unparsed bytes.
     If the error flag is set,
     we return an irrelevant tree as second result
     and @('nil') as remaining bytes.")
   (xdoc::p
    "This is fairly straightforward,
     but there is a slight subtlety missed by some implementations,
     including the reference decoding code in [Wiki:RLP]:
     in order to recognize only valid encodings
     (as formalized by @(tsee rlp-tree-encoding-p)),
     a decoder must reject encodings that use ``non-optimal'' lengths.
     For instance, the singleton byte array @('(10)')
     must be encoded as itself (@(tsee rlp-encode-bytes)),
     and not as @('(129 10)').
     Note that @(tsee rlp-bytes-encoding-p) does not hold on @('(129 10)'),
     because that sequence of bytes
     is not in the image of @(tsee rlp-bytes-tree).
     (This example talks about encoded byte arrays,
     but leaf trees are encoded in the same way.)")
   (xdoc::p
    "So our decoding code checks that
     (i) the form @('(129 x)') is not used with @('x') below 128,
     (ii) a big endian length has no leading zeros, and
     (iii) a big endian length is not below 56.
     Cases (ii) and (iii) apply to both leaf and non-leaf trees,
     while case (i) applies to leaf trees only.
     Without these extra checks, the decoder would accept
     not only all the valid encodings,
     but also some invalid encodings with non-optimal lengths.")
   (xdoc::p
    "Neither [YP:B] nor [Wiki:RLP] explicitly talk about this,
     but the fact that [YP:B] prescribes the encodings in all cases
     can be reasonably taken to exclude the encodings with non-optimal lengths.
     Furthermore, various GitHub issues for Ethereum implementations
     regard the acceptance of encodings with non-optimal lengths as bugs.
     Thus, we take the strict interpretation
     and regard such encodings as invalid.
     (Otherwise, formally, encoding would have to be a relation
     instead of a function.)")
   (xdoc::p
    "The function to parse single trees is mutually recursive with
     a function to parse lists of trees.
     The latter does not return the remaining bytes:
     it is always called with the exact byte sequence
     that is supposed to encode the trees of the list,
     one tree after the other.")
   (xdoc::p
    "The termination of these parsing function is proved
     via a lexicographic measure.
     The first component is the length of the input;
     the second component is an ordering on the two parsing functions
     where the one for trees is smaller than the one for lists of trees.
     This second component is needed because
     the function for lists of trees calls the one for trees
     on the same input (to parse the first tree in the list),
     and so the ordering on the function makes the overall measure smaller.
     When the function for trees calls the one for lists of trees,
     the input has been reduced in length by at least the first byte,
     and so it is immediate to prove that the overall measure decreases.
     When the function for lists of trees calls itself recursively,
     the input has also decreased,
     but this is a property of the function for trees,
     which cannot be proved until the function is admitted,
     i.e. shown to terminate.
     In other words, the termination here depends on functional properties.
     Thus, we use @(tsee mbt) to ensure that the length has in fact decreased,
     which lets us prove termination.
     Then guard verification ensures that that check is always satisfied.")
   (xdoc::p
    "Before verifying guards,
     we need to show that @(tsee rlp-parse-tree)
     returns fewer remaining bytes than the input bytes when there is no error.
     This is done by the linear rules.")
   (xdoc::p
    "If a sequence of bytes is successfully parsed,
     a sequence obtained by adding extra bytes at the end
     is also successfully parsed.
     The decoded tree is the same.
     The remaining bytes are extended with the extra bytes.
     This is all expressed by the theorem @('rlp-parse-tree-extend').
     This theorem plays a role in the left inverse proof below.")
   (xdoc::p
    "@(tsee rlp-parse-tree) is left inverse of @(tsee rlp-encode-tree),
     over the encodable trees.
     This implies that @(tsee rlp-parse-tree) accepts
     all valid encodings of trees.
     This is expressed by the theorem @('rlp-parse-tree-of-rlp-encode-tree'),
     which says that if @(tsee rlp-encode-tree) is successful,
     then parsing is successful,
     with no remaining bytes,
     and returns the starting bytes (modulo fixing).
     The proof is by induction on the encoding functions.
     It is not particularly difficult.
     It needs some @(':expand') hints
     for calls that ACL2's heuristics do not expand;
     note that there is an @(':expand') hint
     for each possible range of the first byte of the encoding,
     except for the range below 128.
     It also needs two instances of a theorems that relates
     the length of the big endian lengths to the lengths themselves;
     note that there are two instances,
     one for leaf trees (i.e. byte arrays encoded with long lengths)
     and one for non-leaf trees (i.e. subtrees encoded with long lengths).")
   (xdoc::p
    "@(tsee rlp-parse-tree) is right inverse of @(tsee rlp-encode-tree),
     over the valid byte array encodings.
     This implies that @(tsee rlp-parse-tree) accepts
     only valid encodings of tree:
     if it accepted an invalid encoding,
     this right inverse theorem would imply that
     @(tsee rlp-encode-tree) would map the result
     back to that invalid encoding,
     which would therefore be a valid encoding,
     contradicting the initial assumption.
     This right inverse theorem is @('rlp-encode-tree-of-rlp-parse-tree'),
     which says that if decoding is successful,
     then encoding is successful
     and the resulting encoding,
     concatenated with the reamining bytes from the decoding,
     is the initial input of the encoding (modulo fixing).
     The proof is by induction on the parsing functions.
     It is not particularly difficult.
     Similarly to the proof for left inverse,
     it uses two instances of the theorem that relates
     the length of the big endian lengths to the lengths themselves;
     the two instances correspond to leaf and non-leaf trees
     encoded with long lengths.")
   (xdoc::p
    "Without the extra checks for optimal lengths in the parser,
     the left inverse theorem would still be provable,
     but the right inverse theorem would not.")
   (xdoc::def "rlp-parse-tree")
   (xdoc::def "rlp-parse-tree-list"))
  :flag-local nil
  :verify-guards nil ; done below

  (define rlp-parse-tree ((encoding byte-listp))
    :returns (mv (error? booleanp)
                 (tree rlp-treep)
                 (rest byte-listp))
    (b* ((encoding (mbe :logic (byte-list-fix encoding) :exec encoding))
         (irrelevant (rlp-tree-leaf nil))
         ((when (endp encoding)) (mv t irrelevant nil))
         ((cons first encoding) encoding)
         ((when (< first 128)) (mv nil (rlp-tree-leaf (list first)) encoding))
         ((when (<= first 183))
          (b* ((len (- first 128))
               ((when (< (len encoding) len)) (mv t irrelevant nil))
               (bytes (take len encoding))
               ((when (and (= len 1)
                           (< (car bytes) 128))) (mv t irrelevant nil))
               (encoding (nthcdr len encoding)))
            (mv nil (rlp-tree-leaf bytes) encoding)))
         ((when (< first 192))
          (b* ((lenlen (- first 183))
               ((when (< (len encoding) lenlen)) (mv t irrelevant nil))
               (len-bytes (take lenlen encoding))
               ((unless (equal (trim-bendian* len-bytes)
                               len-bytes)) (mv t irrelevant nil))
               (encoding (nthcdr lenlen encoding))
               (len (bendian=>nat 256 len-bytes))
               ((when (<= len 55)) (mv t irrelevant nil))
               ((when (< (len encoding) len)) (mv t irrelevant nil))
               (bytes (take len encoding))
               (encoding (nthcdr len encoding)))
            (mv nil (rlp-tree-leaf bytes) encoding)))
         ((when (<= first 247))
          (b* ((len (- first 192))
               ((when (< (len encoding) len)) (mv t irrelevant nil))
               (subencoding (take len encoding))
               (encoding (nthcdr len encoding))
               ((mv error? subtrees) (rlp-parse-tree-list subencoding))
               ((when error?) (mv t irrelevant nil)))
            (mv nil (rlp-tree-nonleaf subtrees) encoding)))
         (lenlen (- first 247))
         ((when (< (len encoding) lenlen)) (mv t irrelevant nil))
         (len-bytes (take lenlen encoding))
         ((unless (equal (trim-bendian* len-bytes)
                         len-bytes)) (mv t irrelevant nil))
         (encoding (nthcdr lenlen encoding))
         (len (bendian=>nat 256 len-bytes))
         ((when (<= len 55)) (mv t irrelevant nil))
         ((when (< (len encoding) len)) (mv t irrelevant nil))
         (subencoding (take len encoding))
         (encoding (nthcdr len encoding))
         ((mv error? subtrees) (rlp-parse-tree-list subencoding))
         ((when error?) (mv t irrelevant nil)))
      (mv nil (rlp-tree-nonleaf subtrees) encoding))
    :measure (two-nats-measure (len encoding) 0)
    :no-function t)

  (define rlp-parse-tree-list ((encoding byte-listp))
    :returns (mv (error? booleanp)
                 (trees rlp-tree-listp))
    (b* (((when (endp encoding)) (mv nil nil))
         ((mv error? tree encoding1) (rlp-parse-tree encoding))
         ((when error?) (mv t nil))
         ((unless (mbt (< (len encoding1) (len encoding)))) (mv t nil))
         ((mv error? trees) (rlp-parse-tree-list encoding1))
         ((when error?) (mv t nil)))
      (mv nil (cons tree trees)))
    :measure (two-nats-measure (len encoding) 1)
    :no-function t)

  ///

  (defrule len-of-rlp-parse-tree
    (<= (len (mv-nth 2 (rlp-parse-tree encoding)))
        (len encoding))
    :rule-classes :linear
    :expand ((rlp-parse-tree encoding)))

  (defrule len-of-rlp-parse-tree-when-no-error
    (implies (not (mv-nth 0 (rlp-parse-tree encoding)))
             (< (len (mv-nth 2 (rlp-parse-tree encoding)))
                (len encoding)))
    :expand ((rlp-parse-tree encoding)))

  (verify-guards rlp-parse-tree
    :hints (("Goal"
             :in-theory
             (enable dab-digit-listp-of-256-is-byte-listp))))

  (fty::deffixequiv rlp-parse-tree
    :hints (("Goal"
             :in-theory (enable rlp-parse-tree
                                rlp-parse-tree-list)
             :expand ((rlp-parse-tree encoding)))))

  (defrule rlp-parse-tree-extend
    (implies (not (mv-nth 0 (rlp-parse-tree encoding)))
             (and (not (mv-nth 0 (rlp-parse-tree (append encoding more))))
                  (equal (mv-nth 1 (rlp-parse-tree (append encoding more)))
                         (mv-nth 1 (rlp-parse-tree encoding)))
                  (equal (mv-nth 2 (rlp-parse-tree (append encoding more)))
                         (append (mv-nth 2 (rlp-parse-tree encoding))
                                 (byte-list-fix more)))))
    :expand ((rlp-parse-tree encoding)
             (rlp-parse-tree (append encoding more))))

  (defthm-rlp-encode-tree-flag

    (defthm rlp-parse-tree-of-rlp-encode-tree
      (b* (((mv e-error? encoding) (rlp-encode-tree tree))
           ((mv d-error? tree1 rest) (rlp-parse-tree encoding)))
        (implies (not e-error?)
                 (and (not d-error?)
                      (not (consp rest))
                      (equal tree1 (rlp-tree-fix tree)))))
      :flag rlp-encode-tree)

    (defthm rlp-parse-tree-list-of-rlp-encode-tree-list
      (b* (((mv e-error? encoding) (rlp-encode-tree-list trees))
           ((mv d-error? trees1) (rlp-parse-tree-list encoding)))
        (implies (not e-error?)
                 (and (not d-error?)
                      (equal trees1 (rlp-tree-list-fix trees)))))
      :flag rlp-encode-tree-list)

    :hints (("Goal"
             :in-theory (enable rlp-encode-tree
                                rlp-encode-tree-list
                                rlp-encode-bytes
                                rlp-parse-tree
                                rlp-parse-tree-list
                                bytep
                                true-listp-when-byte-listp-rewrite)
             :expand ((:free (x y) (rlp-parse-tree (cons (+ 128 x) y)))
                      (:free (x y) (rlp-parse-tree (cons (+ 183 x) y)))
                      (:free (x y) (rlp-parse-tree (cons (+ 192 x) y)))
                      (:free (x y) (rlp-parse-tree (cons (+ 247 x) y)))))
            '(:use ((:instance acl2::len-of-nat=>bendian*-leq-width
                     (nat (len (rlp-tree-leaf->bytes tree)))
                     (base 256)
                     (width 8))
                    (:instance acl2::len-of-nat=>bendian*-leq-width
                     (nat (len (mv-nth 1 (rlp-encode-tree-list
                                          (rlp-tree-nonleaf->subtrees tree)))))
                     (base 256)
                     (width 8))))))

  (defthm-rlp-parse-tree-flag

    (defthm rlp-encode-tree-of-rlp-parse-tree
      (b* (((mv d-error? tree rest) (rlp-parse-tree encoding))
           ((mv e-error? encoding1) (rlp-encode-tree tree)))
        (implies (not d-error?)
                 (and (not e-error?)
                      (equal (append encoding1 rest)
                             (byte-list-fix encoding)))))
      :flag rlp-parse-tree)

    (defthm rlp-encode-tree-list-of-rl-decode-tree-list-exec
      (b* (((mv d-error? trees) (rlp-parse-tree-list encoding))
           ((mv e-error? encoding1) (rlp-encode-tree-list trees)))
        (implies (not d-error?)
                 (and (not e-error?)
                      (equal encoding1 (byte-list-fix encoding)))))
      :flag rlp-parse-tree-list)

    :hints ('(:use ((:instance acl2::len-of-nat=>bendian*-leq-width
                     (nat (bendian=>nat
                           256 (take (+ -183 (car (byte-list-fix encoding)))
                                     (cdr (byte-list-fix encoding)))))
                     (base 256)
                     (width 8))
                    (:instance acl2::len-of-nat=>bendian*-leq-width
                     (nat (bendian=>nat
                           256 (take (+ -247 (car (byte-list-fix encoding)))
                                     (cdr (byte-list-fix encoding)))))
                     (base 256)
                     (width 8))))
            ("Goal"
             :in-theory (e/d (rlp-encode-tree
                              rlp-encode-tree-list
                              rlp-encode-bytes
                              rlp-parse-tree
                              rlp-parse-tree-list
                              dab-digit-listp-of-256-is-byte-listp)
                             (acl2::nthcdr-of-nthcdr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decodex-tree ((encoding byte-listp))
  :returns (mv (error? booleanp)
               (tree rlp-treep))
  :parents (rlp-decoding-executable)
  :short "Executable RLP decoding of a tree."
  :long
  (xdoc::topapp
   (xdoc::p
    "We simply parse the tree
     and ensure that there are no remaining bytes.
     In case of error, we return an irrelevant tree as second result.")
   (xdoc::p
    "The @('x') in the name of this function stands for `executable',
     in contrast with the declaratively specified @(tsee rlp-decode-tree).")
   (xdoc::p
    "The left inverse theorem @('rlp-decodex-tree-of-rlp-encode-tree')
     readily follows from @('rlp-parse-tree-of-rlp-encode-tree').")
   (xdoc::p
    "The right inverse theorem @('rlp-encode-tree-of-rlp-decodex-tree')
     easily follows from @('rlp-encode-tree-of-rlp-parse-tree'),
     but the latter theorem involves @(tsee append)
     and so we use it with a @(':use') hint.")
   (xdoc::p
    "Using these left and right inverse theorems,
     we prove that the executable decoder is equal to @(tsee rlp-decode-tree),
     i.e. the executable decoder is correct.")
   (xdoc::p
    "Since @(tsee rlp-decode-tree) is defined
     as a case split on @(tsee rlp-tree-encoding-p),
     we first show that the latter is equivalent to
     @(tsee rlp-decodex-tree) not returning an error
     (not that this equivalence does not hold for @(tsee rlp-parse-tree),
     which accepts any extensions of the valid encodings).
     The `if' part is proved via the right inverse theorem,
     which says that the encoding is in the image of @(tsee rlp-encode-tree).
     The `only if' part is proved via the part of the left inverse theorem
     that says that if the encoding returns no error
     then decoding on the encoding returns no error
     (roughly speaking, @('encode /= error ==> decode o encode /= error')),
     with the argument instantiated to the @('rlp-tree-encoding-witness')
     (i.e.
     @('encode o witness /= error ==> decode o encode o witness /= error')).
     The @(tsee rlp-tree-enncoding-p) hypothesis establishes the antecedent,
     and the right inverse property of the witness reduces the consequent
     to just @('decode /= error').")
   (xdoc::p
    "With the above equivalence in hand,
     the equality of @(tsee rlp-decode-tree) and @(tsee rlp-decodex-tree)
     is proved by case splitting on @(tsee rlp-tree-encoding-p).
     If that predicate is false,
     both definitions immediately return the same result.
     Otherwise,
     the error results are the same because of the above equivalence,
     and the fact that the tree results are the same is proved
     from the injectivity of @(tsee rlp-encode-tree)
     and the fact that both @(tsee rlp-decode-tree) and @(tsee rlp-decodex-tree)
     are right inverses of @(tsee rlp-encode-tree)."))
  (b* (((mv error? tree rest) (rlp-parse-tree encoding))
       ((when error?) (mv t (rlp-tree-leaf nil)))
       ((when (consp rest)) (mv t (rlp-tree-leaf nil))))
    (mv nil tree))
  ///

  (fty::deffixequiv rlp-decodex-tree) ; needed by some proofs below

  (defrule rlp-decodex-tree-of-rlp-encode-tree
    (b* (((mv e-error? encoding) (rlp-encode-tree tree))
         ((mv d-error? tree1) (rlp-decodex-tree encoding)))
      (implies (not e-error?)
               (and (not d-error?)
                    (equal tree1
                           (rlp-tree-fix tree))))))

  (defrule rlp-encode-tree-of-rlp-decodex-tree
    (b* (((mv d-error? tree) (rlp-decodex-tree encoding))
         ((mv e-error? encoding1) (rlp-encode-tree tree)))
      (implies (not d-error?)
               (and (not e-error?)
                    (equal encoding1
                           (byte-list-fix encoding)))))
    :enable true-listp-when-byte-listp-rewrite
    :use rlp-encode-tree-of-rlp-parse-tree
    :disable rlp-encode-tree-of-rlp-parse-tree)

  (local (in-theory (disable rlp-decodex-tree)))

  (defruled rlp-tree-encoding-p-iff-rlp-decodex-tree-not-error
    (equal (rlp-tree-encoding-p encoding)
           (not (mv-nth 0 (rlp-decodex-tree encoding))))
    :use (if-part only-if-part)

    :prep-lemmas

    ((defruled if-part
       (implies (not (mv-nth 0 (rlp-decodex-tree encoding)))
                (rlp-tree-encoding-p encoding))
       :use ((:instance rlp-tree-encoding-p-suff
              (tree (mv-nth 1 (rlp-decodex-tree encoding))))))

     (defruled only-if-part
       (implies (rlp-tree-encoding-p encoding)
                (not (mv-nth 0 (rlp-decodex-tree encoding))))
       :use (:instance rlp-decodex-tree-of-rlp-encode-tree
             (tree (rlp-tree-encoding-witness encoding)))
       :disable rlp-decodex-tree-of-rlp-encode-tree)))

  (defruled rlp-decode-tree-is-rlp-decodex-tree
    (equal (rlp-decode-tree encoding)
           (rlp-decodex-tree encoding))
    :cases ((rlp-tree-encoding-p encoding))
    :enable (equal-when-encoding
             equal-when-not-encoding)

    :prep-lemmas

    ((defruled equal-when-not-encoding
       (implies (not (rlp-tree-encoding-p encoding))
                (equal (rlp-decode-tree encoding)
                       (rlp-decodex-tree encoding)))
       :enable (rlp-decode-tree
                rlp-decodex-tree)
       :use rlp-tree-encoding-p-iff-rlp-decodex-tree-not-error)

     (defruled equal-error-when-encoding
       (implies (rlp-tree-encoding-p encoding)
                (equal (mv-nth 0 (rlp-decode-tree encoding))
                       (mv-nth 0 (rlp-decodex-tree encoding))))
       :enable rlp-decode-tree
       :use rlp-tree-encoding-p-iff-rlp-decodex-tree-not-error)

     (defruled equal-tree-when-encoding
       (implies (rlp-tree-encoding-p encoding)
                (equal (mv-nth 1 (rlp-decode-tree encoding))
                       (mv-nth 1 (rlp-decodex-tree encoding))))
       :use (rlp-encode-tree-of-rlp-decode-tree
             rlp-encode-tree-of-rlp-decodex-tree
             rlp-tree-encoding-p-iff-rlp-decodex-tree-not-error)
       :disable (rlp-encode-tree-of-rlp-decode-tree
                 rlp-encode-tree-of-rlp-decodex-tree))

     (defruled equal-when-encoding
       (implies (rlp-tree-encoding-p encoding)
                (equal (rlp-decode-tree encoding)
                       (rlp-decodex-tree encoding)))
       :use (equal-error-when-encoding
             equal-tree-when-encoding)
       :enable (rlp-decode-tree rlp-decodex-tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decodex-bytes ((encoding byte-listp))
  :returns (mv (error? booleanp)
               (bytes byte-listp))
  :parents (rlp-decoding-executable)
  :short "Executable RLP decoding of a byte array."
  :long
  (xdoc::topapp
   (xdoc::p
    "This has the same form as the alternative definition rule
     of @(tsee rlp-decode-bytes) in terms of @(tsee rlp-decode-tree).
     As such, it is immediate to prove
     equal (i.e. correct with respect) to @(tsee rlp-decode-bytes),
     using the correctness theorem of @(tsee rlp-decodex-tree)."))
  (b* (((mv error? tree) (rlp-decodex-tree encoding))
       ((when error?) (mv t nil))
       ((unless (rlp-tree-case tree :leaf)) (mv t nil))
       (bytes (rlp-tree-leaf->bytes tree)))
    (mv nil bytes))
  :hooks (:fix)
  ///

  (defruled rlp-decode-bytes-is-rlp-decodex-bytes
    (equal (rlp-decode-bytes encoding)
           (rlp-decodex-bytes encoding))
    :enable (rlp-decode-bytes-alt-def
             rlp-decode-tree-is-rlp-decodex-tree)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decodex-scalar ((encoding byte-listp))
  :returns (mv (error? booleanp)
               (scalar natp))
  :parents (rlp-decoding-executable)
  :short "Executable RLP decoding of a scalar."
  :long
  (xdoc::topapp
   (xdoc::p
    "This has the same form as the alternative definition rule
     of @(tsee rlp-decode-scalar) in terms of @(tsee rlp-decode-bytes).
     As such, it is immediate to prove
     equal (i.e. correct with respect) to @(tsee rlp-decode-scalar),
     using the correctness theorem of @(tsee rlp-decodex-bytes)."))
  (b* (((mv error? bytes) (rlp-decodex-bytes encoding))
       ((when error?) (mv t 0))
       ((unless (equal (trim-bendian* bytes) bytes)) (mv t 0))
       (scalar (bendian=>nat 256 bytes)))
    (mv nil scalar))
  :guard-hints (("Goal"
                 :in-theory (enable dab-digit-listp-of-256-is-byte-listp)))
  :hooks (:fix)
  ///

  (defruled rlp-decode-scalar-is-rlp-decodex-scalar
    (equal (rlp-decode-scalar encoding)
           (rlp-decodex-scalar encoding))
    :enable (rlp-decode-scalar-alt-def
             rlp-decode-bytes-is-rlp-decodex-bytes)))
