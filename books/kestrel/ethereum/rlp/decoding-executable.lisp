; Ethereum Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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
  (xdoc::topstring
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
     We prove these decoders equivalent to the
     <see topic='@(url rlp-decoding-declarative)'>declaratively defined
     ones</see>,
     using the left and right inverse properties of the parser.")
   (xdoc::p
    "While the declaratively defined decoders return a boolean error result,
     which therefore conveys a single kind of error,
     the executable parser and decoders return more detailed error information.
     Thus, the equivalence relation for the error result
     of the declaratively defined decoders and of the executable ones
     is @(tsee iff) instead of @(tsee equal); see the theorems."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum rlp-error
  :parents (rlp-decoding-executable)
  :short "Possible errors when parsing or decoding RLP encodings."
  :long
  (xdoc::topstring
   (xdoc::p
    "These values provide information about the reason why
     an RLP encoding is erroneous and cannot be parsed or decoded.")
   (xdoc::p
    "The @(':no-bytes') error occurs
     when starting to parse or decode a (sub)tree but no bytes are available.")
   (xdoc::p
    "The @(':fewer-bytes-than-...') errors occur when,
     after successfully reading a length,
     there are fewer bytes available than the required length.
     The length may be a short length (i.e. below 56, part of the first byte),
     the length of a long length (i.e. between 1 and 8, part of the first byte),
     or a long length (i.e. a big endian length).
     In these errors, the @('fragment') field consists of the first byte,
     possibly followed by the big endian length bytes as applicable.")
   (xdoc::p
    "The @(':leading-zeros-in-long-length') errors occurs when
     a long length has leading zeros.
     See the discussion in @(tsee rlp-parse-tree).
     The @('fragment') field consists of the first byte
     followed by the big endian length.")
   (xdoc::p
    "The @(':non-optimal-...') errors occur when
     the encoding is longer than it must be.
     See the discussion in @(tsee rlp-parse-tree).
     The @('fragment') field consists of the first byte,
     possibly followed by the big endian length bytes as applicable.")
   (xdoc::p
    "Since parsing and decoding are recursive,
     errors from subtree encodings must be propagated upward,
     because the supertree encodings are therefore erroneous.
     The @(':error-in-subtree') errors propagate and wrap
     the error from a subtree.
     Note that this makes the definition of this fixtype of errors recursive.")
   (xdoc::p
    "The @(':extra-bytes') errors occur only in decoding, not in parsing.
     Parsing always returns any remaining bytes as a result,
     while decoding requires the input bytes to have the right length.
     The @('bytes') field of these errors consists of the extra bytes.")
   (xdoc::p
    "The @(':branch-tree') errors occur
     when attempting to decode a byte array (i.e. a leaf tree)
     results in a branching tree instead.
     The @('fragment') field contains the starting byte of the encoding.")
   (xdoc::p
    "The @(':leading-zeros-in-scalar') errors occur
     when attempting to decode a scalar results in
     a byte array with leading zeros."))
  (:no-bytes ())
  (:fewer-bytes-than-short-length ((fragment byte-list)
                                   (required nat)
                                   (available nat)))
  (:fewer-bytes-than-length-of-length ((fragment byte-list)
                                       (required nat)
                                       (available nat)))
  (:fewer-bytes-than-long-length ((fragment byte-list)
                                  (required nat)
                                  (available nat)))
  (:leading-zeros-in-long-length ((fragment byte-list)))
  (:non-optimal-short-length ((fragment byte-list)))
  (:non-optimal-long-length ((fragment byte-list)))
  (:subtree ((error rlp-error)))
  (:extra-bytes ((bytes byte-list)))
  (:branch-tree ((fragment byte-list)))
  (:leading-zeros-in-scalar ((bytes byte-list))))

(fty::defoption maybe-rlp-error
  rlp-error
  :parents (rlp-decoding-executable)
  :short "Type of the error result of the parsing and decoding functions
          (@('nil') if no error).")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rlp-parse-tree
  :parents (rlp-decoding-executable)
  :short "Parse the RLP encoding of a tree,
          returning any extra bytes for further parsing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function returns an error result (@('nil') if no error),
     the decoded tree,
     and the remaining unparsed bytes.
     If the error is not @('nil'),
     we return an irrelevant tree as second result
     and @('nil') as remaining bytes.")
   (xdoc::p
    "This parser is fairly straightforward,
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
     is not in the image of @(tsee rlp-encode-bytes).
     (This example talks about encoded byte arrays,
     but leaf trees are encoded in the same way.)")
   (xdoc::p
    "So our decoding code checks that
     (i) the form @('(129 x)') is not used with @('x') below 128,
     (ii) a big endian length has no leading zeros, and
     (iii) a big endian length is not below 56.
     Cases (ii) and (iii) apply to both leaf and branching trees,
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
     Then guard verification ensures that that check is always satisfied.
     Under the negated @(tsee mbt) condition, we must return some error,
     but it does not matter which error, since this case never happens.")
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
     except for the range below 128.")
   (xdoc::p
    "@(tsee rlp-parse-tree) is right inverse of @(tsee rlp-encode-tree),
     over the valid tree encodings.
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
     It is not particularly difficult.")
   (xdoc::p
    "Without the extra checks for optimal lengths in the parser,
     the left inverse theorem would still be provable,
     but the right inverse theorem would not.")
   (xdoc::@def "rlp-parse-tree")
   (xdoc::@def "rlp-parse-tree-list"))
  :flag-local nil
  :verify-guards nil ; done below

  (define rlp-parse-tree ((encoding byte-listp))
    :returns (mv (error? maybe-rlp-error-p)
                 (tree rlp-treep)
                 (rest byte-listp))
    (b* ((encoding (byte-list-fix encoding))
         (irrelevant (rlp-tree-leaf nil))
         ((when (endp encoding)) (mv (rlp-error-no-bytes) irrelevant nil))
         ((cons first encoding) encoding)
         ((when (< first 128)) (mv nil (rlp-tree-leaf (list first)) encoding))
         ((when (<= first 183))
          (b* ((len (- first 128))
               ((when (< (len encoding) len))
                (mv (rlp-error-fewer-bytes-than-short-length (list first)
                                                             len
                                                             (len encoding))
                    irrelevant
                    nil))
               (bytes (take len encoding))
               ((when (and (= len 1)
                           (< (car bytes) 128)))
                (mv (rlp-error-non-optimal-short-length (list first
                                                              (car bytes)))
                    irrelevant
                    nil))
               (encoding (nthcdr len encoding)))
            (mv nil (rlp-tree-leaf bytes) encoding)))
         ((when (< first 192))
          (b* ((lenlen (- first 183))
               ((when (< (len encoding) lenlen))
                (mv (rlp-error-fewer-bytes-than-length-of-length (list first)
                                                                 lenlen
                                                                 (len encoding))
                    irrelevant
                    nil))
               (len-bytes (take lenlen encoding))
               ((unless (equal (trim-bendian* len-bytes)
                               len-bytes))
                (mv (rlp-error-leading-zeros-in-long-length (cons first
                                                                  len-bytes))
                    irrelevant
                    nil))
               (encoding (nthcdr lenlen encoding))
               (len (bebytes=>nat len-bytes))
               ((when (<= len 55))
                (mv (rlp-error-non-optimal-long-length (cons first len-bytes))
                    irrelevant
                    nil))
               ((when (< (len encoding) len))
                (mv (rlp-error-fewer-bytes-than-long-length (cons first
                                                                  len-bytes)
                                                            len
                                                            (len encoding))
                    irrelevant
                    nil))
               (bytes (take len encoding))
               (encoding (nthcdr len encoding)))
            (mv nil (rlp-tree-leaf bytes) encoding)))
         ((when (<= first 247))
          (b* ((len (- first 192))
               ((when (< (len encoding) len))
                (mv (rlp-error-fewer-bytes-than-short-length (list first)
                                                             len
                                                             (len encoding))
                    irrelevant
                    nil))
               (subencoding (take len encoding))
               (encoding (nthcdr len encoding))
               ((mv error? subtrees) (rlp-parse-tree-list subencoding))
               ((when error?) (mv (rlp-error-subtree error?) irrelevant nil)))
            (mv nil (rlp-tree-branch subtrees) encoding)))
         (lenlen (- first 247))
         ((when (< (len encoding) lenlen))
          (mv (rlp-error-fewer-bytes-than-length-of-length (list first)
                                                           lenlen
                                                           (len encoding))
              irrelevant
              nil))
         (len-bytes (take lenlen encoding))
         ((unless (equal (trim-bendian* len-bytes)
                         len-bytes))
          (mv (rlp-error-leading-zeros-in-long-length (cons first len-bytes))
              irrelevant
              nil))
         (encoding (nthcdr lenlen encoding))
         (len (bebytes=>nat len-bytes))
         ((when (<= len 55))
          (mv (rlp-error-non-optimal-long-length (cons first len-bytes))
              irrelevant
              nil))
         ((when (< (len encoding) len))
          (mv (rlp-error-fewer-bytes-than-long-length (cons first len-bytes)
                                                      len
                                                      (len encoding))
              irrelevant
              nil))
         (subencoding (take len encoding))
         (encoding (nthcdr len encoding))
         ((mv error? subtrees) (rlp-parse-tree-list subencoding))
         ((when error?)
          (mv (rlp-error-subtree error?) irrelevant nil)))
      (mv nil (rlp-tree-branch subtrees) encoding))
    :measure (two-nats-measure (len encoding) 0)
    :no-function t)

  (define rlp-parse-tree-list ((encoding byte-listp))
    :returns (mv (error? maybe-rlp-error-p)
                 (trees rlp-tree-listp))
    (b* (((when (endp encoding)) (mv nil nil))
         ((mv error? tree encoding1) (rlp-parse-tree encoding))
         ((when error?) (mv error? nil))
         ((unless (mbt (< (len encoding1) (len encoding))))
          (mv (rlp-error-no-bytes) nil))
         ((mv error? trees) (rlp-parse-tree-list encoding1))
         ((when error?) (mv error? nil)))
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

  (verify-guards rlp-parse-tree)

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
                                acl2::true-listp-when-byte-listp-rewrite
                                len-of-nat=>bebytes*-leq-8)
             :expand ((:free (x y) (rlp-parse-tree (cons (+ 128 x) y)))
                      (:free (x y) (rlp-parse-tree (cons (+ 183 x) y)))
                      (:free (x y) (rlp-parse-tree (cons (+ 192 x) y)))
                      (:free (x y) (rlp-parse-tree (cons (+ 247 x) y)))))))

  (defthm-rlp-parse-tree-flag

    (defthm rlp-encode-tree-of-rlp-parse-tree
      (b* (((mv d-error? tree rest) (rlp-parse-tree encoding))
           ((mv e-error? encoding1) (rlp-encode-tree tree)))
        (implies (not d-error?)
                 (and (not e-error?)
                      (equal (append encoding1 rest)
                             (byte-list-fix encoding)))))
      :flag rlp-parse-tree)

    (defthm rlp-encode-tree-list-of-rlp-parse-tree-list
      (b* (((mv d-error? trees) (rlp-parse-tree-list encoding))
           ((mv e-error? encoding1) (rlp-encode-tree-list trees)))
        (implies (not d-error?)
                 (and (not e-error?)
                      (equal encoding1 (byte-list-fix encoding)))))
      :flag rlp-parse-tree-list)

    :hints (("Goal"
             :in-theory (e/d (rlp-encode-tree
                              rlp-encode-tree-list
                              rlp-encode-bytes
                              rlp-parse-tree
                              rlp-parse-tree-list
                              bebytes->nat-lt-2^64)
                             (acl2::nthcdr-of-nthcdr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decodex-tree ((encoding byte-listp))
  :returns (mv (error? maybe-rlp-error-p)
               (tree rlp-treep))
  :parents (rlp-decoding-executable)
  :short "Executable RLP decoding of a tree."
  :long
  (xdoc::topstring
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
     we prove that the executable decoder
     is equivalent to @(tsee rlp-decode-tree),
     i.e. the executable decoder is correct.
     The equivalence is @(tsee iff) for the error result,
     because the executable decoder returns various kinds of errors,
     while the declaratively defined decoder returns just one kind.")
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
     The @(tsee rlp-tree-encoding-p) hypothesis establishes the antecedent,
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
       ((when error?) (mv error? (rlp-tree-leaf nil)))
       ((when (consp rest))
        (mv (rlp-error-extra-bytes rest) (rlp-tree-leaf nil))))
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
    :enable acl2::true-listp-when-byte-listp-rewrite
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
    (and (iff (mv-nth 0 (rlp-decode-tree encoding))
              (mv-nth 0 (rlp-decodex-tree encoding)))
         (equal (mv-nth 1 (rlp-decode-tree encoding))
                (mv-nth 1 (rlp-decodex-tree encoding))))
    :cases ((rlp-tree-encoding-p encoding))
    :enable (equivalent-when-not-encoding
             equivalent-error-when-encoding
             equivalent-tree-when-encoding)

    :prep-lemmas

    ((defruled equivalent-when-not-encoding
       (implies (not (rlp-tree-encoding-p encoding))
                (and (iff (mv-nth 0 (rlp-decode-tree encoding))
                          (mv-nth 0 (rlp-decodex-tree encoding)))
                     (equal (mv-nth 1 (rlp-decode-tree encoding))
                            (mv-nth 1 (rlp-decodex-tree encoding)))))
       :enable (rlp-decode-tree
                rlp-decodex-tree)
       :use rlp-tree-encoding-p-iff-rlp-decodex-tree-not-error)

     (defruled equivalent-error-when-encoding
       (implies (rlp-tree-encoding-p encoding)
                (equal (mv-nth 0 (rlp-decode-tree encoding))
                       (mv-nth 0 (rlp-decodex-tree encoding))))
       :enable rlp-decode-tree
       :use rlp-tree-encoding-p-iff-rlp-decodex-tree-not-error)

     (defruled equivalent-tree-when-encoding
       (implies (rlp-tree-encoding-p encoding)
                (equal (mv-nth 1 (rlp-decode-tree encoding))
                       (mv-nth 1 (rlp-decodex-tree encoding))))
       :use (rlp-encode-tree-of-rlp-decode-tree
             rlp-encode-tree-of-rlp-decodex-tree
             rlp-tree-encoding-p-iff-rlp-decodex-tree-not-error)
       :disable (rlp-encode-tree-of-rlp-decode-tree
                 rlp-encode-tree-of-rlp-decodex-tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decodex-bytes ((encoding byte-listp))
  :returns (mv (error? maybe-rlp-error-p)
               (bytes byte-listp))
  :parents (rlp-decoding-executable)
  :short "Executable RLP decoding of a byte array."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has the same form as the alternative definition rule
     of @(tsee rlp-decode-bytes) in terms of @(tsee rlp-decode-tree).
     As such, it is immediate to prove
     equal (i.e. correct with respect) to @(tsee rlp-decode-bytes),
     using the correctness theorem of @(tsee rlp-decodex-tree)."))
  (b* (((mv error? tree) (rlp-decodex-tree encoding))
       ((when error?) (mv error? nil))
       ((unless (rlp-tree-case tree :leaf))
        (mv (rlp-error-branch-tree (list (car encoding))) nil))
       (bytes (rlp-tree-leaf->bytes tree)))
    (mv nil bytes))
  :hooks (:fix)
  ///

  (defruled rlp-decode-bytes-is-rlp-decodex-bytes
    (and (iff (mv-nth 0 (rlp-decode-bytes encoding))
              (mv-nth 0 (rlp-decodex-bytes encoding)))
         (equal (mv-nth 1 (rlp-decode-bytes encoding))
                (mv-nth 1 (rlp-decodex-bytes encoding))))
    :enable (rlp-decode-bytes-alt-def
             rlp-decode-tree-is-rlp-decodex-tree)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decodex-scalar ((encoding byte-listp))
  :returns (mv (error? maybe-rlp-error-p)
               (scalar natp))
  :parents (rlp-decoding-executable)
  :short "Executable RLP decoding of a scalar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has the same form as the alternative definition rule
     of @(tsee rlp-decode-scalar) in terms of @(tsee rlp-decode-bytes).
     As such, it is immediate to prove
     equal (i.e. correct with respect) to @(tsee rlp-decode-scalar),
     using the correctness theorem of @(tsee rlp-decodex-bytes)."))
  (b* (((mv error? bytes) (rlp-decodex-bytes encoding))
       ((when error?) (mv error? 0))
       ((unless (equal (trim-bendian* bytes) bytes))
        (mv (rlp-error-leading-zeros-in-scalar bytes) 0))
       (scalar (bebytes=>nat bytes)))
    (mv nil scalar))
  :hooks (:fix)
  ///

  (defruled rlp-decode-scalar-is-rlp-decodex-scalar
    (and (iff (mv-nth 0 (rlp-decode-scalar encoding))
              (mv-nth 0 (rlp-decodex-scalar encoding)))
         (equal (mv-nth 1 (rlp-decode-scalar encoding))
                (mv-nth 1 (rlp-decodex-scalar encoding))))
    :enable (rlp-decode-scalar-alt-def
             rlp-decode-bytes-is-rlp-decodex-bytes)))
