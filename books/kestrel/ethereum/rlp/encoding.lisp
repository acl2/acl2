; Ethereum Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "big-endian")
(include-book "trees")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "kestrel/utilities/define-sk" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rlp-encoding
  :parents (rlp)
  :short "RLP encoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "We specify RLP encoding via functions
     from byte arrays, trees, and scalars
     to byte arrays.
     These functions closely correspond to the ones in [YP:B].
     They are high-level, yet executable.")
   (xdoc::p
    "We also define valid RLP encodings, as images of the encoding functions.
     These are declaratively defined, non-executable predicates."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-encode-bytes ((bytes byte-listp))
  :parents (rlp-encoding)
  :returns (mv (error? booleanp)
               (encoding byte-listp
                         :hints (("Goal"
                                  :in-theory
                                  (enable bytep
                                          len-of-nat=>bebytes*-leq-8)))))
  :short "RLP encoding of a byte array."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @($R_{\\mathrm{b}}$) [YP:(180)].")
   (xdoc::p
    "The first result of this function is an error flag,
     which is @('t') if the argument byte array cannot be encoded;
     in this case, @('nil') is returned as the (irrelevant) second result.")
   (xdoc::p
    "Encodings are never empty,
     i.e. they always consist of at least one byte:
     see theorem @('consp-of-rlp-encode-bytes-when-no-error').")
   (xdoc::p
    "The first byte of an encoding is always below 192:
     see theorem @('car-of-rlp-encode-bytes-bound-when-no-error').")
   (xdoc::p
    "The total length of an encoding can be determined
     from the first few bytes (i.e. a prefix) of the encoding:
     see theorem @('len-of-rlp-encode-bytes-from-prefix').
     This rewrite rule is disabled by default,
     because it turns the left-hand side into a more complex right-hand side;
     however, it is usefully enabled in certain proofs.")
   (xdoc::p
    "The total length of an encoding that uses a ``long'' length field
     (i.e. when the initial byte is followed by the length of the length,
     and the actual length consists of one or more bytes)
     is larger than the length field itself:
     see theorem @('len-of-rlp-encode-bytes-lower-bound-when-len-len')."))
  (b* ((bytes (byte-list-fix bytes)))
    (cond ((and (= (len bytes) 1)
                (< (car bytes) 128)) (mv nil bytes))
          ((< (len bytes) 56) (b* ((encoding (cons (+ 128 (len bytes))
                                                   bytes)))
                                (mv nil encoding)))
          ((< (len bytes)
              (expt 2 64)) (b* ((be (nat=>bebytes* (len bytes)))
                                (encoding (cons (+ 183 (len be))
                                                (append be bytes))))
                             (mv nil encoding)))
          (t (mv t nil))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule consp-of-rlp-encode-bytes-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-bytes bytes)))
             (consp (mv-nth 1 (rlp-encode-bytes bytes))))
    :rule-classes :type-prescription)

  (defrule car-of-rlp-encode-bytes-upper-bound-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-bytes bytes)))
             (<= (car (mv-nth 1 (rlp-encode-bytes bytes)))
                 191))
    :rule-classes :linear
    :enable len-of-nat=>bebytes*-leq-8)

  (defruled len-of-rlp-encode-bytes-from-prefix
    (b* (((mv error? encoding) (rlp-encode-bytes bytes)))
      (implies
       (not error?)
       (equal (len encoding)
              (cond ((< (car encoding) 128) 1)
                    ((< (car encoding) (+ 128 56)) (1+ (- (car encoding) 128)))
                    (t (b* ((lenlen (- (car encoding) 183)))
                         (+ 1
                            lenlen
                            (bebytes=>nat (take lenlen (cdr encoding)))))))))))

  (defrule len-of-rlp-encode-bytes-lower-bound-when-len-len
    (b* (((mv error? encoding) (rlp-encode-bytes bytes)))
      (implies (and (not error?)
                    (>= (car encoding) (+ 128 56)))
               (> (len encoding) (- (car encoding) 183))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rlp-encode-tree
  :parents (rlp-encoding)
  :short "RLP encoding of a tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to
     @($\\mathtt{RLP}$) [YP:(179)],
     @($R_{\\mathrm{l}}$) [YP:(183)],
     and @($s$) [YP:(184)].
     More precisely,
     @(tsee rlp-encode-tree) corresponds to @($\\mathtt{RLP}$),
     the branching case of @(tsee rlp-encode-tree)
     corresponds to @($R_{\\mathrm{l}}$),
     and @(tsee rlp-encode-tree-list) corresponds to @($s$).")
   (xdoc::p
    "The first result of
     @(tsee rlp-encode-tree) and @(tsee rlp-encode-tree-list)
     is an error flag,
     which is @('t') if the argument tree or list of trees cannot be encoded;
     in this case, @('nil') is returned as the (irrelevant) second result.")
   (xdoc::p
    "Encodings are never empty,
     i.e. they always consist of at least one byte:
     see theorem @('consp-of-rlp-encode-tree-when-no-error').")
   (xdoc::p
    "The first byte of the encoding of a leaf tree is always below 192:
     see theorems @('car-of-rlp-encode-tree-leaf-upper-bound-when-no-error')
     and @('rlp-encode-tree-car-ineq-to-tree-leaf').
     The first byte of the encoding of a branching tree is always at least 192:
     see theorems @('car-of-rlp-encode-tree-leaf-upper-bound-when-no-error')
     and @('rlp-encode-tree-car-ineq-to-tree-branch').")
   (xdoc::p
    "The total length of an encoding can be determined
     from the first few bytes (i.e. a prefix) of the encoding:
     see theorem @('len-of-rlp-encode-tree-from-prefix').
     This rewrite rule is disabled by default,
     because it turns the left-hand side into a more complex right-hand side;
     however, it is usefully enabled in certain proofs.")
   (xdoc::p
    "The total length of an encoding that uses a ``long'' length field
     (i.e. when the initial byte is followed by the length of the length,
     and the actual length consists of one or more bytes)
     is larger than the length field itself:
     see theorems @('len-of-rlp-encode-tree-lower-bound-when-len-len-1')
     and @('len-of-rlp-encode-tree-lower-bound-when-len-len-2').")
   (xdoc::p
    "Once @(tsee rlp-encode-tree) is defined,
     @(tsee rlp-encode-bytes) could be alternatively ``defined''
     by wrapping the byte array in a tree and encoding the tree.
     This alternative definition rule is disabled by default,
     but may be useful sometimes.
     It should not be enabled
     if the definition of @(tsee rlp-encode-tree) is enabled
     (since the latter is defined in terems of @(tsee rlp-encode-bytes),
     so we add a theory invariant to that effect.")
   (xdoc::@def "rlp-encode-tree")
   (xdoc::@def "rlp-encode-tree-list"))
  :flag-local nil
  :verify-guards nil ; done below

  (define rlp-encode-tree ((tree rlp-treep))
    :returns (mv (error? booleanp)
                 (encoding byte-listp))
    (rlp-tree-case
     tree
     :leaf (rlp-encode-bytes tree.bytes)
     :branch (b* (((mv error? encoding) (rlp-encode-tree-list tree.subtrees))
                  ((when error?) (mv t nil)))
               (cond ((< (len encoding) 56)
                      (b* ((encoding (cons (+ 192 (len encoding))
                                           encoding)))
                        (mv nil encoding)))
                     ((< (len encoding)
                         (expt 2 64))
                      (b* ((be (nat=>bebytes* (len encoding)))
                           (encoding (cons (+ 247 (len be))
                                           (append be encoding))))
                        (mv nil encoding)))
                     (t (mv t nil)))))
    :measure (rlp-tree-count tree)
    :no-function t)

  (define rlp-encode-tree-list ((trees rlp-tree-listp))
    :returns (mv (error? booleanp)
                 (encoding byte-listp))
    (b* (((when (endp trees)) (mv nil nil))
         ((mv error? encoding1) (rlp-encode-tree (car trees)))
         ((when error?) (mv t nil))
         ((mv error? encoding2) (rlp-encode-tree-list (cdr trees)))
         ((when error?) (mv t nil)))
      (mv nil (append encoding1 encoding2)))
    :measure (rlp-tree-list-count trees)
    :no-function t)

  :returns-hints (("Goal" :in-theory (enable bytep
                                             len-of-nat=>bebytes*-leq-8)))

  ///

  (verify-guards rlp-encode-tree
    :hints (("Goal"
             :in-theory (enable acl2::true-listp-when-byte-listp-rewrite))))

  (fty::deffixequiv-mutual rlp-encode-tree)

  (defrule consp-of-rlp-encode-tree-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-tree tree)))
             (consp (mv-nth 1 (rlp-encode-tree tree))))
    :rule-classes :type-prescription
    :expand (rlp-encode-tree tree))

  (defrule car-of-rlp-encode-tree-leaf-upper-bound-when-no-error
    (implies (and (not (mv-nth 0 (rlp-encode-tree tree)))
                  (rlp-tree-case tree :leaf))
             (<= (car (mv-nth 1 (rlp-encode-tree tree)))
                 191))
    :rule-classes :linear)

  (defrule car-of-rlp-encode-tree-branch-upper-bound-when-no-error
    (implies (and (not (mv-nth 0 (rlp-encode-tree tree)))
                  (rlp-tree-case tree :branch))
             (>= (car (mv-nth 1 (rlp-encode-tree tree)))
                 192))
    :rule-classes :linear
    :expand (rlp-encode-tree tree))

  (defrule rlp-encode-tree-car-ineq-to-tree-leaf
    (implies (not (mv-nth 0 (rlp-encode-tree tree)))
             (equal (<= (car (mv-nth 1 (rlp-encode-tree tree)))
                        191)
                    (rlp-tree-case tree :leaf))))

  (defrule rlp-encode-tree-car-ineq-to-tree-branch
    (implies (not (mv-nth 0 (rlp-encode-tree tree)))
             (equal (>= (car (mv-nth 1 (rlp-encode-tree tree)))
                        192)
                    (rlp-tree-case tree :branch))))

  (defruled len-of-rlp-encode-tree-from-prefix
    (b* (((mv error? encoding) (rlp-encode-tree tree)))
      (implies
       (not error?)
       (equal (len encoding)
              (cond ((< (car encoding) 128) 1)
                    ((< (car encoding) (+ 128 56)) (1+ (- (car encoding) 128)))
                    ((< (car encoding) 192)
                     (b* ((lenlen (- (car encoding) 183)))
                       (+ 1
                          lenlen
                          (bebytes=>nat (take lenlen (cdr encoding))))))
                    ((< (car encoding) (+ 192 56)) (1+ (- (car encoding) 192)))
                    (t (b* ((lenlen (- (car encoding) 247)))
                         (+ 1
                            lenlen
                            (bebytes=>nat (take lenlen (cdr encoding))))))))))
    :expand (rlp-encode-tree tree)
    :enable len-of-rlp-encode-bytes-from-prefix)

  (defrule len-of-rlp-encode-tree-lower-bound-when-len-len-1
    (b* (((mv error? encoding) (rlp-encode-tree tree)))
      (implies (and (not error?)
                    (>= (car encoding) (+ 128 56))
                    (< (car encoding) 192))
               (> (len encoding) (- (car encoding) 183))))
    :rule-classes :linear
    :expand (rlp-encode-tree tree))

  (defrule len-of-rlp-encode-tree-lower-bound-when-len-len-2
    (b* (((mv error? encoding) (rlp-encode-tree tree)))
      (implies (and (not error?)
                    (>= (car encoding) (+ 192 56)))
               (> (len encoding) (- (car encoding) 247))))
    :rule-classes :linear
    :expand (rlp-encode-tree tree))

  (defrule consp-of-rlp-encode-tree-list-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-tree-list trees)))
             (equal (consp (mv-nth 1 (rlp-encode-tree-list trees)))
                    (consp trees)))
    :expand (rlp-encode-tree-list trees))

  (defrule nonnil-rlp-encode-tree-list-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-tree-list trees)))
             (iff (mv-nth 1 (rlp-encode-tree-list trees))
                  (consp trees)))
    :expand (rlp-encode-tree-list trees))

  (defruled rlp-encode-bytes-alt-def
    (equal (rlp-encode-bytes bytes)
           (rlp-encode-tree (rlp-tree-leaf bytes)))
    :enable rlp-encode-tree)

  (theory-invariant (incompatible (:rewrite rlp-encode-bytes-alt-def)
                                  (:definition rlp-encode-tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-encode-scalar ((scalar natp))
  :returns (mv (error? booleanp)
               (encoding byte-listp))
  :parents (rlp-encoding)
  :short "RLP encoding of a scalar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @($\\mathtt{RLP}$) [YP:(185)].")
   (xdoc::p
    "The first result of this function is an error flag,
     which is @('t') if the argument scalar is so large that
     its big-endian representation reaches @($2^{64}$) in length."))
  (rlp-encode-bytes (nat=>bebytes* (nfix scalar)))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-tree-encoding-p ((encoding byte-listp))
  :returns (yes/no booleanp)
  :parents (rlp-encoding)
  :short "Check if a byte array is an RLP encoding of a tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a declarative, non-executable definition,
     which essentially characterizes the image of @(tsee rlp-encode-tree)
     (over trees that can be encoded,
     i.e. such that @(tsee rlp-encode-tree) returns a @('nil') error flag).")
   (xdoc::p
    "By definition,
     the witness function is right inverse of the encoding function,
     over the valid encodings."))
  (exists (tree)
          (and (rlp-treep tree)
               (b* (((mv error? encoding1) (rlp-encode-tree tree)))
                 (and (not error?)
                      (equal encoding1 (byte-list-fix encoding))))))
  :skolem-name rlp-tree-encoding-witness
  ///

  (fty::deffixequiv-sk rlp-tree-encoding-p
    :args ((encoding byte-listp)))

  (defrule rlp-treep-of-rlp-tree-encoding-witness
    (implies (rlp-tree-encoding-p encoding)
             (rlp-treep (rlp-tree-encoding-witness encoding))))

  (defrule rlp-encode-tree-of-rlp-tree-encoding-witness
    (implies (rlp-tree-encoding-p encoding)
             (b* (((mv error? encoding1) (rlp-encode-tree
                                          (rlp-tree-encoding-witness
                                           encoding))))
               (and (not error?)
                    (equal encoding1
                           (byte-list-fix encoding))))))

  (defrule rlp-tree-encoding-p-of-rlp-tree-encode-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-tree tree)))
             (rlp-tree-encoding-p (mv-nth 1 (rlp-encode-tree tree))))
    :use (:instance rlp-tree-encoding-p-suff
          (encoding (mv-nth 1 (rlp-encode-tree (rlp-tree-fix tree))))
          (tree (rlp-tree-fix tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-bytes-encoding-p ((encoding byte-listp))
  :returns (yes/no booleanp)
  :parents (rlp-encoding)
  :short "Check if a byte array is an RLP encoding of a byte array."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee rlp-tree-encoding-p).")
   (xdoc::p
    "The encoding of a byte array
     is also the encoding of the tree
     consisting of a single leaf with that byte array.
     The encoding of a leaf tree
     is also the encoding of the byte array in the tree.")
   (xdoc::p
    "By definition,
     the witness function is right inverse of the encoding function,
     over the valid encodings."))
  (exists (bytes)
          (and (byte-listp bytes)
               (b* (((mv error? encoding1) (rlp-encode-bytes bytes)))
                 (and (not error?)
                      (equal encoding1 (byte-list-fix encoding))))))
  :skolem-name rlp-bytes-encoding-witness
  ///

  (fty::deffixequiv-sk rlp-bytes-encoding-p
    :args ((encoding byte-listp)))

  (defrule byte-listp-of-rlp-bytes-encoding-witness
    (implies (rlp-bytes-encoding-p encoding)
             (byte-listp (rlp-bytes-encoding-witness encoding))))

  (defrule rlp-encode-bytes-of-rlp-bytes-encoding-witness
    (implies (rlp-bytes-encoding-p encoding)
             (b* (((mv error? encoding1) (rlp-encode-bytes
                                          (rlp-bytes-encoding-witness
                                           encoding))))
               (and (not error?)
                    (equal encoding1
                           (byte-list-fix encoding))))))

  (defrule rlp-bytes-encoding-p-of-rlp-bytes-encode-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-bytes bytes)))
             (rlp-bytes-encoding-p (mv-nth 1 (rlp-encode-bytes bytes))))
    :use (:instance rlp-bytes-encoding-p-suff
          (encoding (mv-nth 1 (rlp-encode-bytes (byte-list-fix bytes))))
          (bytes (byte-list-fix bytes))))

  (defruled rlp-tree-encoding-p-when-rlp-bytes-encoding-p
    (implies (rlp-bytes-encoding-p encoding)
             (rlp-tree-encoding-p encoding))
    :use (:instance rlp-tree-encoding-p-suff
          (tree (rlp-tree-leaf (rlp-bytes-encoding-witness encoding))))
    :enable rlp-encode-bytes-alt-def)

  (defruled rlp-bytes-encoding-p-when-rlp-tree-encoding-p-and-leaf
    (implies (and (rlp-tree-encoding-p encoding)
                  (rlp-tree-case (rlp-tree-encoding-witness encoding) :leaf))
             (rlp-bytes-encoding-p encoding))
    :use (:instance rlp-bytes-encoding-p-suff
          (bytes (rlp-tree-leaf->bytes (rlp-tree-encoding-witness encoding))))
    :enable (rlp-encode-bytes-alt-def rlp-tree-encoding-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-scalar-encoding-p ((encoding byte-listp))
  :returns (yes/no booleanp)
  :parents (rlp-encoding)
  :short "Check if a byte array is an RLP encoding of a scalar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee rlp-tree-encoding-p).")
   (xdoc::p
    "The encoding of a scalar
     is also the encoding of the byte array
     that is the big endian representation of the scalar.
     The encoding of a byte array with no leading zeros
     is also the encoding of the scalar
     whose big endian representation is the byte array.")
   (xdoc::p
    "By definition,
     the witness function is right inverse of the encoding function,
     over the valid encodings."))
  (exists (scalar)
          (and (natp scalar)
               (b* (((mv error? encoding1) (rlp-encode-scalar scalar)))
                 (and (not error?)
                      (equal encoding1 (byte-list-fix encoding))))))
  :skolem-name rlp-scalar-encoding-witness
  ///

  (fty::deffixequiv-sk rlp-scalar-encoding-p
    :args ((encoding byte-listp)))

  (defrule natp-of-rlp-scalar-encoding-witness
    (implies (rlp-scalar-encoding-p encoding)
             (natp (rlp-scalar-encoding-witness encoding))))

  (defrule rlp-encode-scalar-of-rlp-scalar-encoding-witness
    (implies (rlp-scalar-encoding-p encoding)
             (b* (((mv error? encoding1) (rlp-encode-scalar
                                          (rlp-scalar-encoding-witness
                                           encoding))))
               (and (not error?)
                    (equal encoding1
                           (byte-list-fix encoding))))))

  (defrule rlp-scalar-encoding-p-of-rlp-scalar-encode-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-scalar scalar)))
             (rlp-scalar-encoding-p (mv-nth 1 (rlp-encode-scalar scalar))))
    :use (:instance rlp-scalar-encoding-p-suff
          (encoding (mv-nth 1 (rlp-encode-scalar (nfix scalar))))
          (scalar (nfix scalar))))

  (defruled rlp-bytes-encoding-p-when-rlp-scalar-encoding-p
    (implies (rlp-scalar-encoding-p encoding)
             (rlp-bytes-encoding-p encoding))
    :use (:instance rlp-bytes-encoding-p-suff
          (bytes (nat=>bebytes* (rlp-scalar-encoding-witness encoding))))
    :enable rlp-encode-scalar)

  (defruled rlp-scalar-encoding-p-when-rlp-bytes-encoding-p-and-no-leading-zeros
    (implies (and (rlp-bytes-encoding-p encoding)
                  (equal (trim-bendian*
                          (rlp-bytes-encoding-witness encoding))
                         (rlp-bytes-encoding-witness encoding)))
             (rlp-scalar-encoding-p encoding))
    :use (:instance rlp-scalar-encoding-p-suff
          (scalar (bebytes=>nat (rlp-bytes-encoding-witness encoding))))
    :enable (rlp-encode-scalar
             rlp-bytes-encoding-p)))
