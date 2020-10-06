; Ethereum Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(include-book "basics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ hex-prefix
  :parents (ethereum)
  :short "Hex-prefix encoding."
  :long
  (xdoc::topstring-p
   "Hex-prefix is an encoding method for Ethereum,
    described in [YP:C] and in
    <a href=\"https://github.com/ethereum/wiki/wiki/Patricia-Tree#specification-compact-encoding-of-hex-sequence-with-optional-terminator\"
    >Section
    `Specification: Compact encoding of hex sequence with optional terminator'
    of Page `Patricia Tree' of [Wiki]</a>.")
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hp-encode ((nibbles nibble-listp) (flag booleanp))
  :returns (bytes byte-listp
                  :hints (("Goal" :in-theory (enable bytep
                                                     nibblep
                                                     nibble-fix))))
  :parents (hex-prefix)
  :short "Hex-prefix encoding function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @($\\mathtt{HP}$) [YP:(186)] [YP:(187)].")
   (xdoc::p
    "The @($t$) flag is treated as a boolean (i.e. 0 or not 0),
     so we use directly a boolean as argument to this function.
     Note also that @($\\mathtt{HP}$)
     is called with @($\\mathit{true}$) and @($\\mathit{false}$) in [YP:(194)],
     so perhaps [YP:(187)] should be rephrased
     to treat @($t$) as an actual boolean (as opposed to 0 or not 0)."))
  (b* ((ft (if flag 2 0))
       (len-nibbles (len nibbles))
       (evenp (evenp len-nibbles))
       (first-byte (if evenp
                       (* 16 ft)
                     (b* ((first-nibble (nibble-fix (car nibbles))))
                       (+ (* 16 (1+ ft))
                          first-nibble))))
       (rest-nibbles (if evenp
                         nibbles
                       (cdr nibbles)))
       (rest-bytes (hp-encode-aux rest-nibbles)))
    (cons first-byte rest-bytes))
  :no-function t
  :hooks (:fix)

  :prepwork
  ((define hp-encode-aux ((nibbles nibble-listp))
     :guard (evenp (len nibbles))
     :returns (bytes byte-listp
                     :hints (("Goal" :in-theory (enable bytep
                                                        nibblep
                                                        nibble-fix))))
     :parents (hp-encode hex-prefix)
     :short "Turn a even-length sequence of nibbles into a sequence of bytes."
     :long
     (xdoc::topstring-p
      "This calculates the bytes of the result of @($\\mathtt{HP}$)
       that come after the first byte,
       in the way described by [YP:(186)].")
     (b* (((when (endp nibbles)) nil)
          (nibble-hi (nibble-fix (car nibbles)))
          (nibble-lo (nibble-fix (cadr nibbles)))
          (byte (+ (* 16 nibble-hi) nibble-lo))
          (bytes (hp-encode-aux (cddr nibbles))))
       (cons byte bytes))
     :no-function t
     :hooks (:fix)
     ///
     (local (include-book "arithmetic/top" :dir :system))
     (defret len-of-hp-encode-aux
       (equal (len bytes)
              (floor (len nibbles) 2))
       :hyp (evenp (len nibbles))
       :hints (("Goal" :induct (hp-encode-aux nibbles))))))

  ///

  (defret consp-of-hp-encode
    (consp bytes)
    :rule-classes :type-prescription)

  (local (include-book "arithmetic-5/top" :dir :system))

  (defret len-of-hp-encode
    (equal (len bytes)
           (1+ (floor (len nibbles) 2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk hp-encoding-p ((encoding byte-listp))
  :returns (yes/no booleanp)
  :parents (hex-prefix)
  :short "Check if a byte array is a hex-prefix encoding."
  :long
  (xdoc::topstring-p
   "This is a declarative, non-executable definition,
    which essentially characterizes the image of @(tsee hp-encode).")
  (exists (nibbles flag)
          (and (nibble-listp nibbles)
               (booleanp flag)
               (equal (hp-encode nibbles flag) (byte-list-fix encoding))))
  :skolem-name hp-encoding-witness
  ///

  (fty::deffixequiv-sk hp-encoding-p
    :args ((encoding byte-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hp-decode ((encoding byte-listp))
  :returns
  (mv (error? booleanp)
      (nibbles nibble-listp
               :hints (("Goal"
                        :in-theory
                        (e/d
                         (hp-encoding-p)
                         (hp-encoding-p-of-byte-list-fix-encoding)))))
      (flag booleanp
            :hints (("Goal"
                     :in-theory
                     (e/d
                      (hp-encoding-p)
                      (hp-encoding-p-of-byte-list-fix-encoding))))))
  :parents (hex-prefix)
  :short "Hex-prefix decoding function."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the argument byte array is the result of encoding
     some nibble array and boolean flag,
     we return the nibble array and boolean flag,
     along with a @('nil') error flag.
     Otherwise, we return a @('t') error flag,
     along with an empty byte array and a false flag
     (but these two values are irrelevant in this case).")
   (xdoc::p
    "This is a declarative, non-executable definition,
     which says that decoding is the inverse of encoding.")
   (xdoc::p
    "More precisely, we define decoding as, essentially,
     the right inverse of encoding
     (with respect to byte arrays that are valid encodings),
     as explicated by the theorem @('hp-encode-of-hp-decode').
     To prove that decoding is left inverse of encoding
     (with respect to nibble arrays and boolean flags that can be encoded),
     we need to show that encoding is injective
     over nibble arrays and boolean flags that can be encoded.
     We conjecture that the proof of this property
     may be a by-product of deriving an executable implementation of decoding
     via stepwise refinement
     (e.g. using <see topic='@(url apt::apt)'>APT</see>):
     if there were two different pairs of nibble arrays and boolean flags
     whose encodings are equal,
     an executable implementation of decoding,
     which returns a unique nibble array and boolean flag,
     could not be shown to be equal to @('hp-endoding-witness'),
     which is introduced by a @(tsee defchoose) inside @(tsee defun-sk)
     and therefore could be either pair (of a nibble array and a boolean flag).
     Thus, we defer the injectivity and left inverse proofs for now."))
  (b* ((encoding (byte-list-fix encoding)))
    (if (hp-encoding-p encoding)
        (b* (((mv nibbles flag) (hp-encoding-witness encoding)))
          (mv nil nibbles flag))
      (mv t nil nil)))
  :no-function t
  :hooks (:fix)
  ///

  (defrule hp-encode-of-hp-decode
    (implies (and (byte-listp encoding)
                  (hp-encoding-p encoding))
             (b* (((mv d-error? d-nibbles d-flag) (hp-decode encoding))
                  (e-encoding (hp-encode d-nibbles d-flag)))
               (and (not d-error?)
                    (equal e-encoding encoding))))
    :enable hp-encoding-p))
