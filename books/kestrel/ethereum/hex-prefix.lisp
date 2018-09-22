; Ethereum Library -- Hex-Prefix Encoding
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "basics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ hex-prefix
  :parents (ethereum)
  :short "Hex-prefix encoding."
  :long
  (xdoc::topp
   "Hex-prefix is an encoding method for Ethereum,
    described in [YP:C] and in the
    `Specification: Compact encoding of hex sequence with optional terminator'
    section of the `Patricia Tree' page of [Wiki].")
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hp-encode ((nibbles ubyte4-listp) (flag booleanp))
  :returns (bytes ubyte8-listp
                  :hints (("Goal" :in-theory (enable ubyte8p
                                                     ubyte4p
                                                     ubyte4-fix))))
  :parents (hex-prefix)
  :short "Hex-prefix encoding function."
  :long
  (xdoc::topapp
   (xdoc::p
    "This corresponds to @($\\mathtt{HP}$) [YP:(186)] [YP:(187)].")
   (xdoc::p
    "The @($t$) flag is effectively treated as a boolean (i.e. 0 or not 0),
     so we use directly a boolean as argument to this function.
     Note also that @($\\mathtt{HP}$)
     is called with @($\\mathit{true}$) and @($\\mathit{false}$) in [YP:(194)],
     so perhaps [YP:(187)] should be rephrased
     to treat @($t$) as an actual boolean."))
  (b* ((ft (if flag 2 0))
       (len-nibbles (len nibbles))
       (evenp (evenp len-nibbles))
       (first-byte (if evenp
                       (* 16 ft)
                     (b* ((first-nibble (ubyte4-fix (car nibbles))))
                       (+ (* 16 (1+ ft))
                          first-nibble))))
       (rest-nibbles (if evenp
                         nibbles
                       (cdr nibbles)))
       (rest-bytes (hp-encode-aux rest-nibbles)))
    (cons first-byte rest-bytes))
  :hooks (:fix)

  :prepwork
  ((define hp-encode-aux ((nibbles ubyte4-listp))
     :guard (evenp (len nibbles))
     :returns (bytes ubyte8-listp
                     :hints (("Goal" :in-theory (enable ubyte8p
                                                        ubyte4p
                                                        ubyte4-fix))))
     :parents (hp-encode hex-prefix)
     :short "Turn a even-length sequence of nibbles into a sequence of bytes."
     :long
     (xdoc::topp
      "This calculates the bytes of the result of @($\\mathtt{HP}$)
       that come after the first byte,
       in the way described by [YP:(186)].")
     (b* (((when (endp nibbles)) nil)
          (nibble-hi (ubyte4-fix (car nibbles)))
          (nibble-lo (ubyte4-fix (cadr nibbles)))
          (byte (+ (* 16 nibble-hi) nibble-lo))
          (bytes (hp-encode-aux (cddr nibbles))))
       (cons byte bytes))
     :hooks (:fix))))
