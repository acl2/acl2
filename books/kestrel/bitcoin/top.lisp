; Bitcoin Library
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "base58")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bitcoin
  :parents (acl2::kestrel-books acl2::project)
  :short "A library for Bitcoin."
  :long
  (xdoc::topapp
   (xdoc::p
    "Currently this library contains a formal model of some aspects of
     <a href=\"https://bitcoin.org\">Bitcoin</a>.
     It is expected that this library will be extended with more
     Bitcoin-related formalizations and tools.")
   (xdoc::p
    "This library is based on
     the <a href=\"https://bitcoin.org\">Bitcoin web site</a>
     (`Site' for short),
     the <a href=\"https://en.bitcoin.it\">Bitcoin Wiki</a>
     (`Wiki' for short),
     the <a href=\"https://bitcoin.org/bitcoin.pdf\">Bitcoin White Paper</a>
     (`WP' for short), and
     the <a href=\"https://github.com/bitcoinbook/bitcoinbook\">`Mastering
     Bitcoin' book</a>
     (`MB' for short)."))
  :order-subtopics t)
