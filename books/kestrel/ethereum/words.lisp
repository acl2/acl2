; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/fty/defbyte" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc words
  :parents (basics)
  :short "Words."
  :long
  (xdoc::topstring
   (xdoc::p
    "[YP:9.1] defines the size of words as 256 bits.
     We formalize words as
     the elements of the set @($\\mathbb{N}_{256}$) [YP:3],
     i.e. natural numbers below 256.")))

(fty::defbyte word
  :size 256
  :pred wordp
  :parents (words)
  :short "Fixtype of words.")
