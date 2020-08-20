; Solidity Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOLIDITY")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Linked references to the Solidity language documentation
; for the XDOC documentation of our ACL2 library for Solidity.

(defconst xdoc::*sld*
  (xdoc::&&
   "["
   (xdoc::ahref "https://solidity.readthedocs.io/en/v0.7.0/index.html"
                "SD")
   "]"))

(defconst xdoc::*sld-types*
  (xdoc::&&
   "["
   (xdoc::ahref "https://solidity.readthedocs.io/en/v0.7.0/types.html"
                "SD: Types")
   "]"))

(defconst xdoc::*sld-types-booleans*
  (xdoc::&&
   "["
   (xdoc::ahref "https://solidity.readthedocs.io/en/v0.7.0/types.html#booleans"
                "SD: Types: Booleans")
   "]"))

(defconst xdoc::*sld-types-integers*
  (xdoc::&&
   "["
   (xdoc::ahref "https://solidity.readthedocs.io/en/v0.7.0/types.html#integers"
                "SD: Types: Integers")
   "]"))

(defconst xdoc::*sld-integer-shifts*
  (xdoc::&&
   "["
   (xdoc::ahref "https://solidity.readthedocs.io/en/v0.7.0/types.html#shifts"
                "SD: Types: Integers: Shifts")
   "]"))

(defconst xdoc::*sld-integer-division*
  (xdoc::&&
   "["
   (xdoc::ahref "https://solidity.readthedocs.io/en/v0.7.0/types.html#division"
                "SD: Types: Integers: Division")
   "]"))

(defconst xdoc::*sld-integer-modulo*
  (xdoc::&&
   "["
   (xdoc::ahref "https://solidity.readthedocs.io/en/v0.7.0/types.html#modulo"
                "SD: Types: Integers: Modulo")
   "]"))

(defconst xdoc::*sld-integer-exponentiation*
  (xdoc::&&
   "["
   (xdoc::ahref "https://solidity.readthedocs.io/en/v0.7.0/types.html#exponentiation"
                "SD: Types: Integers: Exponentiation")
   "]"))

(defconst xdoc::*sld-types-conversions-implicit*
  (xdoc::&&
   "["
   (xdoc::ahref
    "https://solidity.readthedocs.io/en/v0.7.0/types.html#implicit-conversions"
    "SD: Types: Conversions between Elementary Types: Implicit Conversions")
   "]"))
