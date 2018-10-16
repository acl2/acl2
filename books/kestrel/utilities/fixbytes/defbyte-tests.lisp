; Fixtypes for Unsigned and Signed Bytes -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/testing" :dir :system)
(include-book "defbyte")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test successful calls with a positive integer as size:

(must-succeed*
 (fty::defbyte 8)
 (assert! (function-symbolp 'ubyte8-p (w state)))
 (assert! (function-symbolp 'ubyte8-fix (w state)))
 (assert! (function-symbolp 'ubyte8-equiv$inline (w state))))

(must-succeed*
 (fty::defbyte 1)
 (assert! (function-symbolp 'ubyte1-p (w state)))
 (assert! (function-symbolp 'ubyte1-fix (w state)))
 (assert! (function-symbolp 'ubyte1-equiv$inline (w state))))

(must-succeed*
 (fty::defbyte 100)
 (assert! (function-symbolp 'ubyte100-p (w state)))
 (assert! (function-symbolp 'ubyte100-fix (w state)))
 (assert! (function-symbolp 'ubyte100-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test successful calls with a named constant as size:

(must-succeed*
 (defconst *size* 7)
 (fty::defbyte *size*)
 (assert! (function-symbolp 'ubyte7-p (w state)))
 (assert! (function-symbolp 'ubyte7-fix (w state)))
 (assert! (function-symbolp 'ubyte7-equiv$inline (w state))))

(must-succeed*
 (defconst *size* 16)
 (fty::defbyte *size*)
 (assert! (function-symbolp 'ubyte16-p (w state)))
 (assert! (function-symbolp 'ubyte16-fix (w state)))
 (assert! (function-symbolp 'ubyte16-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test successful calls with a call of a unary function as size:

(must-succeed*
 (define size () 32)
 (fty::defbyte (size) :type mybyte :description "my bytes")
 (assert! (function-symbolp 'mybyte-p (w state)))
 (assert! (function-symbolp 'mybyte-fix (w state)))
 (assert! (function-symbolp 'mybyte-equiv$inline (w state))))

(must-succeed*
 (encapsulate
   (((size) => *))
   (local (defun size () 2))
   (defthm posp-of-size (posp (size))))
 (fty::defbyte (size) :type mybyte :description "my bytes")
 (assert! (function-symbolp 'mybyte-p (w state)))
 (assert! (function-symbolp 'mybyte-fix (w state)))
 (assert! (function-symbolp 'mybyte-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test calls with a bad size:

(must-fail (fty::defbyte "8"))

(must-fail (fty::defbyte 0))

(must-fail (fty::defbyte 3/4))

(must-fail (fty::defbyte :key))

(must-fail (fty::defbyte *not-a-const*))

(must-succeed*
 (defconst *not-a-posp-const* '(1 2 3))
 (must-fail (fty::defbyte *not-a-posp-const*)))

(must-fail (fty::defbyte (not-a-fn)))

(must-fail (fty::defbyte (len)))

(must-fail (fty::defbyte (cons)))

(must-succeed*
 (defun not-guard-verif () 8)
 (must-fail
  (fty::defbyte (not-guard-verif) :type mybyte :description "my bytes")))

(must-succeed*
 (defun not-provably-posp () "a")
 (must-fail
  (fty::defbyte (not-provably-posp) :type mybyte :description "my bytes")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :SIGNED input:

(must-fail (fty::defbyte 8 :signed "no"))

(must-succeed*
 (fty::defbyte 8 :signed nil)
 (assert! (ubyte8-p 255))
 (assert! (not (ubyte8-p -1))))

(must-succeed*
 (fty::defbyte 8 :signed t)
 (assert! (sbyte8-p -128))
 (assert! (not (sbyte8-p 255))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :TYPE input:

(must-fail (fty::defbyte 8 :type "mybyte"))

(must-succeed*
 (fty::defbyte 8 :type mybyte)
 (assert! (function-symbolp 'mybyte-p (w state)))
 (assert! (function-symbolp 'mybyte-fix (w state)))
 (assert! (function-symbolp 'mybyte-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PRED input:

(must-fail (fty::defbyte 8 :pred 55))

(must-succeed*
 (fty::defbyte 8 :pred mypred)
 (assert! (function-symbolp 'mypred (w state)))
 (assert! (function-symbolp 'ubyte8-fix (w state)))
 (assert! (function-symbolp 'ubyte8-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :FIX input:

(must-fail (fty::defbyte 8 :fix '(1 a #\c)))

(must-succeed*
 (fty::defbyte 8 :fix myfix)
 (assert! (function-symbolp 'ubyte8-p (w state)))
 (assert! (function-symbolp 'myfix (w state)))
 (assert! (function-symbolp 'ubyte8-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :EQUIV input:

(must-fail (fty::defbyte 8 :equiv "EQ"))

(must-succeed*
 (fty::defbyte 8 :equiv myequiv)
 (assert! (function-symbolp 'ubyte8-p (w state)))
 (assert! (function-symbolp 'ubyte8-fix (w state)))
 (assert! (function-symbolp 'myequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PARENTS input:

(must-fail (fty::defbyte 8 :parents "123"))

(must-succeed (fty::defbyte 8 :parents nil))

(must-succeed (fty::defbyte 8 :parents (this that)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :DESCRIPTION input:

(must-fail (fty::defbyte 8 :description 'something))

(must-succeed (fty::defbyte 8 :description nil))

(must-succeed (fty::defbyte 8 :description "my bytes"))

(must-succeed
 (fty::defbyte 8 :description (concatenate 'string "my" " " "bytes")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :LONG input:

(must-fail (fty::defbyte 8 :long #\a))

(must-succeed (fty::defbyte 8 :long nil))

(must-succeed (fty::defbyte 8 :long "<p>More doc.</p>"))

(must-succeed (fty::defbyte 8 :long (xdoc::topp "More doc.")))
