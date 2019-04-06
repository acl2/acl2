; FTY -- Byte Fixtype Generator -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defbyte")

(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test successful calls with a positive integer as size:

(must-succeed*
 (fty::defbyte ubyte8 :size 8)
 (assert! (function-symbolp 'ubyte8-p (w state)))
 (assert! (function-symbolp 'ubyte8-fix (w state)))
 (assert! (function-symbolp 'ubyte8-equiv$inline (w state))))

(must-succeed*
 (fty::defbyte ubyte1 :size 1)
 (assert! (function-symbolp 'ubyte1-p (w state)))
 (assert! (function-symbolp 'ubyte1-fix (w state)))
 (assert! (function-symbolp 'ubyte1-equiv$inline (w state))))

(must-succeed*
 (fty::defbyte ubyte100 :size 100)
 (assert! (function-symbolp 'ubyte100-p (w state)))
 (assert! (function-symbolp 'ubyte100-fix (w state)))
 (assert! (function-symbolp 'ubyte100-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test successful calls with a named constant as size:

(must-succeed*
 (defconst *size* 7)
 (fty::defbyte ubyte7 :size *size*)
 (assert! (function-symbolp 'ubyte7-p (w state)))
 (assert! (function-symbolp 'ubyte7-fix (w state)))
 (assert! (function-symbolp 'ubyte7-equiv$inline (w state))))

(must-succeed*
 (defconst *size* 16)
 (fty::defbyte ubyte16 :size *size*)
 (assert! (function-symbolp 'ubyte16-p (w state)))
 (assert! (function-symbolp 'ubyte16-fix (w state)))
 (assert! (function-symbolp 'ubyte16-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test successful calls with a call of a unary function as size:

(must-succeed*
 (define size () 32)
 (fty::defbyte byte :size (size))
 (assert! (function-symbolp 'byte-p (w state)))
 (assert! (function-symbolp 'byte-fix (w state)))
 (assert! (function-symbolp 'byte-equiv$inline (w state))))

(must-succeed*
 (encapsulate
   (((size) => *))
   (local (defun size () 2))
   (defthm posp-of-size (posp (size))))
 (fty::defbyte byte :size (size))
 (assert! (function-symbolp 'byte-p (w state)))
 (assert! (function-symbolp 'byte-fix (w state)))
 (assert! (function-symbolp 'byte-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the TYPE input:

(must-fail (fty::defbyte "mybyte" :size 8))

(must-succeed*
 (fty::defbyte mybyte :size 8)
 (assert! (function-symbolp 'mybyte-p (w state)))
 (assert! (function-symbolp 'mybyte-fix (w state)))
 (assert! (function-symbolp 'mybyte-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :SIZE input:

(must-fail (fty::defbyte byte :size "8"))

(must-fail (fty::defbyte byte :size 0))

(must-fail (fty::defbyte byte :size 3/4))

(must-fail (fty::defbyte byte :size :key))

(must-fail (fty::defbyte byte :size *not-a-const*))

(must-succeed*
 (defconst *not-a-posp-const* '(1 2 3))
 (must-fail (fty::defbyte byte :size *not-a-posp-const*)))

(must-fail (fty::defbyte byte :size (not-a-fn)))

(must-fail (fty::defbyte byte :size (len)))

(must-fail (fty::defbyte byte :size (cons)))

(must-succeed*
 (defun not-guard-verif () 8)
 (assert-event (not (eq (symbol-class 'not-guard-verif (w state))
                        :common-lisp-compliant)))
 (must-fail
  (fty::defbyte byte :size (not-guard-verif))))

(must-succeed*
 (defun not-provably-posp () "a")
 (verify-guards not-provably-posp)
 (must-fail
  (fty::defbyte byte :size (not-provably-posp))))

(must-succeed*
 (fty::defbyte byte :size 10)
 (assert! (byte-p 1023))
 (assert! (not (byte-p 1024))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :SIGNED input:

(must-fail (fty::defbyte byte :size 8 :signed "no"))

(must-succeed*
 (fty::defbyte ubyte :size 8 :signed nil)
 (assert! (ubyte-p 255))
 (assert! (not (ubyte-p -1))))

(must-succeed*
 (fty::defbyte sbyte :size 8 :signed t)
 (assert! (sbyte-p -128))
 (assert! (not (sbyte-p 255))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PRED input:

(must-fail (fty::defbyte byte :size 8 :pred 55))

(must-succeed*
 (fty::defbyte byte :size 8 :pred mypred)
 (assert! (function-symbolp 'mypred (w state)))
 (assert! (function-symbolp 'byte-fix (w state)))
 (assert! (function-symbolp 'byte-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :FIX input:

(must-fail (fty::defbyte byte :size 8 :fix '(1 a #\c)))

(must-succeed*
 (fty::defbyte byte :size 8 :fix myfix)
 (assert! (function-symbolp 'byte-p (w state)))
 (assert! (function-symbolp 'myfix (w state)))
 (assert! (function-symbolp 'byte-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :EQUIV input:

(must-fail (fty::defbyte byte :size 8 :equiv "EQ"))

(must-succeed*
 (fty::defbyte byte :size 8 :equiv myequiv)
 (assert! (function-symbolp 'byte-p (w state)))
 (assert! (function-symbolp 'byte-fix (w state)))
 (assert! (function-symbolp 'myequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PARENTS input:

(must-fail (fty::defbyte byte :size 8 :parents "123"))

(must-succeed (fty::defbyte byte :size 8 :parents nil))

(must-succeed (fty::defbyte byte :size 8 :parents (this that)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :SHORT input:

(must-fail (fty::defbyte byte :size 8 :short 'something))

(must-succeed (fty::defbyte byte :size 8 :short nil))

(must-succeed (fty::defbyte byte :size 8 :short "Short doc."))

(must-succeed
 (fty::defbyte byte :size 8 :short (concatenate 'string "Short" " " "doc.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :LONG input:

(must-fail (fty::defbyte byte :size 8 :long #\a))

(must-succeed (fty::defbyte byte :size 8 :long nil))

(must-succeed (fty::defbyte byte :size 8 :long "<p>More doc.</p>"))

(must-succeed (fty::defbyte byte :size 8 :long (xdoc::topstring-p "More doc.")))
