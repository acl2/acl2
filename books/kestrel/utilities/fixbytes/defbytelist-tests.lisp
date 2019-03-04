; Fixtypes of True Lists of Unsigned and Signed Bytes -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defbytelist")

(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test successful calls with default options:

(must-succeed*
 (fty::defbyte 8)
 (fty::defbytelist ubyte8)
 (assert! (function-symbolp 'ubyte8-list-p (w state)))
 (assert! (function-symbolp 'ubyte8-list-fix$inline (w state)))
 (assert! (function-symbolp 'ubyte8-list-equiv$inline (w state))))

(must-succeed*
 (fty::defbyte 16 :type word)
 (fty::defbytelist word)
 (assert! (function-symbolp 'word-list-p (w state)))
 (assert! (function-symbolp 'word-list-fix$inline (w state)))
 (assert! (function-symbolp 'word-list-equiv$inline (w state))))

(must-succeed*
 (fty::defbyte 1 :signed t)
 (fty::defbytelist sbyte1)
 (assert! (function-symbolp 'sbyte1-list-p (w state)))
 (assert! (function-symbolp 'sbyte1-list-fix$inline (w state)))
 (assert! (function-symbolp 'sbyte1-list-equiv$inline (w state))))

(must-succeed*
 (defconst *size* 100)
 (fty::defbyte *size*)
 (fty::defbytelist ubyte100)
 (assert! (function-symbolp 'ubyte100-list-p (w state)))
 (assert! (function-symbolp 'ubyte100-list-fix$inline (w state)))
 (assert! (function-symbolp 'ubyte100-list-equiv$inline (w state))))

(must-succeed*
 (define size () 50)
 (fty::defbyte (size) :type mybyte)
 (fty::defbytelist mybyte)
 (assert! (function-symbolp 'mybyte-list-p (w state)))
 (assert! (function-symbolp 'mybyte-list-fix$inline (w state)))
 (assert! (function-symbolp 'mybyte-list-equiv$inline (w state))))

(must-succeed*
 (encapsulate
   (((size) => *))
   (local (defun size () 2))
   (defthm posp-of-size (posp (size))))
 (fty::defbyte (size) :type mybyte)
 (fty::defbytelist mybyte)
 (assert! (function-symbolp 'mybyte-list-p (w state)))
 (assert! (function-symbolp 'mybyte-list-fix$inline (w state)))
 (assert! (function-symbolp 'mybyte-list-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test calls with a bad element type:

(must-fail (fty::defbytelist "string"))

(must-fail (fty::defbytelist (#\x 3/4)))

(must-fail (fty::defbytelist not-even-a-fixtype))

(must-fail (fty::defbytelist nat))

(must-succeed*
 (fty::defbyte 8 :type mybyte)
 (must-fail (fty::defbytelist mybyt)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :TYPE input:

(must-succeed*
 (fty::defbyte 4)
 (must-fail (fty::defbytelist ubyte4 :type #\A)))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :type nibbles)
 (assert! (function-symbolp 'nibbles-p (w state)))
 (assert! (function-symbolp 'nibbles-fix$inline (w state)))
 (assert! (function-symbolp 'nibbles-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PRED input:

(must-succeed*
 (fty::defbyte 4)
 (must-fail (fty::defbytelist ubyte4 :pred 888)))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :pred nibblesp)
 (assert! (function-symbolp 'nibblesp (w state)))
 (assert! (function-symbolp 'ubyte4-list-fix$inline (w state)))
 (assert! (function-symbolp 'ubyte4-list-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :FIX input:

(must-succeed*
 (fty::defbyte 4)
 (must-fail (fty::defbytelist ubyte4 :fix #c(1 2))))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :fix nibfix)
 (assert! (function-symbolp 'ubyte4-list-p (w state)))
 (assert! (function-symbolp 'nibfix$inline (w state)))
 (assert! (function-symbolp 'ubyte4-list-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :EQUIV input:

(must-succeed*
 (fty::defbyte 4)
 (must-fail (fty::defbytelist ubyte4 :equiv (1 1 1))))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :equiv nibeq)
 (assert! (function-symbolp 'ubyte4-list-p (w state)))
 (assert! (function-symbolp 'ubyte4-list-fix$inline (w state)))
 (assert! (function-symbolp 'nibeq$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PARENTS input:

(must-succeed*
 (fty::defbyte 4)
 (must-fail (fty::defbytelist ubyte4 :parents one)))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :parents nil))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :parents (this that)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :SHORT input:

(must-succeed*
 (fty::defbyte 4)
 (must-fail (fty::defbytelist ubyte4 :short #\s)))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :short "Short doc."))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :short (concatenate 'string "Short" " " "doc.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :LONG input:

(must-succeed*
 (fty::defbyte 4)
 (must-fail (fty::defbytelist ubyte4 :long (#\t #\o #\p #\i #\c))))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :long "<p>More doc.</p>"))

(must-succeed*
 (fty::defbyte 4)
 (fty::defbytelist ubyte4 :long (xdoc::topp "More doc.")))
