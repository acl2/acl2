; FTY -- Byte List Fixtype Generator -- Tests
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
 (fty::defbyte ubyte8 :size 8)
 (fty::defbytelist ubyte8-list :elt-type ubyte8)
 (assert! (function-symbolp 'ubyte8-list-p (w state)))
 (assert! (function-symbolp 'ubyte8-list-fix$inline (w state)))
 (assert! (function-symbolp 'ubyte8-list-equiv$inline (w state))))

(must-succeed*
 (fty::defbyte word :size 16)
 (fty::defbytelist word-list :elt-type word)
 (assert! (function-symbolp 'word-list-p (w state)))
 (assert! (function-symbolp 'word-list-fix$inline (w state)))
 (assert! (function-symbolp 'word-list-equiv$inline (w state))))

(must-succeed*
 (fty::defbyte sbyte1 :size 1 :signed t)
 (fty::defbytelist sbyte1-list :elt-type sbyte1)
 (assert! (function-symbolp 'sbyte1-list-p (w state)))
 (assert! (function-symbolp 'sbyte1-list-fix$inline (w state)))
 (assert! (function-symbolp 'sbyte1-list-equiv$inline (w state))))

(must-succeed*
 (defconst *size* 100)
 (fty::defbyte ubyte100 :size *size*)
 (fty::defbytelist ubyte100-list :elt-type ubyte100)
 (assert! (function-symbolp 'ubyte100-list-p (w state)))
 (assert! (function-symbolp 'ubyte100-list-fix$inline (w state)))
 (assert! (function-symbolp 'ubyte100-list-equiv$inline (w state))))

(must-succeed*
 (define size () 50)
 (fty::defbyte mybyte :size (size))
 (fty::defbytelist mybyte-list :elt-type mybyte)
 (assert! (function-symbolp 'mybyte-list-p (w state)))
 (assert! (function-symbolp 'mybyte-list-fix$inline (w state)))
 (assert! (function-symbolp 'mybyte-list-equiv$inline (w state))))

(must-succeed*
 (encapsulate
   (((size) => *))
   (local (defun size () 2))
   (defthm posp-of-size (posp (size))))
 (fty::defbyte mybyte :size (size))
 (fty::defbytelist mybyte-list :elt-type mybyte)
 (assert! (function-symbolp 'mybyte-list-p (w state)))
 (assert! (function-symbolp 'mybyte-list-fix$inline (w state)))
 (assert! (function-symbolp 'mybyte-list-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the TYPE input:

(must-succeed*
 (fty::defbyte ubyte4 :size 4)
 (must-fail (fty::defbytelist #\A :elt-type ubyte4)))

(must-succeed*
 (fty::defbyte ubyte4 :size 4)
 (fty::defbytelist nibbles :elt-type ubyte4)
 (assert! (function-symbolp 'nibbles-p (w state)))
 (assert! (function-symbolp 'nibbles-fix$inline (w state)))
 (assert! (function-symbolp 'nibbles-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :ELT-TYPE input:

(must-fail (fty::defbytelist byte-list :elt-type "string"))

(must-fail (fty::defbytelist byte-list :elt-type (#\x 3/4)))

(must-fail (fty::defbytelist byte-list :elt-type not-even-a-fixtype))

(must-fail (fty::defbytelist byte-list :elt-type nat))

(must-succeed*
 (fty::defbyte mybyte :size 8)
 (must-fail (fty::defbytelist mybyte-list :elt-type mybyt)))

(must-succeed*
 (fty::defbyte mybyte :size 5)
 (fty::defbytelist mybyte-list :elt-type mybyte)
 (assert! (mybyte-list-p '(0 1 31)))
 (assert! (not (mybyte-list-p '(32)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PRED input:

(must-succeed*
 (fty::defbyte byte :size 4)
 (must-fail (fty::defbytelist bytes :elt-type byte :pred 888)))

(must-succeed*
 (fty::defbyte ubyte4 :size 4)
 (fty::defbytelist ubyte4-list :elt-type ubyte4 :pred nibblesp)
 (assert! (function-symbolp 'nibblesp (w state)))
 (assert! (function-symbolp 'ubyte4-list-fix$inline (w state)))
 (assert! (function-symbolp 'ubyte4-list-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :FIX input:

(must-succeed*
 (fty::defbyte byte :size 4)
 (must-fail (fty::defbytelist bytes :elt-type byte :fix #c(1 2))))

(must-succeed*
 (fty::defbyte ubyte4 :size 4)
 (fty::defbytelist ubyte4-list :elt-type ubyte4 :fix nibfix)
 (assert! (function-symbolp 'ubyte4-list-p (w state)))
 (assert! (function-symbolp 'nibfix$inline (w state)))
 (assert! (function-symbolp 'ubyte4-list-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :EQUIV input:

(must-succeed*
 (fty::defbyte ubyte4 :size 4)
 (must-fail (fty::defbytelist ubyte4-list :elt-type ubyte4 :equiv (1 1 1))))

(must-succeed*
 (fty::defbyte ubyte4 :size 4)
 (fty::defbytelist ubyte4-list :elt-type ubyte4 :equiv nibeq)
 (assert! (function-symbolp 'ubyte4-list-p (w state)))
 (assert! (function-symbolp 'ubyte4-list-fix$inline (w state)))
 (assert! (function-symbolp 'nibeq$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PARENTS input:

(must-succeed*
 (fty::defbyte byte :size 4)
 (must-fail (fty::defbytelist byte-list :elt-type byte :parents one)))

(must-succeed*
 (fty::defbyte byte :size 4)
 (fty::defbytelist byte-list :elt-type byte :parents nil))

(must-succeed*
 (fty::defbyte byte :size 4)
 (fty::defbytelist byte-list :elt-type byte :parents (this that)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :SHORT input:

(must-succeed*
 (fty::defbyte byte :size 4)
 (must-fail (fty::defbytelist bytes :elt-type byte :short #\s)))

(must-succeed*
 (fty::defbyte byte :size 4)
 (fty::defbytelist bytes :elt-type byte :short "Short doc."))

(must-succeed*
 (fty::defbyte byte :size 4)
 (fty::defbytelist bytes
                   :elt-type byte
                   :short (concatenate 'string "Short" " " "doc.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :LONG input:

(must-succeed*
 (fty::defbyte byte :size 4)
 (must-fail (fty::defbytelist bytes
                              :elt-type byte
                              :long (#\t #\o #\p #\i #\c))))

(must-succeed*
 (fty::defbyte byte :size 4)
 (fty::defbytelist bytes :elt-type byte :long "<p>More doc.</p>"))

(must-succeed*
 (fty::defbyte byte :size 4)
 (fty::defbytelist bytes :elt-type byte :long (xdoc::topstring-p "More doc.")))
