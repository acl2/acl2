; Typed Osets -- Fixtype Generator -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defset")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
              :elt-type nat)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
              :elt-type nat
              :pred nat-setp)
 (assert! (function-symbolp 'nat-setp (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
              :elt-type nat
              :fix nat-sfix)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-sfix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
              :elt-type nat
              :equiv nat-sequiv)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-sequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
              :elt-type nat
              :pred nat-setp
              :fix nat-sfix
              :equiv nat-sequiv)
 (assert! (function-symbolp 'nat-setp (w state)))
 (assert! (function-symbolp 'nat-sfix (w state)))
 (assert! (function-symbolp 'nat-sequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset nat-set
              :elt-type nat
              :parents (fty::defset set::std/osets)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset nat-set
              :elt-type nat
              :short "short"))

(must-succeed
 (fty::defset nat-set
              :elt-type nat
              :short (concatenate 'string "sh" "ort")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset nat-set
              :elt-type nat
              :long "long"))

(must-succeed
 (fty::defset nat-set
              :elt-type nat
              :long (concatenate 'string "lo" "ng")))
