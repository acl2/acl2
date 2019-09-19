; FTY -- Oset Fixtype Generator -- Tests
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
   :elt-type nat
   :elementp-of-nil nil)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :pred nat-setp)
 (assert! (function-symbolp 'nat-setp (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :fix nat-sfix)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-sfix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :equiv nat-sequiv)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-sequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
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
   :elementp-of-nil nil
   :parents (fty::defset set::std/osets)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :short "short"))

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :short (concatenate 'string "sh" "ort")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :long "long"))

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :long (concatenate 'string "lo" "ng")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset sym-set
   :elt-type symbol
   :elementp-of-nil t))
