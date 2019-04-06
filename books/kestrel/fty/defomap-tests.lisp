; FTY -- Omap Fixtype Generator -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defomap")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string)
 (assert! (function-symbolp 'nat-string-map-p (w state)))
 (assert! (function-symbolp 'nat-string-map-fix (w state)))
 (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :pred nat-string-mapp)
 (assert! (function-symbolp 'nat-string-mapp (w state)))
 (assert! (function-symbolp 'nat-string-map-fix (w state)))
 (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :fix nat-string-mfix)
 (assert! (function-symbolp 'nat-string-map-p (w state)))
 (assert! (function-symbolp 'nat-string-mfix (w state)))
 (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :equiv nat-string-mequiv)
 (assert! (function-symbolp 'nat-string-map-p (w state)))
 (assert! (function-symbolp 'nat-string-map-fix (w state)))
 (assert! (function-symbolp 'nat-string-mequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :parents (fty::defomap omap::omaps)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :short "short"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :short (concatenate 'string "sh" "ort")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :long "long"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :long (concatenate 'string "lo" "ng")))
