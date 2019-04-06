; FTY -- Alias Generator -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "deffixtype-alias")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::deffixtype-alias nat2 nat
   :pred nat2p
   :fix nat2-fix
   :equiv nat2-equiv)
 (fty::defprod use-alias ((a nat) (b nat2))))

(must-succeed*
 (fty::deffixtype-alias nat2 nat
   :fix nat2-fix
   :equiv nat2-equiv)
 (fty::defprod use-alias ((a nat) (b nat2))))

(must-succeed*
 (fty::deffixtype-alias nat2 nat
   :pred nat2p
   :equiv nat2-equiv)
 (fty::defprod use-alias ((a nat) (b nat2))))

(must-succeed*
 (fty::deffixtype-alias nat2 nat
   :pred nat2p
   :fix nat2-fix)
 (fty::defprod use-alias ((a nat) (b nat2))))

(must-succeed*
 (fty::deffixtype-alias nat2 nat
   :pred nat2p)
 (fty::defprod use-alias ((a nat) (b nat2))))

(must-succeed*
 (fty::deffixtype-alias nat2 nat
   :fix nat2-fix)
 (fty::defprod use-alias ((a nat) (b nat2))))

(must-succeed*
 (fty::deffixtype-alias nat2 nat
   :equiv nat2-equiv)
 (fty::defprod use-alias ((a nat) (b nat2))))

(must-succeed*
 (fty::deffixtype-alias nat2 nat)
 (fty::defprod use-alias ((a nat) (b nat2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (fty::defprod 2dpoint ((xx int) (yy int)))

 (fty::deffixtype-alias point 2dpoint
   :pred pointp
   :fix point-fix
   :equiv point-equiv)

 (fty::defprod segment ((start pointp) (end pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (fty::deftagsum onetwo (:one ((get string))) (:two ((get true-list))))

 (fty::deffixtype-alias one/two onetwo
   :pred one/two-p
   :fix one/two-fix
   :equiv one/two-equiv)

 (fty::deftagsum one/two/three (:one/two ((get one/two))) (:three ((get int)))))
