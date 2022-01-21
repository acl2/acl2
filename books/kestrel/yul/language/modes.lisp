; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/fty/defresult" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum mode
  :parents (static-semantics dynamic-semantics)
  :short "Fixtype of modes."
  :long
  (xdoc::topstring
   (xdoc::p
    "[Yul: Specification of Yul: Formal Specification] introduces
     the notion of mode, which indicates how a statement completes execution.")
   (xdoc::p
    "We disable the executable counterparts of the constructors of this type,
     because we want to treat them abstractly.
     Their definition is already disabled by default, as it should,
     but the fact that their executable counterpart is enabled
     defeats the disabling of their definition, given that they are nullary."))
  (:regular ())
  (:break ())
  (:continue ())
  (:leave ())
  :pred modep
  ///
  (in-theory (disable (:e mode-regular)
                      (:e mode-break)
                      (:e mode-continue)
                      (:e mode-leave))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset mode-set
  :parents (static-semantics dynamic-semantics)
  :short "Fixtype of osets of modes."
  :elt-type mode
  :elementp-of-nil nil
  :pred mode-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult mode-set-result
  :parents (static-semantics dynamic-semantics)
  :short "Fixtype of errors and osets of modes."
  :ok mode-set
  :pred mode-set-resultp)

;;;;;;;;;;;;;;;;;;;;

(defruled not-resulterrp-when-mode-setp
  (implies (mode-setp x)
           (not (resulterrp x)))
  :enable (mode-setp resulterrp))
