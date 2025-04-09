; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/fty/defresult" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ modes
  :parents (static-semantics dynamic-semantics)
  :short "Modes."
  :long
  (xdoc::topstring
   (xdoc::p
    "[Yul: Specification of Yul: Formal Specification] introduces
     the notion of mode, which indicates how a statement completes execution."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum mode
  :short "Fixtype of modes."
  :long
  (xdoc::topstring
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
  :short "Fixtype of sets of modes."
  :elt-type mode
  :elementp-of-nil nil
  :pred mode-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult mode-set-result
  :parents (static-semantics dynamic-semantics)
  :short "Fixtype of errors and sets of modes."
  :ok mode-set
  :pred mode-set-resultp)
