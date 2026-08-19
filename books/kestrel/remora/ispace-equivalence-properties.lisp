; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence-infrules")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "std/util/defund-sk" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-equivalence-properties
  :parents (static-semantics)
  :short "Properties of ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove properties of the equivalence predicates
     defined via inference rules in
     @(see ispace-equivalence-inference-rules)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-equiv-holds-only-on-dimensions
  :short "The equivalence of dimensions and lists of dimensiont
          holds only on dimensions and lists of dimensions."

  (defthm-dim=-proof-validp-clique-flag
    (defthmd dimp-when-dim=-proof-validp
      (implies (dim=-proof-validp proof concl.dim1 concl.dim2)
               (and (dimp concl.dim1)
                    (dimp concl.dim2)))
      :flag dim=-proof-validp)
    (defthmd dim-listp-when-dims=-proof-validp
      (implies (dims=-proof-validp proof concl.dims1 concl.dims2)
               (and (dim-listp concl.dims1)
                    (dim-listp concl.dims2)))
      :flag dims=-proof-validp)
    :hints (("Goal" :in-theory (enable dim=-proof-validp
                                       dims=-proof-validp
                                       dim=-refl-validp
                                       dim=-symm-validp
                                       dim=-trans-validp
                                       dims=-refl-validp
                                       dims=-symm-validp
                                       dims=-trans-validp
                                       dim=-cong-add-validp
                                       dim=-cong-sub-validp
                                       dim=-cong-mul-validp
                                       dims=-cong-cons-validp
                                       dim=-add0-validp
                                       dim=-add1-validp
                                       dim=-add3m-validp
                                       dim=-mul0-validp
                                       dim=-mul1-validp
                                       dim=-mul3m-validp
                                       dim=-sub2m-validp
                                       dim=-add-comm-validp
                                       dim=-add-assoc-validp
                                       dim=-add-id-validp
                                       dim=-add-inv-validp
                                       dim=-add-const-validp
                                       dim=-mul-comm-validp
                                       dim=-mul-assoc-validp
                                       dim=-mul-id-validp
                                       dim=-mul-const-validp
                                       dim=-distrib-validp))))

  (defruled dimp-when-dim=
    (implies (dim= dim1 dim2)
             (and (dimp dim1)
                  (dimp dim2)))
    :enable (dim= dimp-when-dim=-proof-validp))

  (defruled dim-listp-when-dims=
    (implies (dims= dims1 dims2)
             (and (dim-listp dims1)
                  (dim-listp dims2)))
    :enable (dims= dim-listp-when-dims=-proof-validp)))
