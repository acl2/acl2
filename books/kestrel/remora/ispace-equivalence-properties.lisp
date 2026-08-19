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
  :short "The equivalence of dimensions and lists of dimensions
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-equiv-holds-only-on-shapes/ispaces
  :short "The equivalence of shapes, ispaces, and lists thereof
          holds only on shapes, ispaces, and lists thereof."

  (defthm-shp=-proof-validp-clique-flag
    (defthmd shapep-when-shp=-proof-validp
      (implies (shp=-proof-validp proof concl.shp1 concl.shp2)
               (and (shapep concl.shp1)
                    (shapep concl.shp2)))
      :flag shp=-proof-validp)
    (defthmd shape-listp-when-shps=-proof-validp
      (implies (shps=-proof-validp proof concl.shps1 concl.shps2)
               (and (shape-listp concl.shps1)
                    (shape-listp concl.shps2)))
      :flag shps=-proof-validp)
    (defthmd ispacep-when-isp=-proof-validp
      (implies (isp=-proof-validp proof concl.isp1 concl.isp2)
               (and (ispacep concl.isp1)
                    (ispacep concl.isp2)))
      :flag isp=-proof-validp)
    (defthmd ispace-listp-when-isps=-proof-validp
      (implies (isps=-proof-validp proof concl.isps1 concl.isps2)
               (and (ispace-listp concl.isps1)
                    (ispace-listp concl.isps2)))
      :flag isps=-proof-validp)
    :hints (("Goal" :in-theory (enable shp=-proof-validp
                                       shps=-proof-validp
                                       isp=-proof-validp
                                       isps=-proof-validp
                                       shp=-refl-validp
                                       shp=-symm-validp
                                       shp=-trans-validp
                                       shps=-refl-validp
                                       shps=-symm-validp
                                       shps=-trans-validp
                                       isp=-refl-validp
                                       isp=-symm-validp
                                       isp=-trans-validp
                                       isps=-refl-validp
                                       isps=-symm-validp
                                       isps=-trans-validp
                                       shp=-cong-dims-validp
                                       shp=-cong-append-validp
                                       shp=-cong-splice-validp
                                       isp=-cong-dim-validp
                                       isp=-cong-shape-validp
                                       shps=-cong-cons-validp
                                       isps=-cong-cons-validp
                                       shp=-dims0-validp
                                       shp=-dims2m-validp
                                       shp=-append1-validp
                                       shp=-append3m-validp
                                       shp=-splice0-validp
                                       shp=-splice1m-dim-validp
                                       shp=-splice1m-shape-validp
                                       shp=-append-assoc-validp
                                       shp=-append-id-left-validp
                                       shp=-append-id-right-validp
                                       isp=-ispace-dim-shape-validp))))

  (defruled shapep-when-shp=
    (implies (shp= shp1 shp2)
             (and (shapep shp1)
                  (shapep shp2)))
    :enable (shp= shapep-when-shp=-proof-validp))

  (defruled shape-listp-when-shps=
    (implies (shps= shps1 shps2)
             (and (shape-listp shps1)
                  (shape-listp shps2)))
    :enable (shps= shape-listp-when-shps=-proof-validp))

  (defruled ispacep-when-isp=
    (implies (isp= isp1 isp2)
             (and (ispacep isp1)
                  (ispacep isp2)))
    :enable (isp= ispacep-when-isp=-proof-validp))

  (defruled ispace-listp-when-isps=
    (implies (isps= isps1 isps2)
             (and (ispace-listp isps1)
                  (ispace-listp isps2)))
    :enable (isps= ispace-listp-when-isps=-proof-validp)))
