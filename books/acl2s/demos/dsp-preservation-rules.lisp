(in-package "ACL2")
(include-book "acl2s/cgen/top" :dir :system :ttags :all)
(acl2s-defaults :set testing-enabled :naive)
(acl2s-defaults :set :use-fixers t)
(acl2s-defaults :set :recursively-fix nil)
(acl2s-defaults :set :sampling-method :uniform-random)
(acl2s-defaults :set num-trials 1000)
(acl2s-defaults :set verbosity-level 3)
(acl2s-defaults :set num-witnesses 0)
(include-book "dsp-defuns" :ttags :all)
;(include-book "dsp-defthms" :ttags :all)
(include-book "dsp-type-and-fixer-defuns" :ttags :all)


; PRESERVATION RULES w/o these you get 22 vac, while with we get 17. hmm

(cgen::define-rule nodep-preserved-by-nodep-fx2
  :hyp (graphp g)
  :rule (implies (nodep u g)
                 (let ((g (node-fx2 n g)))
                   (nodep u g)))
  :rule-classes :preservation)

(cgen::define-rule nodep-preserved-by-pt-prop-fx
  :hyp (and (vertex-path-alistp pt) (graphp g))
  :rule (implies (nodep x g)
                 (mv-let (pt g) (pt-propertyp-fix2 a pt g)
                         (nodep x g)))
  :rule-classes :preservation)

(cgen::define-rule nodep-preserved-by-path-from-to-fx
  :hyp (and (vertex-listp p) (graphp g))
  :rule (implies (nodep x g)
                 (mv-let (p g) (path-from-to-fix p a b g)
                         (nodep x g)))
  :rule-classes :preservation)

(cgen::define-rule nodep-preserved-by-fsp-fix
; it does not delete nodes, only edges.
  :hyp (and (graphp g) (vertexp u) (vertex-path-alistp pt) (source-vertexp a))
  :rule (implies (nodep u g)
                 (mv-let (pt g) (fs-propertyp-fix3 a fs fs0 pt g)
                         (nodep u g)))
  :rule-classes :preservation)

(cgen::define-rule nodep-preserved-by-invp-fix
  :hyp (and (graphp g) (vertexp u) (vertex-path-alistp pt) (source-vertexp a)
            (vertex-listp ts)
            (my-subsetp ts (all-nodes g)))
  :rule (implies (nodep u g) 
                 (mv-let (pt g) (invp-fx ts pt g a)
                         (nodep u g)))
  :rule-classes :preservation)


(cgen::define-rule path-from-to-preserved-by-pt-prop-fx
  :hyp (and (vertex-path-alistp pt) (graphp g) (vertexp x1) (vertexp x2))
  :rule (implies (pathp-from-to p x1 x2 g)
                 (mv-let (PT G) (PT-PROPERTYP-FIX2 A PT G)
                         (pathp-from-to p x1 x2 g)))
  :rule-classes :preservation)

(cgen::define-rule path-from-to-preserved-by-fs-prop-fx
                   :hyp (and (vertex-path-alistp pt) (graphp g)
                             (vertexp x1) (vertexp x2)
                             )
  :rule (implies (pathp-from-to p x1 x2 g)
                 (mv-let (pt g) (fs-propertyp-fix3 a fs fs0 pt g)
                         (pathp-from-to p x1 x2 g)))
  :rule-classes :preservation)



(cgen::define-rule path-in-pt-preserved-by-pt-prop-fx
  :hyp (and (vertex-path-alistp pt) (graphp g) (source-vertexp a) (vertexp u))
  :rule (implies (path u pt)
                 (mv-let (PT G) (PT-PROPERTYP-FIX2 A PT G)
                         (path u pt)))
  :rule-classes :preservation)

;; (cgen::define-rule eq-path-a-in-pt-preserved-by-pt-prop-fx
;;                    :hyp (and (graphp g) (vertex-path-alistp pt) (source-vertexp a)
;;                              (vertex-listp vs)
;;                              (vertexp u) (pathp-from-to vs a u g))
;;   :rule (implies (equal (path u pt) vs) 
;;                  (mv-let (pt g) (pt-propertyp-fix2 a pt g)
;;                          (equal (path u pt) vs)))
;;   :rule-classes :preservation)

(cgen::define-rule pt-propertyp-preserved-by-tsp-fix
  :hyp (and (graphp g) (vertex-path-alistp pt) (source-vertexp a))
  :rule (implies (pt-propertyp a pt g)
                 (let ((pt (ts-propertyp-fix a ts fs pt g)))
                   (pt-propertyp a pt g)))
  :rule-classes :preservation)


(cgen::define-rule pt-propertyp-preserved-by-fsp-fix
  :hyp (and (graphp g) (vertex-path-alistp pt) (source-vertexp a))
  :rule (implies (pt-propertyp a pt g)
                 (mv-let (pt g) (fs-propertyp-fix3 a fs fs0 pt g)
                         (pt-propertyp a pt g)))
  :rule-classes :preservation)

(cgen::define-rule fsp-fix-preserves-path-a-pt ; hack
                   :hyp (and (graphp g) (vertex-path-alistp pt) (source-vertexp a))
  :rule (implies (equal (path A pt) (CONS A 'NIL))
                 (mv-let (pt g) (fs-propertyp-fix3 a fs fs0 pt g)
                         (equal (path A pt) (CONS A 'NIL))))
  :rule-classes :preservation)

(cgen::define-rule fsp-fix-preserves-path-a-pt1 ; hack
  :hyp (and (graphp g) (vertex-path-alistp pt) (source-vertexp a))
  :rule (implies (equal (CONS A 'NIL) (path A pt))
                 (mv-let (pt g) (fs-propertyp-fix3 a fs fs0 pt g)
                         (equal (CONS A 'NIL) (path A pt))))
  :rule-classes :preservation)

(cgen::define-rule invp-fix-preserves-path-a-pt ; hack
  :hyp (and (graphp g) (1ertex-path-alistp pt) (source-vertexp a))

  :rule (implies (equal (path A pt) (CONS A 'NIL)) 
                 (mv-let (pt g) (invp-fx ts pt g a)
                         (equal (path A pt) (CONS A 'NIL))))
  :rule-classes :preservation)

(cgen::define-rule invp-fix-preserves-path-a-pt1 ; hack
                   :hyp (and (graphp g) (vertex-path-alistp pt) (source-vertexp a))

  :rule (implies (equal (CONS A 'NIL) (path A pt)) 
                 (mv-let (pt g) (invp-fx ts pt g a)
                         (equal (CONS A 'NIL) (path A pt))))
  :rule-classes :preservation)



