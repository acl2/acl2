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



;DEFTHMS for helping fixer rules

(in-theory (disable vertexp vertex-listp member-equal MEMBER-OF-CONS))

;cgen: mportant rule that helps the above rule to fire
(defthm memberp-implies-consp
  (implies (member x L)
           (consp L))
  :rule-classes (:forward-chaining))


(defthm source-vertex=>vertex
  (implies (source-vertexp x)
           (vertexp x))
  :hints (("Goal" :in-theory (enable source-vertexp vertexp)))
  :rule-classes :forward-chaining)


;note nodep is non-recursive right now
(defthm nodep-implies-g-non-empty ;this helps in firing node-fx1 fixer rule i suppose
  (implies (nodep n g)
           (consp g))
  :rule-classes :forward-chaining)

(defthm pathp-implies-g-non-empty
  (implies (pathp n g)
           (consp g))
  :rule-classes :forward-chaining)

(defthm pathp-aux-implies-g-non-empty
  (implies (pathp-aux n g)
           (consp g))
  :rule-classes :forward-chaining)

(defthm vertex-listp-path ;  get (path u pt) type IMP for firing fxr rules
  (implies (vertex-path-alistp pt)
           (vertex-listp (path u pt)))
  :hints (("Goal" :in-theory (disable vertexp))))

(defthm vertex-listp-path-backup ;  get (path u pt) type IMP for firing fxr rules
  (implies (vertex-path-alistp pt)
           (vertex-listp (cdr (assoc-equal u pt))))
  :hints (("Goal" :use vertex-listp-path)))

(defthm last-vertex-listp-type
  (implies (vertex-listp x)
           (vertex-listp (last x)))
  :hints (("Goal" :in-theory (disable vertexp))))

(defthm comp-set-vertex-listp-type
  (implies (and (vertex-listp ts)
                (vertex-listp vs))
           (vertex-listp (comp-set ts vs)))
  :hints (("Goal" :in-theory (disable vertexp))))

                

;FIXER RULES

(cgen::define-rule del-fx2
  :rule (let ((L (del-fx2 a L1 L)))
          (equal L1 (del a L)))
  :rule-classes :fixer)

(cgen::define-rule memp-fx1
           :hyp (consp L)
           :rule (let ((x (memp-fx1 x L)))
                   (memp x L))
           :rule-classes :fixer)

(cgen::define-rule memp-fx2
  :rule (let ((L (memp-fx2 a L)))
          (memp a L))
  :rule-classes :fixer)

(cgen::define-rule setp-fx
  :rule (let ((X1 (setp-fx X1)))
          (setp X1))
  :rule-classes :fixer)

(cgen::define-rule my-subsetp-fx1
  :rule (let ((X1 (my-subsetp-fx1 X1 X2)))
          (my-subsetp X1 X2))
  :rule-classes :fixer)

(cgen::define-rule my-subsetp-fx2
  :rule (let ((X2 (my-union X1 X2)))
          (my-subsetp X1 X2))
  :rule-classes :fixer)

(cgen::define-rule nodep-fx1
  :hyp (and (graphp g) (vertexp n)) ; add consp g?
  :rule (let ((n (node-fx1 n g)))
          (nodep n g))
  :rule-classes :fixer)

(cgen::define-rule nodep-fx2
  :hyp (and (graphp g) (vertexp n))
  :rule (let ((g (node-fx2 n g)))
          (nodep n g))
  :rule-classes :fixer)

;fresh variable vs introduced
(cgen::define-rule path-non-empty-fix
 :hyp (and (vertex-path-alistp pt) 
           (vertexp u)
           (vertex-listp _vs)) ;free variable
 :rule (let ((pt (path-non-empty-fix u _vs pt)))
         (path u pt))
 :rule-classes :fixer)

(cgen::define-rule path-eq-fx1
  :hyp (and (vertexp x) (vertex-listp vs) (vertex-path-alistp pt))
  :rule (let ((pt (put-assoc-equal x vs pt)))
          (equal vs (path x pt)))
  :rule-classes :fixer)

(cgen::define-rule pathp-from-to-fx
  :hyp (and (graphp g) (vertexp a) (vertexp b)
            (vertex-listp P))
  :rule (mv-let (P g) (path-from-to-fix P a b g)
          (pathp-from-to P a b g))
  :rule-classes :fixer)

;fixer for pathp
(cgen::define-rule path-fx1
  :hyp (and (graphp g) 
            (vertex-listp P))
  :rule (mv-let (P g) (pathp-fx P g)
          (pathp P g))
  :rule-classes :fixer)

(cgen::define-rule pt-propertyp-fix2
  :hyp (and (graphp g) (source-vertexp a) (vertex-path-alistp pt))
  :rule (mv-let (pt g) (pt-propertyp-fix2 a pt g)
                (pt-propertyp a pt g))
  :rule-classes :fixer)

(cgen::define-rule confinedp-fx1
  :rule (let ((p (find-partial-path p fs)))
          (confinedp p fs))
  :rule-classes :fixer)

;; (cgen::define-rule confinedp-fx2 ;not helpful unless you define inverter for (CONS U FS)
;;   :hyp (and (vertex-listp fs) (vertex-listp p))
;;   :rule (let ((fs (my-union (butlast p 1) fs)))
;;           (confinedp p fs))
;;   :rule-classes :fixer)

(cgen::define-rule shortest-confined-pathp-fx
  :hyp (and (graphp g) (source-vertexp a) (vertexp b)
            (vertex-listp fs) (vertex-listp p))
  :rule (let ((p (shortest-confined-path-fxr a b p fs g)))
          (shortest-confined-pathp a b p fs g))
  :rule-classes :fixer)

(cgen::define-rule shortest-pathp-fx
  :hyp (and (graphp g) (source-vertexp a) (vertexp b) (vertex-listp p))
  :rule (let ((p (shortest-path-fxr a b p g)))
          (shortest-pathp a b p g))
  :rule-classes :fixer)

(cgen::define-rule ts-propertyp-fix
  :hyp (and (graphp g) (source-vertexp a)
            (vertex-path-alistp pt) ;important for variability
            ;(pt-propertyp a pt g)
            (vertex-listp fs)
            (vertex-listp ts) ;important for finding cex
            ;(my-subsetp ts (all-nodes g)) fails to preserve once edges are deleted from g
            ;(memp a fs) ;crucual o.w. this rule does not pass!! ok modified ts-p-fix to delete all assoc
            )
  :rule (let ((pt (ts-propertyp-fix a ts fs pt g)))
          (ts-propertyp a ts fs pt g))
  :rule-classes :fixer)

(cgen::define-rule fs-propertyp-fix3
  :hyp (and (graphp g) (source-vertexp a) 
            (vertex-path-alistp pt)
            ;(pt-propertyp a pt g)  ;keep instead the pres rule
            (vertex-listp fs)
            (vertex-listp fs0)
            ;(my-subsetp fs fs0) ;how come fs-prop-fix1 needs it?
            )
  :rule (mv-let (pt g) (fs-propertyp-fix3 a fs fs0 pt g)
                (fs-propertyp a fs fs0 pt g))
  :rule-classes :fixer)



(cgen::define-rule invp-fx
  :hyp (and (graphp g) (source-vertexp a) 
            (vertex-path-alistp pt)
            (vertex-listp ts)
            (my-subsetp ts (all-nodes g)) ;needed for soundness
            )
  :rule (mv-let (pt g) (invp-fx ts pt g a)
                (invp ts pt g a))
  :rule-classes :fixer
  );takes 40 seconds for 1000 test runs!!!
; if i remove my-subsetp ts constraint, we get counterexample:

