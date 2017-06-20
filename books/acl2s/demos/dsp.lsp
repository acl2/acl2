
;------------HEADER START-------------------
(in-package "ACL2")
(include-book "dsp-defuns" :ttags :all)
;(include-book "dsp-defthms" :ttags :all)
(include-book "dsp-type-and-fixer-defuns" :ttags :all)
(include-book "dsp-fixer-rules" :ttags :all)
(include-book "dsp-preservation-rules" :ttags :all)
(include-book "acl2s/cgen/top" :dir :system :ttags :all)

(acl2s-defaults :set testing-enabled :naive)
(acl2s-defaults :set :use-fixers t)
(acl2s-defaults :set :recursively-fix t)
(acl2s-defaults :set :sampling-method :uniform-random)
(acl2s-defaults :set cgen-local-timeout 0); takes lot of time because of find-all-paths ? why?
(acl2s-defaults :set num-trials 1000)
(acl2s-defaults :set verbosity-level 3)
(acl2s-defaults :set num-witnesses 0)

;(include-book "misc/profiling" :dir :system)
;-------------HEADER END-----------------------

;(memoize 'find-all-simple-paths :ideal-okp t)
(TABLE ACL2-DEFAULTS-TABLE :MEMOIZE-IDEAL-OKP T)
(profile 'pathp-from-to)

(make-event (er-progn 
             (mv-let (start state) 
                     (acl2::read-run-time state)
                     (assign start-time start))
             (value '(value-triple :ok))))
        

; TEST? EVENTS

;(set-fmt-hard-right-margin 100 state)

; TODO? pt-propertyp not being preserved.
(test? ;pathp-from-to-path-1 ; [Custom]
 (implies (and (graphp g) (source-vertexp a) (vertexp u)
               (vertex-path-alistp pt) ;types

               (pt-propertyp a pt g)
               (path u pt))
          (pathp-from-to (path u pt) a u g)))


(test? ; prop-path-nil ; [Custom]
(implies (and (source-vertexp a) (vertex-listp s) (graphp g) ;types
              )
  (ts-propertyp a s nil (list (cons a (list a))) g)))

(test? ; comp-set-subset
  (implies (my-subsetp s1 s2) ;47
           (not (comp-set s2 s1))))
  
(test? ;subsetp-cons
  (implies (my-subsetp x y) ;49.3
           (my-subsetp x (cons e y))))

(test? ;subsetp-x-x
  (my-subsetp x x))

(test? ;comp-set-id
  (equal (comp-set s s) nil))



(test? ; invp-0 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) ;added o.w. cexample
                (nodep a g) ;0.10
                ) 
           (invp (all-nodes g) (list (cons a (list a))) g a))
)

;====================================================================
(test? ;subset-union
  (implies (or (my-subsetp s1 s2) (my-subsetp s1 s3)) ;48.20
           (my-subsetp s1 (my-union s2 s3))))

(test? ;memp-subset-memp-temp
  (implies (and (memp a s) ;0.80
                (my-subsetp s r)) ;49.40
           (memp a r)))

(test? ; neighbor-implies-nodep
 (implies (and  (graphp g) (vertexp u) (vertexp v) ;types
                (memp v (neighbors u g))) ;0.10
           (memp v (all-nodes g))))

(test? ; paths-table-reassign-lemma2
  (implies (and (graphp g) (vertex-listp p) ;types
                (pathp p g) ;0 if g not given type, 2.40% if given
                (memp v (neighbors (car (last p)) g))) ;0%
           (pathp (append p (list v)) g)))


(test? ; paths-table-reassign-lemma4 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt) (vertexp u) ;types
                (pt-propertyp a pt g) ;18.80
                (path u pt) ;1.90
                (memp v (neighbors u g))) ;0
           (pathp-from-to (append (path u pt) (list v))
                         a v g)))

(include-book "misc/eval" :dir :system)
;faulty flawed conjecture shown in dissertation chapter 5 motivation
;that is a modification of the above lemma.
(must-fail
(test? ; paths-table-reassign-lemma4 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt) (vertexp u) ;types
                (pt-propertyp a pt g) ;18.80
                (path u pt) ;1.90
                (memp v (neighbors u g))) ;0
           (pathp-from-to (append (path u pt) (list u v))
                         a v g)))
)


(test? ;path-len-implies-not-nil
 (implies (and (graphp g) (vertex-path-alistp pt) (vertexp u) ;types
               (path-len (path u pt) g)) ;0.20
          (path u pt)))


(test? ; edge-len-implies-neighbors
  (implies (and (graphp g) (vertexp v) (vertexp u) ;types
                (edge-len u v g)) ;0.30
                (memp v (neighbors u g))))


(test? ; pt-propertyp-reassign ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt) ;types
                (pt-propertyp a pt g);16
                (my-subsetp v-lst (all-nodes g)));49.40
           (pt-propertyp a (reassign u v-lst pt g) g)))
  

;=====================================================================
(test? ; shortest-pathp-corollary
  (implies (and (graphp g) (vertex-listp path) (vertex-listp p) ;types
                (source-vertexp a) (vertexp b)   ;types
                (shortest-pathp a b p g) ;99
                (pathp-from-to path a b g)) ;0
           (shorterp p path g)))


(test? ; shortest-implies-unchanged-lemma1 ; [Custom]
 (implies (and (vertex-listp path) (vertex-listp p) ;types
                (vertexp u) (vertexp v)) ;types
          (equal (path v (cons (cons u path) pt))
                 (if (equal v u) path
                   (path v pt)))))

(test? ;memp-implies-memp-union-1
 (implies (memp u s1) ;1.10
          (memp u (my-union s1 s2))))

(test? ;memp-implies-memp-union-2
    (implies (memp u s2) ;0.6
             (memp u (my-union s1 s2))))

(test? ;not-memp-edge-len-lemma
  (implies (assoc v alst) ;4.30
           (memp v (strip-cars alst))))

(test? ;not-memp-edge-len
  (implies (not (memp v (all-nodes g))) ;95.90
           (not (edge-len a v g))))



(test? ; path-len-append
  (implies (and (graphp g) (vertex-listp p) (vertexp v) ;types
                (pathp p g)) ;3.5
           (equal (path-len (append p (list v)) g)
                  (plus (path-len p g)
                        (edge-len (car (last p)) v g)))))



(test? ; pathp-implies-true-listp
  (implies (and (graphp g) (vertex-listp p) ;types
                (pathp p g)) ;3.5
           (true-listp p)))


(test? ; shortest-implies-unchanged ; [Custom]
  (implies (and (source-vertexp a) (graphp g)  (vertexp v) (vertex-path-alistp pt) ;types 
                (shortest-pathp a v (path v pt) g) ;99.90 ;TODO not being fixed
                (pt-propertyp a pt g) ;18.90
                (nodep v g)) ;11.10
           (equal (path v (reassign u v-lst pt g))
                  (path v pt))))
  
;=====================================================================
(test? ; fs-propertyp-memp ; [Custom]
  (implies (and (graphp g) (vertexp v) (source-vertexp a) ;types 
                (vertex-path-alistp pt) (vertex-listp s) (vertex-listp fs) ;types 
                (fs-propertyp a fs s pt g) ;93.70
                (memp v fs)) ;3.80
           (and (shortest-pathp a v (path v pt) g)
                (confinedp (path v pt) s))))

(test? ; fs-propertyp-memp-lemma ; [Custom]
  (implies (and (graphp g) (vertexp v) (vertexp u)  (source-vertexp a) ;types  
                (vertex-path-alistp pt) (vertex-listp s) (vertex-listp fs) ;types
                (my-subsetp fs (all-nodes g))
                (fs-propertyp a fs s pt g) ;94 
                (pt-propertyp a pt g) ;18
                (memp v fs)) ;3
           (equal (path v (reassign u (neighbors u g) pt g))
                  (path v pt))))
  
(test? ; fs-propertyp-choose-next-lemma1 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertexp u) ;types
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp s);types
                (fs-propertyp a fs s pt g) ;93.8
                (pt-propertyp a pt g) ;18.2
                (my-subsetp fs (all-nodes g))) ;3
           (fs-propertyp a fs s (reassign u (neighbors u g) pt g) g)))
  
(test? ; fs-propertyp-choose-lemma2 ; [Custom]
 (implies (and (graphp g) (source-vertexp a) (vertexp u)  ;types
                 (vertex-path-alistp pt) (vertex-listp s) (vertex-listp fs) ;types
                (fs-propertyp a fs s pt g) ;93.7
                (my-subsetp fs (all-nodes g)) ;4.10
                (confinedp (path u pt) s) ;99
                (pt-propertyp a pt g) ;17.30 TODO -- BUG!! (path u pt) equation UNSAT
                (nodep u g) ;11.90
                (shortest-pathp a u (path u pt) g)) ;99.90
           (fs-propertyp a (cons u fs) s
                         (reassign u (neighbors u g) pt g)
                         g)))


(test? ; fs-propertyp-choose-lemma3 ; [Custom]
  (implies (and (graphp g)  (source-vertexp a) ;types
                (vertex-path-alistp pt) (vertex-listp s) (vertex-listp ss) (vertex-listp fs) ;types
                (my-subsetp s fs) ;0.60
                (my-subsetp fs (all-nodes g)) ;3.70
                (pt-propertyp a pt g) ;17.10
                (fs-propertyp a fs ss pt g)) ;93.80
           (fs-propertyp a s ss pt g)))

(test? ; fs-propertyp-choose-lemma4-lemma ; [Custom]
  (implies (and (my-subsetp s ss)
                (confinedp p s))
           (confinedp p ss)))

(test? ; fs-propertyp-choose-lemma4 ; [Custom]
  (implies (and (graphp g) (source-vertexp a)  ;types
                 (vertex-path-alistp pt) (vertex-listp s) (vertex-listp ss) (vertex-listp fs) ;types
                (my-subsetp s ss)
                (my-subsetp s (all-nodes g))
                (my-subsetp fs (all-nodes g))
                (fs-propertyp a fs s pt g))
           (fs-propertyp a fs ss pt g)))

(defun find-partial-path (p s)
  (if (endp p) nil
    (if (memp (car p) s)
        (cons (car p) (find-partial-path (cdr p) s))
      (list (car p)))))

(test? ; edge-listp-values-positive
  (implies (and (edge-listp a)
                (cdr (assoc-equal b a)))
           (<= 0 (cdr (assoc-equal b a))))
  :rule-classes :linear)

(test? ; graph-weight-nonneg
  (implies (and (graphp g)
                (edge-len a b g))
           (<= 0 (edge-len a b g)))
  :rule-classes :linear)


(test? ; graph-path-weight-nonneg
  (implies (and (graphp g)
                (path-len p g))
           (<= 0 (path-len p g)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable edge-len))))


(test? ; edge-len-implies-nodep
  (implies (edge-len a b g)
           (memp a (all-nodes g))))



(test?;  notnodep-necc
  (implies (not (nodep a g))
           (not (neighbors a g))))


(test? ; pathp-implies-car-nodep
  (implies (and (graphp g) (vertex-listp p)
                (pathp p g))
           (memp (car p) (all-nodes g))))



(test? ; pathp-partial-path
  (implies (and (graphp g) (vertex-listp p) (vertex-listp s) ;types
                (pathp p g))
           (and (pathp-from-to (find-partial-path p s) (car p)
                              (car (last (find-partial-path p s))) g)
                (confinedp (find-partial-path p s) s))))


(test? ; shorterp-trans
  (implies (and (graphp g) (vertex-listp p1) (vertex-listp p2) (vertex-listp p3) ;types
                (shorterp p1 p2 g) ;97.60
                (shorterp p2 p3 g)) ;96
           (shorterp p1 p3 g)))


(test? ; shorterp-by-partial-trans
  (implies (and (vertex-listp path) (vertex-listp path) (vertex-listp s)
                (shorterp p (find-partial-path path s) g)
                (graphp g))
           (shorterp p path g)))


;TODO ts-prop sat with high rate
(test? ; ts-propertyp-prop-lemma1 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertexp v) ;types
                (vertex-path-alistp pt) (vertex-listp ts) (vertex-listp fs) ;types
                (ts-propertyp a ts fs pt g) ;95.50 ;
                (memp v ts)) ;2.40
           (and (shortest-confined-pathp a v (path v pt) fs g)
                (confinedp (path v pt) fs))))



(test? ; ts-propertyp-prop-lemma2 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertexp b) 
                (vertex-listp p) (vertex-listp path) (vertex-listp fs)   
                
                (pathp-from-to path a b g) ;0
                (shortest-confined-pathp a b p fs g) ;99
                (confinedp path fs)) ;24
           (shorterp p path g)))

(test? ; ts-propertyp-prop ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertexp v) 
                 (vertex-path-alistp pt) (vertex-listp path) (vertex-listp ts) (vertex-listp fs)    
                
                (ts-propertyp a ts fs pt g)
                (confinedp path fs)
                (pathp-from-to path a v g)
                (memp v ts))
           (and (shorterp (path v pt) path g)
                (confinedp (path v pt) fs))))

(test? ; shorterp-by-partial-and-choose-next ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertexp u) (vertexp v) 
                (vertex-path-alistp pt) (vertex-listp path) (vertex-listp ts) ;types   
                (vertex-listp (all-nodes g)) ;types
                
                (shorterp (path u pt) (path v pt) g)
                (memp v ts)
                (ts-propertyp a ts (comp-set ts (all-nodes g)) pt g)
                (pathp-from-to path a v g)
                (confinedp path (comp-set ts (all-nodes g))))
           (shorterp (path u pt) path g)))

(test? ; choose-next-shorterp-other ; [Custom]
  (implies (and (graphp g) (vertexp v) 
                (vertex-path-alistp pt)  (vertex-listp ts) ;types   
                
                (memp v ts))
           (shorterp (path (choose-next ts pt g) pt)
                    (path v pt) g)))

(test? ; not-comp-set-id
  (implies (memp v all)
           (iff (memp v (comp-set ts all))
                (not (memp v ts)))))

(test? ; find-partial-path-last-memp
  (implies (and (graphp g) (vertex-listp p) (vertex-listp ts) ;types   
                (memp (car (last p)) ts)
                (pathp p g)
                (my-subsetp ts (all-nodes g)))
           (memp (car (last (find-partial-path p (comp-set ts (all-nodes g)))))
                ts)))



(test? ; choose-next-shortest-lemma ; [Custom]
  (implies (and (graphp g) (vertex-path-alistp pt) (vertex-listp ts) ;types   
                (consp ts))
           (memp (choose-next ts pt g) ts)))

(test? ; choose-next-shortest ; [Custom] ;WHY
  (implies (and (graphp g) (source-vertexp a)
                (vertex-path-alistp pt) (vertex-listp ts) ;types   
                
                (consp ts)
                (my-subsetp ts (all-nodes g)) ;3.40
                (invp ts pt g a)) ;13.70
           (shortest-pathp a (choose-next ts pt g)
                           (path (choose-next ts pt g) pt) g)))
  


(test? ; choose-next-confinedp ; [Custom]
  (implies (and (graphp g) (source-vertexp a)
                (vertex-path-alistp pt) (vertex-listp ts) ;types   
                
                (invp ts pt g a)
                (consp ts)
                (my-subsetp ts (all-nodes g)))
           (confinedp (path (choose-next ts pt g) pt)
                              (comp-set ts (all-nodes g)))))
  
(test? ;subsetp-comp-set-all
  (my-subsetp (comp-set ts all) all))

(test? ;subsetp-del
  (my-subsetp (del u ts) ts))

(test? ;cons-subsetp-comp-set-del-lemma
  (my-subsetp (comp-set ts all)
              (comp-set (del u ts) all)))

(test? ;subsetp-comp-set-del-lemma1
  (implies (my-subsetp s1 (cons v s2))
           (my-subsetp s1
                       (list* v u s2))))

(test? ;subsetp-comp-set-del-lemma2
  (implies (and (memp v ts)
                (not (equal v u)))
           (memp v (del u ts))))

(test? ;subsetp-comp-set-del
  (implies (and (setp ts)
                (setp all))
           (my-subsetp (comp-set (del u ts) all)
                       (cons u (comp-set ts all)))))

(test? ;edge-listp-prop
  (implies (and (edge-listp lst)
                (not (assoc u lst)))
           (not (memp u (strip-cars lst)))))

(test? ;edge-listp-implies-setp
  (implies (edge-listp lst)
           (setp (strip-cars lst))))

(test? ;not-memp-union
  (implies (and (not (memp u s1))
                (not (memp u s2)))
           (not (memp u (my-union s1 s2)))))

(test? ;setp-union
  (implies (and (setp s1)
                (setp s2))
           (setp (my-union s1 s2))))

(test? ;setp-all-nodes
  (implies (graphp g)
           (setp (all-nodes g))))

(test? ;memp-subset-memp
  (implies (and (my-subsetp s r)
                (memp a s))
           (memp a r)))

(test? ;neighbors-subsetp-all-nodes
  (my-subsetp (neighbors u g)
              (all-nodes g)))


(test? ; fs-propertyp-choose ; [Custom] WHY?
  (implies (and (graphp g) (source-vertexp a)
                (vertex-path-alistp pt) (vertex-listp ts) ;types   
                
                (invp ts pt g a)
                (my-subsetp ts (all-nodes g))
                (graphp g)
                (consp ts)
                (setp ts))
           (let ((u (choose-next ts pt g)))
             (fs-propertyp a (comp-set (del u ts)
                                       (all-nodes g))
                           (comp-set (del u ts) (all-nodes g))
                           (reassign u (neighbors u g) pt g)
                           g))))
 
;=====================================================================


(test? ; neighbor-implies-edge-len
  (implies (and (graphp g) (vertexp u) (vertexp v) ;types   
                (memp v (neighbors u g)))
           (edge-len u v g)))

(test? ; pathp-implies-path-len
  (implies (and (graphp g) (vertex-listp p)
                (pathp p g))
           (path-len p g)))
  
(test? ; pathpt-iff-path-len ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                (pt-propertyp a pt g))
           (iff (path u pt)
                (path-len (path u pt) g))))

(test? ; reassign-path ; [Custom]
  (implies (and (graphp g) (vertexp v) (vertexp u) (vertex-listp v-lst) (vertex-path-alistp pt) ;types
                (not (memp v v-lst)))
           (equal (path v (reassign u v-lst pt g))
                  (path v pt))))

(test? ; shorterp-reassign-append ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                (vertexp v) (vertexp u) (vertex-listp v-lst) ;types
                (pt-propertyp a pt g)
                (path u pt)
                (memp v v-lst))
           (shorterp (path v (reassign u v-lst pt g))
                    (append (path u pt) (list v)) g)))


                    

(test? ; shorterp-reassign-lemma ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt) (vertexp u) ;types
                (path-len (path u pt) g)
                (pt-propertyp a pt g))
           (and (pathp (path u pt) g)
                (equal (car (path u pt)) a)
                (equal (car (last (path u pt))) u))))

(test? ; shorterp-reassign ; [Custom]
  (implies  (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                 (pt-propertyp a pt g))
           (shorterp (path v (reassign u v-lst pt g))
                    (path v pt) g)))
  
(test? ; true-listp-path ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                (pt-propertyp a pt g))
           (true-listp (path u pt))))





(test? ; pathp-from-to-append ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                (vertexp v) (vertexp w)
                (pt-propertyp a pt g)
                (path w pt)
                (memp v (neighbors w g)))
           (pathp-from-to (append (path w pt)
                                 (list v))
                         a v g)))

(test? ; confinedp-append
  (implies (and (confinedp p s)
                (memp (car (last p)) s))
           (confinedp (append p (list v)) s)))

(test? ; shorterp-than-append-fs ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                (vertexp v) (vertexp w) (vertex-listp s) (vertex-listp fs)
                
                (shortest-confined-pathp a v (path v pt) s g)
                (fs-propertyp a fs s pt g)
                (my-subsetp fs s)
                (path w pt)
                (pt-propertyp a pt g)
                (memp w fs))
           (shorterp (path v pt)
                    (append (path w pt) (list v)) g))
 )

(test? ; path-length
  (implies (and (graphp g) (vertex-listp p)
                (pathp p g)
                (not (equal (car p)
                            (car (last p)))))
           (<= 2 (len p)))
  :rule-classes :linear)

(test? ; pathp-find-last-next
  (implies (and (graphp g) (vertex-listp p)
                (pathp p g)
                (<= 2 (len p)))
           (and (pathp (find-last-next-path p) g)
                (memp (car (last p))
                     (neighbors (car (last (find-last-next-path p))) g))))
 )

(test? ; find-last-implies-all-in
  (implies (and (find-last-next-path p)
                (confinedp p fs))
           (memp (car (last (find-last-next-path p))) fs)))


(test? ; pathp-from-to-implies-all-path
 (implies (and (graphp g) (vertex-listp p) (source-vertexp a) (vertexp v) (vertex-listp fs) 
               (pathp-from-to p a v g)
               (not (equal a v))
               (confinedp p fs))
          (and (memp v (neighbors (last-node p) g))
               (pathp-from-to (find-last-next-path p) a (last-node p) g)
               (memp (last-node p) fs))))

(test? ; path-len-implies-pathp
  (implies (and (graphp g) (vertex-listp p)
                (path-len p g)
                (true-listp p))
           (pathp p g)))


(test? ; shorterp-and-pathp-implies-pathp
  (implies (and (graphp g) (vertex-listp p1) (vertex-listp p2)  
                (shorterp p1 p2 g)
                (true-listp p1)
                (pathp p2 g))
           (pathp p1 g)))

(test? ; shorterp-implies-append-shorterp
  (implies (and (graphp g) (vertex-listp p1) (vertex-listp p2)  
                
                (shorterp p1 p2 g)
                (true-listp p1)
                (equal (car (last p1))
                       (car (last p2)))
                (pathp p2 g))
           (shorterp (append p1 (list v))
                    (append p2 (list v)) g)))
 

(test? ; pathpt-implies-path-last-node ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                (vertexp u) (vertexp v)
                
                (pt-propertyp a pt g)
                (pathp (path u pt) g))
           (equal (car (last (path u pt))) u)))

(test? ; last-node-lemma1 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                (vertexp u) (vertexp v) (vertex-listp p)
                
                (pt-propertyp a pt g)
                (pathp-from-to p a v g)
                (not (equal a v))
                (shortest-pathp a (last-node p) (path (last-node p) pt) g))
           (shorterp (append (path (last-node p) pt) (list v))
                    (append (find-last-next-path p) (list v)) g)))
 

(test? ; last-node-lemma2 ; [Custom]
  (implies (and (graphp g) (vertexp v) (vertex-listp p)
                (equal (car (last p)) v)
                (pathp p g))
           (equal (append (find-last-next-path p) (list v))
                  p)))

(test? ; last-node-lemma ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt)
                (vertexp u) (vertexp v) (vertex-listp p)
                
                (pt-propertyp a pt g)
                (pathp-from-to p a v g)
                (not (equal a v))
                (shortest-pathp a (last-node p) (path (last-node p) pt) g))
           (shorterp (append (path (last-node p) pt) (list v))
                    p g))
 )

(test? ; memp-not-car-implies-memp
  (implies (and (memp v (cons u fs))
                (not (equal v u)))
           (memp v fs)))


(test? ; fs-propertyp-implies-pathp ; [Custom] LOOK nice demonstrative example!!
  (implies (and (graphp g) (source-vertexp a) (vertexp w) 
                 (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp s) (vertex-listp p2)
                 
                (fs-propertyp a fs s pt g)
                (memp w fs)
                (pathp-from-to p2 a w g))
           (path w pt)))

; this example is very instructive for improving the implementation
; non-shallow term (SHORTEST-PATHP A U (PATH U PT) G)) not fixed
(test? ; ts-propertyp-lemma2-1 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertexp u) (vertexp v)
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp p) 
                 
                (shortest-confined-pathp a v (path v pt) fs g)
                (fs-propertyp a fs fs pt g)
                (pathp-from-to p a v g)
                (not (equal a v))
                (path u pt)
                (shortest-pathp a u (path u pt) g)
                (confinedp p (cons u fs))
                (pt-propertyp a pt g))
           (shorterp (path v (reassign u (neighbors u g) pt g)) p g)))
  
;=====================================================================
(defun find-partial-path-to-u (p u)
  (cond ((not (memp u p)) nil)
        ((equal (car p) u) (list u))
        (t (cons (car p)
                 (find-partial-path-to-u (cdr p) u)))))

(test? ; pathp-implies-path-to-u-pathp
  (implies (and (graphp g) (vertexp u) (vertex-listp p) 
                
                (memp u p)
                (pathp p g))
           (pathp-from-to (find-partial-path-to-u p u) (car p) u g)))

(test? ; not-memp-implies-confinedp
  (implies (and (confinedp p (cons u fs))
                (not (memp u p)))
           (confinedp p fs)))

(test? ; nil-shorterp-than-nil
  (implies (and (graphp g) (vertex-listp p1) (vertex-listp p2) 
                (shorterp p1 p2 g)
                (not p1))
           (not (pathp p2 g))))

(test? ; shortest-pathp-nil-implies-lemma
 (implies (and (graphp g) (source-vertexp a) (vertexp u)
               (vertex-listp p1) (vertex-listp p2) 
               (shortest-pathp a u p1 g)
               (not p1)
               (equal (car p2) a)
               (pathp p2 g))
          (not (memp u p2))))

(test? ; ts-propertyp-lemma2-2 ; [Custom]
  (implies (and (graphp g) (source-vertexp a)  (vertexp u)  (vertexp v) 
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp p) 
                
                (shortest-confined-pathp a v (path v pt) fs g)
                (fs-propertyp a fs fs pt g)
                (pathp-from-to p a v g)
                (not (equal a v))
                (shortest-pathp a u (path u pt) g)
                (confinedp p (cons u fs))
                (pt-propertyp a pt g))
           (shorterp (path v (reassign u (neighbors u g) pt g)) p g)))
  

(test? ; shortest-pathp-list-a
  (implies (and (graphp g) (source-vertexp a) ) ;types
           (shortest-pathp a a (list a) g)))

(test? ; path-a-pt ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertexp u)
                (vertex-path-alistp pt) (vertex-listp v-lst)
                
                (pt-propertyp a pt g)
                (graphp g)
                (nodep a g)
                (equal (path a pt) (list a)))
           (equal (path a (reassign u v-lst pt g))
                  (path a pt))))

(test? ; ts-propertyp-lemma2-3 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (nodep a g) (vertexp u) (vertexp v) 
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp p) 
                
                (shortest-confined-pathp a v (path v pt) fs g)
                (fs-propertyp a fs fs pt g)
                (pathp-from-to p a v g)
                (confinedp p (cons u fs))
                (shortest-pathp a u (path u pt) g)
                (pt-propertyp a pt g)
                (equal (path a pt) (list a)))
           (shorterp (path v (reassign u (neighbors u g) pt g)) p g)))

(test? ; ts-propertyp-lemma2 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (nodep a g) (vertexp u) (vertexp v) 
                (vertex-path-alistp pt) (vertex-listp fs)
                
                (shortest-confined-pathp a v (path v pt) fs g)
                (nodep a g)
                (equal (path a pt) (list a))
                (fs-propertyp a fs fs pt g)
                (shortest-pathp a u (path u pt) g)
                (pt-propertyp a pt g))
           (shortest-confined-pathp a v (path v (reassign u (neighbors u g)
                                                         pt g))
                                   (cons u fs) g)))

(test? ; ts-propertyp-lemma3-1
  (implies (confinedp p fs)
           (confinedp p (cons u fs))))

(test? ; ts-propertyp-lemma3-2 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (nodep a g) (vertexp u) (vertexp v)
                (vertex-path-alistp pt) (vertex-listp fs)
                
                (pt-propertyp a pt g)
                (confinedp (path u pt) fs))
           (confinedp (append (path u pt) (list v))
                              (cons u fs))))

(test? ; ts-propertyp-lemma3-3 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (nodep a g) (vertexp u) (vertexp v)
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp v-lst)
                
                (pt-propertyp a pt g)
                (confinedp (path v pt) fs)
                (confinedp (path u pt) fs))
           (confinedp (path v (reassign u v-lst pt g))
                      (cons u fs))))

(test? ; ts-propertyp-prop-lemma ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (nodep a g) (vertexp u) (vertexp v)
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp ts)
                
                (ts-propertyp a ts fs pt g)
                (memp u ts))
           (confinedp (path u pt) fs)))

(test? ; ts-propertyp-lemma3 ; [Custom]
 (implies (and (graphp g) (source-vertexp a) (nodep a g) (vertexp u) (vertexp v) 
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp ts)
                
                (pt-propertyp a pt g)
                (equal (path a pt) (list a)) ;0
                (fs-propertyp a fs fs pt g)
                (ts-propertyp a ts fs pt g)
                (memp u ts)
                (shortest-pathp a u (path u pt) g))
           (ts-propertyp a (del u ts) (cons u fs)
                         (reassign u (neighbors u g) pt g) g)))
 
(test? ; shortest-confined-pathp-subset
  (implies (and (graphp g) (source-vertexp a)  (vertexp u) (vertexp v) 
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp p) (vertex-listp s)
                
                (shortest-confined-pathp a u p fs g)
                (my-subsetp s fs))
           (shortest-confined-pathp a u p s g)))

(test? ; ts-propertyp-lemma1 ; [Custom]
  (implies (and (graphp g) (source-vertexp a)  
                (vertex-path-alistp pt) (vertex-listp fs) (vertex-listp ts) (vertex-listp s)
                
                (my-subsetp s fs)
                (my-subsetp fs s)
                (ts-propertyp a ts fs pt g))
           (ts-propertyp a ts s pt g)))

(test? ; not-memp-del
  (implies (setp ts)
           (not (memp u (del u ts)))))

(test? ; ts-propertyp-choose-next ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt) (vertex-listp ts) ;types
                
                (invp ts pt g a)
                (my-subsetp ts (all-nodes g))
                (setp ts)
                (consp ts)
                (nodep a g)
                (equal (path a pt) (list a)))
           (let ((u (choose-next ts pt g)))
             (ts-propertyp a (del u ts) (comp-set (del u ts) (all-nodes g))
                           (reassign u (neighbors u g) pt g) g))))

(test? ; invp-choose-next ; [Custom]
 (implies (and (source-vertexp a) (vertex-path-alistp pt) (vertex-listp ts) ;types
                
                (invp ts pt g a)
                (my-subsetp ts (all-nodes g))
                (graphp g)
                (consp ts)
                (setp ts)
                (nodep a g)
                (equal (path a pt) (list a))) ;0
           (let ((u (choose-next ts pt g)))
             (invp (del u ts)
                  (reassign u (neighbors u g) pt g)
                  g a))))


(test? ; del-subsetp
  (implies (my-subsetp ts s)
           (my-subsetp (del u ts) s)))

(test? ; del-true-listp
  (implies (true-listp ts)
           (true-listp (del u ts))))

(test? ; del-noduplicates
  (implies (setp ts)
           (setp (del u ts))))

(test? ; path-a-pt-reassign ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt) (vertex-listp v-lst) ;types
                 
                (pt-propertyp a pt g)
                (nodep a g)
                (equal (path a pt) (list a)))
           (equal (path a (reassign u v-lst pt g))
                  (list a))))

(test? ; invp-last-lemma ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (vertex-path-alistp pt) (vertex-listp ts) ;types
                
                (invp ts pt g a)
                (my-subsetp ts (all-nodes g))
                (nodep a g)
                (equal (path a pt) (list a))
                (true-listp ts)
                (setp ts))
           (invp nil (dsp ts pt g) g a)))

(test? ; true-listp-union
  (implies (and (true-listp lst1)
                (true-listp lst2))
           (true-listp (my-union lst1 lst2))))

(test? ; true-list-all-nodes
  (true-listp (all-nodes g)))

(test? ; invp-last ; [Custom]
 (implies (and (source-vertexp a) ;types
               (nodep a g)
               (graphp g))
           (invp nil (dsp (all-nodes g)
                         (list (cons a (list a)))
                         g) g a)))

(test? ; main-lemma1 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (nodep a g) (vertexp b) (vertex-path-alistp pt) ;types
                (invp nil pt g a) ;16.5
                (nodep b g)) ;10.60 -- yet no witnesses to the whole conjecture NOTE
           (shortest-pathp a b (path b pt) g)))

(test? ; main-lemma2 ; [Custom]
  (implies (and (graphp g) (source-vertexp a) (nodep a g) (vertexp b) (vertex-path-alistp pt) ;types
                
                (invp nil pt g a)
                (nodep b g))
           (or (null (path b pt))
               (pathp-from-to (path b pt) a b g))))
#|
(DSP '(A G1 N Z9 W5 Y F2 Z8 Z3 V9 L1
                            H2 O2 S1 X5 D1 O W2 Z6 W4 Q I B1 Q2 H1
                            Y5 S U2 M1 V2 B Y9 W7 X9 X A1 L X4 S2)
                         '((A A))
                         '((A (A1 . 2/3)
                             (G1 . 722/335)
                             (N . 1/4)
                             (Z9 . 86/57)
                             (W5 . 1/3)
                             (Y . 2/15)
                             (F2 . 1/3)
                             (Z8 . 12)
                             (Z3 . 38/77)
                             (V9 . 7/10)
                             (L1 . 21/100))
                          (X4 (H2 . 1/5)
                              (O2 . 935/3599)
                              (X9 . 1/12)
                              (S1 . 1)
                              (X5 . 1/4)
                              (D1 . 91/24)
                              (O . 1)
                              (W2 . 9/7)
                              (Z6 . 29/9)
                              (W4 . 2)
                              (Q . 1)
                              (I . 2/3)
                              (A1 . 3/2)
                              (B1 . 2810/879))
                          (S2 (Q2 . 827/569)
                              (H1 . 2172/563)
                              (Y5 . 235/167)
                              (S . 12/13)
                              (U2 . 1)
                              (M1 . 329/73)
                              (V2 . 751/222)
                              (B . 3)
                              (Y9 . 13/6)
                              (W7 . 8/5))
                          (X9 (X . 59/18) (A1 . 129/196))
                          (L (X4 . 1) (S2 . 1))))
|#
(test? ; main-lemma3 ; [Custom]
  (implies (and (source-vertexp a) (vertexp b) ;types
                
                (nodep a g)
                (nodep b g)
                (graphp g))
           (or (null (dijkstra-shortest-path a b g))
               (pathp-from-to (dijkstra-shortest-path a b g)
                             a b g))))

(test? ; main-lemma4 ; [Custom]
  (implies (and (source-vertexp a) (vertexp b) ;types
                
                (nodep a g)
                (nodep b g)
                (graphp g))
           (shortest-pathp a b (dijkstra-shortest-path a b g) g)))
  


(test? ; main-theorem ; [Custom]
  (implies (and (source-vertexp a) (vertexp b) ;types
                
                (nodep a g)
                (nodep b g)
                (graphp g))
           (let ((rho (dijkstra-shortest-path a b g)))
             (and (or (null rho)
                      (pathp-from-to rho a b g))
                  (shortest-pathp a b rho g)))))

(make-event
 (er-progn (mv-let (end state) 
                   (acl2::read-run-time state)
                   (assign end-time end))
           (value '(value-triple :ok))))

(make-event
 (b* ((start (@ start-time))
      (end (@ end-time)))
     (pprogn (print-rational-as-decimal (- end start)
                                        (standard-co state)
                                        state)
             (princ$ " seconds" (standard-co state) state)
             (newline (standard-co state) state)
             (newline (standard-co state) state)
             (value '(value-triple :ok)))))
            



;misc

(defun for (n seed. ans)
  (if (zp n)
    ans
    (b* (((mv x seed.) (nth-vertex-path-alist/acc n seed.)) 
         ((when (< (len x) 3)) 
          (prog2$ (cw "~x0 is small. n is ~x1~%" x n)
                  (for (1- n) seed. (cons x ans)))))
        (for (1- n) seed. ans))))

(value-triple (len (for 1000 (defdata::getseed state) nil)))#|ACL2s-ToDo-Line|#
 ;=166 so 16.6% pt sat trivially
;changed nth-vertex-path-alist/acc to give non-nil alists so now this is 0

#|
Comments:
1. (IMPLIES (AND (GRAPHP G)
              (VERTEX-LISTP P)
              (SOURCE-VERTEXP A)
              (VERTEXP V)
              (VERTEX-LISTP FS)
              (PATHP-FROM-TO P A V G) --- 1
              (NOT (EQUAL A V))
              (CONFINEDP P FS))       --- 2    1&2 need to be fixed simultaneously
         (AND (MEMP V (NEIGHBORS (LAST-NODE P) G))
              (PATHP-FROM-TO (FIND-LAST-NEXT-PATH P)
                             A (LAST-NODE P)
                             G)
              (MEMP (LAST-NODE P) FS)))


|#
;(memsum)
