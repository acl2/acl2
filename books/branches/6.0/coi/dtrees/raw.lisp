#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;;
;; Dependency Trees for Data Dependency Analysis
;; Jared Davis 
;;

(in-package "DTREE")
(include-book "equiv")


;; Throughout the dtree manipulation functions (erase, update) it is often be
;; necessary to build new dtrees, but rather than writing rules about (list
;; :dtree ...), we prefer a new, unique target for our rules.  Towards this
;; purpose, we introduce raw-dtree below.

(defund rawdtree (localdeps children)
  (declare (xargs :guard (and (set::listsetp localdeps)
                              (mapp children)
                              (dtreemapp children))))
  (list :dtree 
        (set::listsetfix localdeps)
        (dtreemapfix children)))
  
(defthm dtreep-of-rawdtree
  (dtreep (rawdtree localdeps children))
  :hints(("Goal" :in-theory (enable rawdtree dtreep))))

(defthm localdeps-of-rawdtree
  (equal (localdeps (rawdtree localdeps children))
         (set::listsetfix localdeps))
  :hints(("Goal" :in-theory (enable localdeps rawdtree dtreep))))

(defthm children-of-rawdtree
  (equal (children (rawdtree localdeps children))
         (dtreemapfix children))
  :hints(("Goal" :in-theory (enable children rawdtree dtreep))))





;; One major property that we need to know about our dtree construction is that
;; we can substitute in equivalent children and end up with an equivalent
;; result.  

(encapsulate
 ()

 (local (defthm lemma1
          (implies (and (subdepsmap sub super)
                        (in a (rawdtree locals sub)))
                   (in a (rawdtree locals super)))
          :hints(("Goal" 
                  :in-theory (disable subdeps-of-gets-when-subdepsmap)
                  :use (:instance subdeps-of-gets-when-subdepsmap
                                  (key (car a)))
                  :expand ((in a (rawdtree locals sub))
                           (in a (rawdtree locals super)))))))
                        
 (local (defthm lemma2
          ;; Interestingly, the mutually recursive version of deps is easier to
          ;; work with here...
          (implies (subdepsmap sub super)
                   (set::subset (deps (rawdtree locals sub))
                                 (deps (rawdtree locals super))))
          :hints(("Goal" 
                  :in-theory (disable set::double-containment)
                  :use ((:instance mrdeps (dtree (rawdtree locals sub)))
                        (:instance mrdeps (dtree (rawdtree locals super))))))))

 (local (defthm lemma3
          (implies (subdepsmap sub super)
                   (set::subset (deps (get a (rawdtree locals sub)))
                                (deps (get a (rawdtree locals super)))))
          :hints(("Goal" 
                  :in-theory (disable subdeps-of-gets-when-subdepsmap)
                  :use (:instance subdeps-of-gets-when-subdepsmap
                                  (key (car a)))
                  :expand ((get a (rawdtree locals sub))
                           (get a (rawdtree locals super)))))))
                 
 (defthm subdeps-of-rawdtrees-when-subdepsmap
   (implies (subdepsmap sub super)
            (subdeps (rawdtree locals sub)
                     (rawdtree locals super))))

 (local (defthm lemma4
          (implies (and (subtreemap sub super)
                        (in a (rawdtree locals sub)))
                   (in a (rawdtree locals super)))
          :hints(("Goal" :use (:instance lemma1)))))

 (local (defthm lemma5
          (implies (subtreemap sub super)
                   (set::subset (localdeps (rawdtree locals sub))
                                (localdeps (rawdtree locals super))))
          :hints(("Goal" 
                  :in-theory (disable set::double-containment)
                  :use ((:instance mrdeps (dtree (rawdtree locals sub)))
                        (:instance mrdeps (dtree (rawdtree locals super))))))))

 (local (defthm lemma6
          (implies (subtreemap sub super)
                   (set::subset 
                    (localdeps (get a (rawdtree locals sub)))
                    (localdeps (get a (rawdtree locals super)))))
          :hints(("Goal" 
                  :in-theory (disable subtree-of-gets-when-subtreemap)
                  :use ((:instance subtree-of-gets-when-subtreemap
                                   (key (car a))))
                  :expand ((get a (rawdtree locals sub))
                           (get a (rawdtree locals super)))))))

 (defthm subtree-of-rawdtrees-when-subtreemap
   (implies (subtreemap sub super)
            (subtree (rawdtree locals sub)
                     (rawdtree locals super))))

)

(defcong equivdepsmap equivdeps (rawdtree localdeps children) 2
  :hints(("Goal" :in-theory (enable equivdepsmap equivdeps))))

(defcong equivmap equiv (rawdtree localdeps children) 2
  :hints(("Goal" :in-theory (enable equivmap equiv))))

(defcong set::listsetequiv equal (rawdtree locals children) 1
  :hints(("Goal" :in-theory (enable rawdtree))))

(encapsulate
 ()

 (local (defthm in-deps-rawdtree  
          (equal (set::in a (deps (rawdtree localdeps children)))
                 (or (set::in a (set::listsetfix localdeps))
                     (set::in a (depsmap children))))
          :hints(("Goal" 
                  :use (:instance mrdeps 
                                  (dtree (rawdtree localdeps children)))))))
 
 (defthm deps-rawdtree
   (equal (deps (rawdtree localdeps children))
          (set::union (set::listsetfix localdeps) 
                      (depsmap children))))

)
               





;; Another property that we would like is that, if one constructs a dtree out
;; of the localdeps and children of another dtree, the result is equivalent to
;; whatever you started with.


(encapsulate
 ()

 (local (defthm lemma1
          (equal (in path (rawdtree (localdeps dtree) (children dtree)))
                 (in path dtree))
          :hints(("Goal" :in-theory (enable in)))))

 (local (defthm lemma2
          (equal (localdeps (rawdtree (localdeps dtree)
                                      (children dtree)))
                 (localdeps dtree))
          :hints(("Goal" :in-theory (disable set::double-containment)
                  :use ((:instance mrdeps 
                                   (dtree (rawdtree (localdeps dtree)
                                                     (children dtree))))
                        (:instance mrdeps
                                   (dtree dtree)))))))

 (local (defthm lemma3
          (equal (localdeps (get path (rawdtree (localdeps dtree) 
                                                (children dtree))))
                 (localdeps (get path dtree)))
          :hints(("Goal"
                  :in-theory (e/d (get) 
                                  (set::double-containment))))))

 (defthm rawdtree-of-localdeps-and-children-under-equiv
   (equiv (rawdtree (localdeps dtree) (children dtree))
          dtree)
   :hints(("Goal" :in-theory (enable equiv))))
)






;; We would like to have users of the library use the leaf function to
;; construct new dependency sets, rather than just consing together lists with
;; :dtree tags, etc.  Essentially, (leaf '(1 2 3)) creates a new dtree with no
;; children and a dependency set of { 1, 2, 3 }.

(defund leaf (locals)
  (declare (xargs :guard (set::listsetp locals)))
  (rawdtree locals (map::emptymap)))

(defcong set::listsetequiv equal (leaf locals) 1
  :hints(("Goal" :in-theory (enable leaf))))

(defthm dtreep-of-leaf
  (dtreep (leaf locals))
  :hints(("Goal" :in-theory (enable leaf))))

(defthm localdeps-of-leaf
  (equal (localdeps (leaf locals))
         (set::listsetfix locals))
  :hints(("Goal" :in-theory (e/d (leaf) (set::double-containment)))))

(defthm children-of-leaf
  (equal (children (leaf locals))
         (map::emptymap))
  :hints(("Goal" :in-theory (enable leaf))))

(defthm deps-of-leaf
  (equal (deps (leaf locals))
         (set::listsetfix locals))
  :hints(("Goal"          
          :in-theory (disable set::double-containment)
          :use (:instance mrdeps (dtree (leaf locals))))))

(defthm domain-of-leaf
  (equal (domain (leaf locals))
         '(nil))
  :hints(("Goal" :in-theory (enable domain aux-domain))))

(defthm in-leaf
  (equal (in path (leaf locals))
         (atom path))
  :hints(("Goal" :in-theory (enable in))))

(defthm get-of-leaf
  (equal (get path (leaf locals))
         (if (atom path)
             (leaf locals)
           *default*))
  :hints(("Goal" :in-theory (enable get))))

