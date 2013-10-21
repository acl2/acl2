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
(include-book "deps")

;; We say that x is a subtree of y if both (1) the domain of x is a subset of
;; the domain of y, and (2) for every path in the domain of x, the localdeps of
;; this path in x are a subset of the localdeps of this path in y.  

(defund subtree1 (locs sub super)
  (declare (xargs :guard (and (set::setp locs)
                              (dtreep sub)
                              (dtreep super))))
  (or (set::empty locs)
      (and (in (set::head locs) super)
           (set::subset 
            (localdeps (get (set::head locs) sub))
            (localdeps (get (set::head locs) super)))
           (subtree1 (set::tail locs) sub super))))

(defund subtree (sub super)
  (declare (xargs :guard (and (dtreep sub)
                              (dtreep super))))
  (subtree1 (domain sub) sub super))

(defthm subtree1-of-dtreefix-of-sub
  (equal (subtree1 locs (dtreefix sub) super)
         (subtree1 locs sub super))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm subtree1-of-dtreefix-of-super
  (equal (subtree1 locs sub (dtreefix super))
         (subtree1 locs sub super))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm in-super-when-subtree1-and-in-locs
  (implies (and (subtree1 locs sub super)
                (set::in path locs))
           (in path super))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm in-localdeps-of-get-when-in-localdeps-of-get-of-subtree
  (implies (and (subtree1 locs sub super)
                (set::in path locs)
                (set::in a (localdeps (get path sub))))
           (set::in a (localdeps (get path super))))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm subset-of-localdeps-of-gets-when-subtree1
  (implies (and (subtree1 locs sub super)
                (set::in path locs))
           (set::subset (localdeps (get path sub))
                         (localdeps (get path super)))))

(defthm subtree1-when-empty-locs
  (implies (set::empty locs)
           (subtree1 locs sub super))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm subtree-of-dtreefix-of-sub
  (equal (subtree (dtreefix sub) super)
         (subtree sub super))
  :hints(("Goal" :in-theory (enable subtree))))

(defthm subtree-of-dtreefix-of-super
  (equal (subtree sub (dtreefix super))
         (subtree sub super))
  :hints(("Goal" :in-theory (enable subtree))))

(encapsulate
 ()

 (local (defthmd lemma
          (implies (and (subtree sub super)
                        (true-listp path)
                        (in path sub))
                   (in path super))
          :hints(("Goal" :in-theory (enable subtree)))))

 (defthm in-super-when-in-subtree
   (implies (and (subtree sub super)
                 (in path sub))
            (in path super))
   :hints(("Goal" :use (:instance lemma (path (list::fix path)))))))

(defthm in-get-of-super-when-in-get-of-subtree
  (implies (and (subtree sub super)
                (in a (get path sub)))
           (in a (get path super))))

(encapsulate
 ()

 (local (defthmd lemma1
          (implies (and (subtree sub super)
                        (not (in path sub)))
                   (set::subset (localdeps (get path sub))
                                 (localdeps (get path super))))
          :hints(("Goal" :in-theory (enable subtree)))))
  
 (local (defthmd lemma2
          (implies (and (subtree sub super)
                        (true-listp path)
                        (in path sub))
                   (set::subset (localdeps (get path sub))
                                 (localdeps (get path super))))
          :hints(("Goal" :in-theory (enable subtree)))))
  
 (local (defthmd lemma3
          (implies (and (subtree sub super)
                        (in path sub))
                   (set::subset (localdeps (get path sub))
                                 (localdeps (get path super))))
          :hints(("Goal" 
                  :use (:instance lemma2 (path (list::fix path)))))))
  
 (defthm subset-of-localdeps-of-gets-when-subtree
   (implies (subtree sub super)
            (set::subset (localdeps (get path sub))
                          (localdeps (get path super))))
   :hints(("Goal" 
           :in-theory (enable lemma1 lemma3)
           :cases ((in path sub))))))

(defthm in-localdeps-of-get-when-subtree
   (implies (and (subtree sub super)
                 (set::in a (localdeps (get path sub))))
            (set::in a (localdeps (get path super))))
   :hints(("Goal" 
           :in-theory (disable subset-of-localdeps-of-gets-when-subtree)
           :use (:instance subset-of-localdeps-of-gets-when-subtree))))

(defthm subset-of-localdeps-when-subtree
  (implies (subtree sub super)
           (set::subset (localdeps sub)
                         (localdeps super)))
  :hints(("Goal" :use (:instance subset-of-localdeps-of-gets-when-subtree
                                 (path nil)))))

(defthm in-localdeps-of-super-when-in-localdeps-of-subtree
  (implies (and (subtree sub super)
                (set::in a (localdeps sub)))
           (set::in a (localdeps super)))
  :hints(("Goal" :use (:instance in-localdeps-of-get-when-subtree
                                 (path nil)))))

(encapsulate
 ()

 (encapsulate
  (((subtree-hyps) => *)
   ((subtree-sub) => *)
   ((subtree-super) => *))
 
  (local (defun subtree-hyps () nil))
  (local (defun subtree-sub () nil))
  (local (defun subtree-super () nil))
 
  (defthmd subtree-membership-constraint
    (implies 
     (and (subtree-hyps)
          (in subtree-path (subtree-sub)))
     (and (in subtree-path (subtree-super))
          (set::subset 
           (localdeps (get subtree-path (subtree-sub)))
           (localdeps (get subtree-path (subtree-super))))))))

 (local (defund subtree1-badguy (locs sub super)
          (declare (xargs :verify-guards nil))
          (cond ((set::empty locs)
                 nil)
                ((and (in (set::head locs) super)
                      (set::subset 
                       (localdeps (get (set::head locs) sub))
                       (localdeps (get (set::head locs) super))))
                 (subtree1-badguy (set::tail locs) sub super))
                (t (set::head locs)))))
          
 (local (defthmd subtree1-badguy-witness
          (equal (not (subtree1 locs sub super))
                 (and (set::in (subtree1-badguy locs sub super) locs)
                      (or (not (in (subtree1-badguy locs sub super) super))
                          (not (set::subset 
                                (localdeps (get (subtree1-badguy locs sub super)
                                                sub))
                                (localdeps (get (subtree1-badguy locs sub super)
                                                super)))))))
          :hints(("Goal" 
                  :in-theory (enable subtree1-badguy subtree1)
                  :induct (subtree1-badguy locs sub super)))))
  
 (defthmd subtree-by-membership-driver
   (implies (subtree-hyps)
            (subtree (subtree-sub) (subtree-super)))
   :hints(("Goal"
           :in-theory (enable subtree)
           :use ((:instance subtree1-badguy-witness 
                            (locs (domain (subtree-sub)))
                            (sub (subtree-sub))
                            (super (subtree-super)))
                 (:instance subtree-membership-constraint
                            (subtree-path
                             (subtree1-badguy (domain (subtree-sub))
                                              (subtree-sub) 
                                              (subtree-super))))))))

 (defadvice subtree-by-membership
   (implies (subtree-hyps)
            (subtree (subtree-sub) (subtree-super)))
   :rule-classes (:pick-a-point :driver subtree-by-membership-driver)))

(defthm subtree-reflexive
  (subtree x x))

(defthm subtree-transitive-one
  (implies (and (subtree x y)
                (subtree y z))
           (subtree x z)))

(defthm subtree-transitive-two
  (implies (and (subtree y z)
                (subtree x y))
           (subtree x z)))

(defthm subtree-of-get-with-get
  (implies (subtree sub super)
           (subtree (get path sub) 
                    (get path super))))

(defthm in-children-of-super-when-in-children-of-subtree
  (implies (and (subtree sub super)
                (map::in key (children sub)))
           (map::in key (children super)))
  :hints(("Goal" 
          :in-theory (enable in-children-is-in-of-singleton-path))))

(defthm subset-of-domains-when-subtree
  (implies (subtree sub super)
           (set::subset (map::domain (children sub))
                         (map::domain (children super)))))

(defthm in-deps-of-get-super-when-in-deps-of-get-subtree
  ;; We want to show that for every path, (deps (get path x)) is a subset of
  ;; (deps (get path y)).  To show this, by membership all we must do is show
  ;; that (in a (deps (get path x))) implies (in a (deps (get path y))).
  ;;
  ;; We use the depsource function to choose the particular path to the node in
  ;; (get path x) that has a as its localdep.  Then, since x is a subtree of y,
  ;; we know that a is also a localdep when we follow that same path through (get
  ;; path y).  Then, since a is a localdep of some path in (get path y), it
  ;; follows that a is a dep of y.
  (implies (and (subtree sub super)
                (set::in a (deps (get path sub))))
           (set::in a (deps (get path super))))
  :hints(("Goal"
          :in-theory (disable in-localdeps-of-get-when-subtree
                              in-deps-when-in-localdeps-of-get
                              get-of-get)
          :use ((:instance in-localdeps-of-get-when-subtree
                           (sub (get path sub))
                           (super (get path super))
                           (path (depsource a (get path sub)))
                           (a a))
                (:instance in-deps-when-in-localdeps-of-get
                           (path (depsource a (get path sub)))
                           (dtree (get path super))
                           (a a))))))

(defthm in-deps-of-super-when-in-deps-of-subtree
  (implies (and (subtree sub super)
                (set::in a (deps sub)))
           (set::in a (deps super)))
  :hints(("Goal" 
          :use (:instance in-deps-of-get-super-when-in-deps-of-get-subtree
                          (path nil)))))

(defthm subset-of-deps-when-subtree
  (implies (subtree sub super)
           (set::subset (deps sub) 
                         (deps super))))



;; We now introduce a slightly weaker notion, where only the "deps" rather than
;; "localdeps" must be identical.
;;
;; bzo do we *really* want all of these rules, since after all some of them
;; are just the same as subtree rules, and we have the implication that
;; (subtree x y) => (subdeps x y) ?

(defund subdeps1 (locs sub super)
  (declare (xargs :guard (and (set::setp locs)
                              (dtreep sub)
                              (dtreep super))))
  (or (set::empty locs)
      (and (in (set::head locs) super)
           (set::subset 
            (deps (get (set::head locs) sub))
            (deps (get (set::head locs) super)))
           (subdeps1 (set::tail locs) sub super))))

(defund subdeps (sub super)
  (declare (xargs :guard (and (dtreep sub)
                              (dtreep super))))
  (subdeps1 (domain sub) sub super))

(defthm subdeps1-of-dtreefix-of-sub
  (equal (subdeps1 locs (dtreefix sub) super)
         (subdeps1 locs sub super))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm subdeps1-of-dtreefix-of-super
  (equal (subdeps1 locs sub (dtreefix super))
         (subdeps1 locs sub super))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm in-super-when-subdeps1-and-in-locs
  (implies (and (subdeps1 locs sub super)
                (set::in path locs))
           (in path super))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm in-deps-of-get-super-when-in-deps-of-get-subdeps
  (implies (and (subdeps1 locs sub super)
                (set::in path locs)
                (set::in a (deps (get path sub))))
           (set::in a (deps (get path super))))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm subset-of-deps-of-gets-when-subdeps1
  (implies (and (subdeps1 locs sub super)
                (set::in path locs))
           (set::subset (deps (get path sub))
                         (deps (get path super)))))

(defthm subdeps1-when-empty-locs
  (implies (set::empty locs)
           (subdeps1 locs sub super))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm subdeps-of-dtreefix-of-sub
  (equal (subdeps (dtreefix sub) super)
         (subdeps sub super))
  :hints(("Goal" :in-theory (enable subdeps))))

(defthm subdeps-of-dtreefix-of-super
  (equal (subdeps sub (dtreefix super))
         (subdeps sub super))
  :hints(("Goal" :in-theory (enable subdeps))))

(encapsulate
 ()

 (local (defthmd lemma
          (implies (and (subdeps sub super)
                        (true-listp path)
                        (in path sub))
                   (in path super))
          :hints(("Goal" :in-theory (enable subdeps)))))

 (defthm in-super-when-in-subdeps
   (implies (and (subdeps sub super)
                 (in path sub))
            (in path super))
   :hints(("Goal" :use (:instance lemma (path (list::fix path)))))))

(defthm in-get-of-super-when-in-get-of-subdeps
  (implies (and (subdeps sub super)
                (in a (get path sub)))
           (in a (get path super))))

(encapsulate
 ()

 (local (defthmd lemma1
          (implies (and (subdeps sub super)
                        (not (in path sub)))
                   (set::subset (deps (get path sub))
                                 (deps (get path super))))
          :hints(("Goal" :in-theory (enable subdeps)))))
  
 (local (defthmd lemma2
          (implies (and (subdeps sub super)
                        (true-listp path)
                        (in path sub))
                   (set::subset (deps (get path sub))
                                 (deps (get path super))))
          :hints(("Goal" :in-theory (enable subdeps)))))
  
 (local (defthmd lemma3
          (implies (and (subdeps sub super)
                        (in path sub))
                   (set::subset (deps (get path sub))
                                 (deps (get path super))))
          :hints(("Goal" 
                  :use (:instance lemma2 (path (list::fix path)))))))
  
 (defthm subset-of-deps-of-gets-when-subdeps
   (implies (subdeps sub super)
            (set::subset (deps (get path sub))
                          (deps (get path super))))
   :hints(("Goal" 
           :in-theory (enable lemma1 lemma3)
           :cases ((in path sub))))))

(defthm in-deps-of-get-when-subdeps
  (implies (and (subdeps sub super)
                (set::in a (deps (get path sub))))
           (set::in a (deps (get path super))))
  :hints(("Goal" 
          :in-theory (disable subset-of-deps-of-gets-when-subdeps)
          :use (:instance subset-of-deps-of-gets-when-subdeps))))

(defthm subset-of-deps-when-subdeps
  (implies (subdeps sub super)
           (set::subset (deps sub)
                         (deps super)))
  :hints(("Goal" :use (:instance subset-of-deps-of-gets-when-subdeps
                                 (path nil)))))

(defthm in-deps-of-super-when-in-deps-of-subdeps
  (implies (and (subdeps sub super)
                (set::in a (deps sub)))
           (set::in a (deps super)))
  :hints(("Goal" :use (:instance in-deps-of-get-when-subdeps
                                 (path nil)))))

(encapsulate
 ()

 (encapsulate
  (((subdeps-hyps) => *)
   ((subdeps-sub) => *)
   ((subdeps-super) => *))
 
  (local (defun subdeps-hyps () nil))
  (local (defun subdeps-sub () nil))
  (local (defun subdeps-super () nil))
 
  (defthmd subdeps-membership-constraint
    (implies 
     (and (subdeps-hyps)
          (in subdeps-path (subdeps-sub)))
     (and (in subdeps-path (subdeps-super))
          (set::subset 
           (deps (get subdeps-path (subdeps-sub)))
           (deps (get subdeps-path (subdeps-super))))))))

 (local (defund subdeps1-badguy (locs sub super)
          (declare (xargs :verify-guards nil))
          (cond ((set::empty locs)
                 nil)
                ((and (in (set::head locs) super)
                      (set::subset 
                       (deps (get (set::head locs) sub))
                       (deps (get (set::head locs) super))))
                 (subdeps1-badguy (set::tail locs) sub super))
                (t (set::head locs)))))
          
 (local (defthmd subdeps1-badguy-witness
          (equal (not (subdeps1 locs sub super))
                 (and (set::in (subdeps1-badguy locs sub super) locs)
                      (or (not (in (subdeps1-badguy locs sub super) super))
                          (not (set::subset 
                                (deps (get (subdeps1-badguy locs sub super)
                                                sub))
                                (deps (get (subdeps1-badguy locs sub super)
                                                super)))))))
          :hints(("Goal" 
                  :in-theory (enable subdeps1-badguy subdeps1)
                  :induct (subdeps1-badguy locs sub super)))))
  
 (defthmd subdeps-by-membership-driver
   (implies (subdeps-hyps)
            (subdeps (subdeps-sub) (subdeps-super)))
   :hints(("Goal"
           :in-theory (enable subdeps)
           :use ((:instance subdeps1-badguy-witness 
                            (locs (domain (subdeps-sub)))
                            (sub (subdeps-sub))
                            (super (subdeps-super)))
                 (:instance subdeps-membership-constraint
                            (subdeps-path
                             (subdeps1-badguy (domain (subdeps-sub))
                                              (subdeps-sub) 
                                              (subdeps-super))))))))

 (defadvice subdeps-by-membership
   (implies (subdeps-hyps)
            (subdeps (subdeps-sub) (subdeps-super)))
   :rule-classes (:pick-a-point :driver subdeps-by-membership-driver)))

(defthm subdeps-reflexive
  (subdeps x x))

(defthm subdeps-transitive-one
  (implies (and (subdeps x y)
                (subdeps y z))
           (subdeps x z)))

(defthm subdeps-transitive-two
  (implies (and (subdeps x y)
                (subdeps y z))
           (subdeps x z)))

(defthm subdeps-of-get-with-get
  (implies (subdeps sub super)
           (subdeps (get path sub)
                    (get path super))))

(defthm in-children-of-super-when-in-children-of-subdeps
  (implies (and (subdeps sub super)
                (map::in key (children sub)))
           (map::in key (children super)))
  :hints(("Goal" 
          :in-theory (enable in-children-is-in-of-singleton-path))))
          
(defthm subset-of-domains-when-subdeps
  (implies (subdeps sub super)
           (set::subset (map::domain (children sub))
                         (map::domain (children super)))))

(defthm subdeps-when-subtree
  (implies (subtree sub super)
           (subdeps sub super)))




;; We now extend our subtree and subdeps relations to maps.  We call the
;; extended relations subtreemap and subdepsmap.

(defund subtreemap (sub super)
  (declare (xargs :guard (and (mapp sub)
                              (mapp super)
                              (dtreemapp sub)
                              (dtreemapp super))))
  (or (map::empty-exec sub)
      (and (map::in (map::head sub) super)
           (subtree (map::get (map::head sub) sub)
                    (map::get (map::head sub) super))
           (subtreemap (map::tail sub) super))))

(defthm in-super-when-in-subtreemap
  (implies (and (subtreemap sub super)
                (map::in key sub))
           (map::in key super))
  :hints(("Goal" :in-theory (enable subtreemap))))

(defthm in-subtreemap-when-not-in-super
  (implies (and (subtreemap sub super)
                (not (map::in key super)))
           (equal (map::in key sub)
                  nil))
  :hints(("Goal" :in-theory (enable subtreemap))))
                      
(defthm subtree-of-gets-when-subtreemap
  (implies (subtreemap sub super)
           (equal (subtree (map::get key sub) 
                           (map::get key super))
                  (if (map::in key sub)
                      t
                    (subtree (map::emptymap)
                             (map::get key super)))))
  :hints(("Goal" :in-theory (enable subtreemap))))

       
(encapsulate
 ()

 (encapsulate
  (((subtreemap-hyps) => *)
   ((subtreemap-sub) => *)
   ((subtreemap-super) => *))
 
  (local (defun subtreemap-hyps () nil))
  (local (defun subtreemap-sub () nil))
  (local (defun subtreemap-super () nil))
 
  (defthmd subtreemap-membership-constraint
    (implies 
     (and (subtreemap-hyps)
          (map::in subtreemap-key (subtreemap-sub)))
     (and (map::in subtreemap-key (subtreemap-super))
          (subtree (map::get subtreemap-key (subtreemap-sub))
                   (map::get subtreemap-key (subtreemap-super)))))))

 (local (defund subtreemap-badguy (sub super)
          (cond ((map::empty-exec sub)
                 nil)
                ((and (map::in (map::head sub) super)
                      (subtree (map::get (map::head sub) sub)
                               (map::get (map::head sub) super)))
                 (subtreemap-badguy (map::tail sub) super))
                (t (map::head sub)))))

 (local (defthmd subtreemap-badguy-witness
          (equal (not (subtreemap sub super))
                 (and (map::in (subtreemap-badguy sub super) sub)
                      (or (not (map::in (subtreemap-badguy sub super) super))
                          (not (subtree (map::get (subtreemap-badguy sub super)
                                                  sub)
                                        (map::get (subtreemap-badguy sub super)
                                                  super))))))
          :hints(("Goal" 
                  :in-theory (enable subtreemap subtreemap-badguy)
                  :induct (subtreemap-badguy sub super)))))

 (defthmd subtreemap-by-membership-driver
   (implies (subtreemap-hyps)
            (subtreemap (subtreemap-sub) (subtreemap-super)))
   :hints(("Goal"
           :in-theory (enable subtreemap)
           :use ((:instance subtreemap-badguy-witness
                            (sub (subtreemap-sub))
                            (super (subtreemap-super)))
                 (:instance subtreemap-membership-constraint
                            (subtreemap-key
                             (subtreemap-badguy (subtreemap-sub)
                                                (subtreemap-super))))))))

 (defadvice subtreemap-by-membership
   (implies (subtreemap-hyps)
            (subtreemap (subtreemap-sub) (subtreemap-super)))
   :rule-classes (:pick-a-point :driver subtreemap-by-membership-driver)))

(defthm subtreemap-reflexive
  (subtreemap x x))

(defthm subtreemap-transitive-one
  (implies (and (subtreemap x y)
                (subtreemap y z))
           (subtreemap x z))
  :hints(("Goal" :in-theory (enable subtreemap))))

(defthm subtreemap-transitive-two
  (implies (and (subtreemap y z)
                (subtreemap x y))
           (subtreemap x z)))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (map::equiv x x-equiv)
                        (subtreemap x y))
                   (subtreemap x-equiv y))))

 (defcong map::equiv equal (subtreemap x y) 1)
 (defcong map::equiv equal (subtreemap x y) 2))

(defthm in-depsmap-of-super-when-in-depsmap-of-subtree
  (implies (and (subtreemap sub super)
                (set::in a (depsmap sub)))
           (set::in a (depsmap super)))
  :hints(("Goal" :in-theory (enable subtreemap))))

(defthm subset-of-depsmaps-when-subtreemap
  (implies (subtreemap sub super)
           (set::subset (depsmap sub)
                         (depsmap super))))

(defthm subtreemap-of-children-when-subtree
  (implies (subtree sub super)
           (subtreemap (children sub)
                       (children super)))
  :hints(("Goal" 
          :in-theory (enable get-of-children-is-get-of-singleton-path))))





(defund subdepsmap (sub super)
  (declare (xargs :guard (and (mapp sub)
                              (mapp super)
                              (dtreemapp sub)
                              (dtreemapp super))))
  (or (map::empty-exec sub)
      (and (map::in (map::head sub) super)
           (subdeps (map::get (map::head sub) sub)
                    (map::get (map::head sub) super))
           (subdepsmap (map::tail sub) super))))

(defthm in-super-when-in-subdepsmap
  (implies (and (subdepsmap sub super)
                (map::in key sub))
           (map::in key super))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm in-subdepsmap-when-not-in-super
  (implies (and (subdepsmap sub super)
                (not (map::in key super)))
           (equal (map::in key sub)
                  nil))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm subdeps-of-gets-when-subdepsmap
  (implies (subdepsmap sub super)
           (equal (subdeps (map::get key sub) 
                           (map::get key super))
                  (if (map::in key sub)
                      t
                    (subdeps (map::emptymap) 
                             (map::get key super)))))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(encapsulate
 ()

 (encapsulate
  (((subdepsmap-hyps) => *)
   ((subdepsmap-sub) => *)
   ((subdepsmap-super) => *))
 
  (local (defun subdepsmap-hyps () nil))
  (local (defun subdepsmap-sub () nil))
  (local (defun subdepsmap-super () nil))
 
  (defthmd subdepsmap-membership-constraint
    (implies 
     (and (subdepsmap-hyps)
          (map::in subdepsmap-key (subdepsmap-sub)))
     (and (map::in subdepsmap-key (subdepsmap-super))
          (subdeps (map::get subdepsmap-key (subdepsmap-sub))
                   (map::get subdepsmap-key (subdepsmap-super)))))))

 (local (defund subdepsmap-badguy (sub super)
          (cond ((map::empty-exec sub)
                 nil)
                ((and (map::in (map::head sub) super)
                      (subdeps (map::get (map::head sub) sub)
                               (map::get (map::head sub) super)))
                 (subdepsmap-badguy (map::tail sub) super))
                (t (map::head sub)))))

 (local (defthmd subdepsmap-badguy-witness
          (equal (not (subdepsmap sub super))
                 (and (map::in (subdepsmap-badguy sub super) sub)
                      (or (not (map::in (subdepsmap-badguy sub super) super))
                          (not (subdeps (map::get (subdepsmap-badguy sub super)
                                                  sub)
                                        (map::get (subdepsmap-badguy sub super)
                                                  super))))))
          :hints(("Goal" 
                  :in-theory (enable subdepsmap subdepsmap-badguy)
                  :induct (subdepsmap-badguy sub super)))))

 (defthmd subdepsmap-by-membership-driver
   (implies (subdepsmap-hyps)
            (subdepsmap (subdepsmap-sub) (subdepsmap-super)))
   :hints(("Goal"
           :in-theory (enable subdepsmap)
           :use ((:instance subdepsmap-badguy-witness
                            (sub (subdepsmap-sub))
                            (super (subdepsmap-super)))
                 (:instance subdepsmap-membership-constraint
                            (subdepsmap-key
                             (subdepsmap-badguy (subdepsmap-sub)
                                                (subdepsmap-super))))))))

 (defadvice subdepsmap-by-membership
   (implies (subdepsmap-hyps)
            (subdepsmap (subdepsmap-sub) (subdepsmap-super)))
   :rule-classes (:pick-a-point :driver subdepsmap-by-membership-driver)))


(defthm subdepsmap-reflexive
  (subdepsmap x x))

(defthm subdepsmap-transitive-one
  (implies (and (subdepsmap x y)
                (subdepsmap y z))
           (subdepsmap x z))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm subdepsmap-transitive-two
  (implies (and (subdepsmap y z)
                (subdepsmap x y))
           (subdepsmap x z)))

(encapsulate
 ()

 (local (defthm lemma
          (implies (and (map::equiv x x-equiv)
                        (subdepsmap x y))
                   (subdepsmap x-equiv y))))

 (defcong map::equiv equal (subdepsmap x y) 1)
 (defcong map::equiv equal (subdepsmap x y) 2))

(defthm in-depsmap-of-super-when-in-depsmap-of-subdeps
  (implies (and (subdepsmap sub super)
                (set::in a (depsmap sub)))
           (set::in a (depsmap super)))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm subset-of-depsmaps-when-subdepsmap
  (implies (subdepsmap sub super)
           (set::subset (depsmap sub)
                         (depsmap super))))

(defthm subdepsmap-of-children-when-subdeps
  (implies (subdeps sub super)
           (subdepsmap (children sub)
                       (children super)))
  :hints(("Goal" 
          :in-theory (enable get-of-children-is-get-of-singleton-path))))

(defthm subdepsmap-when-subtreemap
  (implies (subtreemap sub super)
           (subdepsmap sub super)))




;; We introduce dtree equivalences using "mutual subtrees" and "mutual
;; subdeps", so that dtrees are equivalent iff (1) their domains are the same,
;; and (2) the localdeps/deps at every path within both trees are the same
;; sets.  

(defund equiv (x y)
  (declare (xargs :guard (and (dtreep x)
                              (dtreep y))))
  (and (subtree x y)
       (subtree y x)))
         
(defund equivdeps (x y)
  (declare (xargs :guard (and (dtreep x)
                              (dtreep y))))
  (and (subdeps x y)
       (subdeps y x)))

(defequiv equiv
  :hints(("Goal" :in-theory (enable equiv))))

(defequiv equivdeps
  :hints(("Goal" :in-theory (enable equivdeps))))


;; Since equiv refines equivdeps, we get to reuse many rules.

(defrefinement equiv equivdeps
  :hints(("Goal" :in-theory (enable equiv equivdeps))))

;; dtreefix - We write this rule with equiv rather than equivdeps, because it
;; is basically like writing "equal" instead of "iff".

(defthm dtreefix-under-equiv
  (equiv (dtreefix dtree) dtree)
  :hints(("Goal" :in-theory (enable equiv))))

;; localdeps - We can't provide a congruence for equivdeps, becuase equivdeps
;; alone doesn't tell us anything about the localdeps.  But, we can provide a
;; great rule for equiv.

(defcong equiv equal (localdeps dtree) 1
  :hints(("Goal" :in-theory (enable equiv))))

;; in - We prove the equivalence for equivdeps.  This automatically gives us
;; the equiv rule for free, since equiv -> equivdeps -> equal in's.

(defcong equivdeps equal (in path dtree) 2
  :hints(("Goal" :in-theory (enable equivdeps))))

;; get - We prove two rules for get.  For the equivdeps rule we can only 
;; say that the results are equivdeps.  For the equiv rule, we know that 
;; the results are equiv.

(defcong equivdeps equivdeps (get path dtree) 2
  :hints(("Goal" :in-theory (enable equivdeps))))

(defcong equiv equiv (get path dtree) 2
  :hints(("Goal" :in-theory (enable equiv))))

;; domain - We know that even merely equivdeps dtrees have the same domain, so
;; we only prove the rule for equivdeps.

(defcong equivdeps equal (domain dtree) 1
  :hints(("Goal" :in-theory (enable equivdeps))))

;; deps - we know that even merely equivdeps dtrees have the same deps, so we
;; only prove the rule for equivdeps.

(defcong equivdeps equal (deps dtree) 1
  :hints(("Goal" :in-theory (enable equivdeps))))

;; subtree and subdeps are preserved by their corresponding equivalences.  note
;; that we get for free that equiv preserves subdeps.

(defcong equivdeps equal (subdeps sub super) 1
  :hints(("Goal" :in-theory (enable equivdeps))))

(defcong equivdeps equal (subdeps sub super) 2
  :hints(("Goal" :in-theory (enable equivdeps))))

(defcong equiv equal (subtree sub super) 1
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equal (subtree sub super) 2
  :hints(("Goal" :in-theory (enable equiv))))





;; In this litany of :congruence rules, we unfortunately have no rule about
;; (children dtree).  But what could we prove?  It is not even true that the
;; children must be MAPS::map-equal, because each child would only be equiv or
;; equivdeps, rather than truly equal in the ACL2 sense.  What we need are new
;; equivalences that permit such differences.

(defund equivmap (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y)
                              (dtreemapp x)
                              (dtreemapp y))))
  (and (subtreemap x y)
       (subtreemap y x)))

(defund equivdepsmap (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y)
                              (dtreemapp x)
                              (dtreemapp y))))
  (and (subdepsmap x y)
       (subdepsmap y x)))

(defequiv equivmap
  :hints(("Goal" :in-theory (enable equivmap))))

(defequiv equivdepsmap
  :hints(("Goal" :in-theory (enable equivdepsmap))))


;; We have the following refinement chain:
;; equal -> map::equiv -> equivmap -> equivdepsmap

(defrefinement map::equiv equivmap
  :hints(("Goal" :in-theory (enable equivmap))))

(defrefinement equivmap equivdepsmap
  :hints(("Goal" :in-theory (enable equivmap equivdepsmap))))

;; dtreemapfix - dtreemapfix dtree-fixes each of its results, so it is not
;; map::equiv to its result, but it is surely equivmap to its result.

(defthm dtreemapfix-under-equivmap
  (equivmap (dtreemapfix map) map)
  :hints(("Goal" :in-theory (enable equivmap))))


;; domain - we know that even maps which are merely equivdepsmap to one another
;; have identical domains.  This is "the most powerful" form of equivance we
;; can prove given the above refinement chain.

(defcong equivdepsmap equal (map::domain map) 1
  :hints(("Goal" :in-theory (enable equivdepsmap))))

;; erase - each equivalence relation has its own congruence rule across erase.

(defcong equivdepsmap equivdepsmap (map::erase a map) 2
  :hints(("Goal" :in-theory (enable equivdepsmap))))

(defcong equivmap equivmap (map::erase a map) 2
  :hints(("Goal" :in-theory (enable equivmap))))

;; set - each equivalence gets its own congruences across set

(defcong equiv equivmap (map::set key val map) 2
  :hints(("Goal" :in-theory (enable equivmap))))

(defcong equivdeps equivdepsmap (map::set key val map) 2
  :hints(("Goal" :in-theory (enable equivdepsmap))))

(defcong equivmap equivmap (map::set key val map) 3
  :hints(("Goal" :in-theory (enable equivmap))))

(defcong equivdepsmap equivdepsmap (map::set key val map) 3
    :hints(("Goal" :in-theory (enable equivdepsmap))))

;; depsmap - we already have (defcong map::equiv equal (depsmap map) 1), but, 
;; we actually want a stronger form of this, which we prove below:

(defcong equivdepsmap equal (depsmap map) 1
  :hints(("Goal" :in-theory (enable equivdepsmap))))



;; The following are congruence rules, that were unexpectedly proven. A 
;; mutual-recursive function that would walk down the tree and compare was 
;; being developed, but this approach seems much more clean, and it gives us 
;; the same power as an equivalence relation using mutual recursion.
;;
;; The real trick behind this is the use of the "domain" function in our
;; definition of subtree, and the property subtree-of-get-with-get, which
;; essentially tells you that the equiv-ness of dtrees extends all the way
;; throughout their children.  Because of this, we get the same coverage as a
;; mutually recursive equivalence relation, but without having to really make
;; things mutually recursive.

(defcong equivmap equiv (map::get key map) 2
  :hints(("Goal" :in-theory (enable equivmap equiv))))

(defcong equivdepsmap equivdeps (map::get key map) 2
  :hints(("Goal" :in-theory (enable equivdepsmap equivdeps))))

(defcong equiv equivmap (children dtree) 1
  :hints(("Goal" :in-theory (enable equivmap equiv))))

(defcong equivdeps equivdepsmap (children dtree) 1
  :hints(("Goal" :in-theory (enable equivdepsmap equivdeps))))

