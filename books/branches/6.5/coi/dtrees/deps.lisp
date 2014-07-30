#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;;
;; Dependency Trees for Data Dependency Analysis
;; Jared Davis 
;;
;;
;; deps.lisp
;;
;; Introduces deps and deps-map, the functions which compute the dependency
;; sets for dtrees.
;;
;; Dependency Sets are the primary feature of dtrees.  That is, each dtree is
;; said to represent a particular set of dependencies, which can be constructed
;; by unioning all of the dtree's local dependencies recursively with the
;; dependencies of all of the dtree's children.

(in-package "DTREE")
(include-book "base")



;; DEFINITION OF DEPS
;;
;; I like to think of the dependency set being defined using quantification as
;; follows:
;;
;;   deps(dtree) = Union_{path \in (domain dtree)}
;;                   (localdeps (lookup path dtree))
;;
;; To me this is an "ideal" definition from a reasoning perspective, and it
;; would be nice to be able to work with this definition when trying to prove
;; theorems.  We can implement this idea by writing two functions: deps1 will
;; compute the above union for any particular set of paths, and deps will just
;; invoke deps1 with the entire domain of the dtree.
;;
;; However, this is not ideal from an execution standpoint, as computing the
;; domain of a dtree could be an expensive operation.  So, for execution
;; efficiency, we will use the function mrdeps below, a mutually-recursive
;; implementation that simply walks down the tree and unions together all of
;; the localdeps it finds on the way.
;;
;; In the end, I will demonstrate that both definitions are equivalent, and
;; thus I will justify an MBE substitution allowing me to use mrdeps under the
;; hood for deps.  Finally, we also provide a function, depsmap, which computes
;; the dependency set for a map of dtrees.

(mutual-recursion 

 (defund mrdeps (dtree)
   (declare (xargs :guard (dtreep dtree)
                   :measure (count dtree)
                   :verify-guards nil))
   (set::union (localdeps dtree)
               (mrdepsmap (children dtree))))

 (defund mrdepsmap (map)
   (declare (xargs :guard (and (mapp map)
                               (dtreemapp map))
                   :measure (countmap map)
                   :verify-guards nil))
   (if (map::empty-exec map)
       (set::emptyset)
     (set::union (mrdeps (map::get (map::head map) map))
                 (mrdepsmap (map::tail map)))))
 )

(defund deps1 (locs dtree)
  (declare (xargs :guard (and (set::setp locs)
                              (dtreep dtree))
                  :verify-guards nil))
  (if (set::empty locs)
      (set::emptyset)
    (set::union (localdeps (get (set::head locs) dtree))
                (deps1 (set::tail locs) dtree))))

(defund deps (dtree)
  (declare (xargs :guard (dtreep dtree)
                  :verify-guards nil))
  (mbe :logic (deps1 (domain dtree) dtree)
       :exec (mrdeps dtree)))
  
(defund depsmap (map)
  (declare (xargs :guard (and (mapp map)
                              (dtreemapp map))
                  :verify-guards nil))
  (mbe :logic (if (map::empty-exec map)
                  (set::emptyset)
                (set::union (deps (map::get (map::head map) map))
                            (depsmap (map::tail map))))
       :exec (mrdepsmap map)))






;; THE DEPS FUNCTIONS PRODUCE LIST SETS
;;
;; The equivalence proof which allows us to soundly make this substitution is
;; rather involved.  From a high level, we argue that both deps and mrdeps
;; produce sets, and then proceed to employ a double containment proof.  To
;; begin, lets show that all of these functions produce sets.

(local (defun mrdeps-induct (flag x)
         (declare (xargs :measure (if (equal flag :dtree)
                                      (count x)
                                    (countmap x))))
         (if (equal flag :dtree)
             (mrdeps-induct :map (children x))
           (if (map::empty-exec x)
               nil
             (list (mrdeps-induct :dtree (map::get (map::head x) x))
                   (mrdeps-induct :map (map::tail x)))))))

(encapsulate
 ()

 (local (defthm lemma
          (if (equal flag :dtree)
              (set::listsetp (mrdeps x))
            (set::listsetp (mrdepsmap x)))
          :rule-classes nil
          :hints(("Goal" 
                  :in-theory (enable mrdeps mrdepsmap)
                  :induct (mrdeps-induct flag x)))))

 (defthm listsetp-of-mrdeps
   (set::listsetp (mrdeps dtree))
   :hints(("Goal" :use (:instance lemma
                                  (flag :dtree)
                                  (x dtree)))))

 (defthm listsetp-of-mrdepsmap
   (set::listsetp (mrdepsmap map))
   :hints(("Goal" :use (:instance lemma
                                  (flag :map)
                                  (x map)))))

 )
  
   
(defthm listsetp-of-deps1
  (set::listsetp (deps1 locs dtree))
  :hints(("Goal" :in-theory (enable deps1))))

(defthm listsetp-of-deps
  (set::listsetp (deps dtree))
  :hints(("Goal" :in-theory (enable deps))))

(defthm listsetp-of-depsmap
  (set::listsetp (depsmap map))
  :hints(("Goal" :in-theory (enable depsmap))))

(verify-guards mrdeps)
(verify-guards deps1)





;; MEMBERSHIP IN THE DEPS SET
;;
;; An essential and "obvious" property of the deps set is that, if a is an 
;; element of the localdeps for any node within the tree, a is also a member
;; of the deps set.  This is relatively straightforward for the simple deps
;; function, but proving this property is more complicated for the mutually
;; recursive deps.
;;
;; Recall that what we want to prove is something like the following:
;;
;;   Given a dtree, dtree.
;;   Given a path p, with (in p dtree).  
;;   Given *p = (get p dtree), i.e., the tree p points to.
;;   Given (set::in dep (localdeps *p)).
;;   Show that: (in dep (mrdeps dtree)).
;;
;; But because mrdeps is mutually recursive, we should simultaneously consider
;; the map case.  For that case, lets prove the following:
;;
;;   Given a dtree map, map.
;;   Given a path p, with (in-map p map).
;;   Given *p = (get-map p map), i.e., the tree p points to.
;;   Given (set::in dep (localdeps *p))
;;   Show that: (in dep (mrdepsmap dtree))
;;
;; If you're wondering what in-map and get-map are supposed to be, that
;; makes two of us (haha).  Of course, if p is nonempty, we have some idea of
;; what these ideas ought to be.  In fact, we could say, that whenever p is
;; nonempty, it would be nice to define
;;
;;  (in-map p map) as (in (cdr p) (map::get (car p) map))
;;
;; and
;;
;;  (get-map p map) as (get (cdr p) (map::get (car p) map))
;;
;; But what in the world do we do when p is empty?  My answer is that I am just
;; going to return nil, and our induction scheme should prevent us from ever
;; considering this case.  In other words, we will add an extra given to the
;; map case:
;;
;;   Given that p is a consp.
;;
;; Once we phrase the theorem right, it goes through without much of a problem.
;; The tricky part with mutual recursion seems to be just stating the property 
;; that you are trying to prove.

(defthm in-deps1-when-in-localdeps
  (implies (and (set::in path locs)
                (set::in a (localdeps (get path dtree))))
           (set::in a (deps1 locs dtree)))
  :hints(("Goal" :in-theory (enable deps1))))

(defthm in-deps-when-in-localdeps-of-get
  (implies (set::in a (localdeps (get path dtree)))
           (set::in a (deps dtree)))
  :hints(("Goal" :in-theory (enable deps)
          :use (:instance in-deps1-when-in-localdeps
                          (locs (domain dtree))
                          (path (list::fix path))))))

(defthm in-deps-when-in-localdeps
  (implies (set::in a (localdeps dtree))
           (set::in a (deps dtree)))
  :hints(("Goal" 
          :in-theory (disable in-deps-when-in-localdeps-of-get)
          :use (:instance in-deps-when-in-localdeps-of-get
                          (path nil)))))

(defthm empty-of-localdeps-of-get-when-deps-empty
  (implies (set::empty (deps dtree))
           (set::empty (localdeps (get path dtree))))
  :hints(("Goal" 
          :in-theory (disable in-deps-when-in-localdeps-of-get)
          :use (:instance in-deps-when-in-localdeps-of-get
                          (a (set::head (localdeps (get path dtree))))))))

(defthm empty-of-localdeps-when-deps-empty
  (implies (set::empty (deps dtree))
           (set::empty (localdeps dtree)))
  :hints(("Goal" 
          :in-theory (disable empty-of-localdeps-of-get-when-deps-empty)
          :use (:instance empty-of-localdeps-of-get-when-deps-empty
                          (path nil)))))

(defthm empty-of-deps-when-nonempty-of-localdeps-of-get
  (implies (not (set::empty (localdeps (get path dtree))))
           (equal (set::empty (deps dtree))
                  nil)))

(defthm empty-of-deps-when-nonempty-of-localdeps
  (implies (not (set::empty (localdeps dtree)))
           (equal (set::empty (deps dtree))
                  nil)))

(local (in-theory (enable mrdeps)))


;; Normally I really dislike having "open" theorems.  However, the ACL2
;; hieuristics for opening mutually recursive functions really don't seem to
;; work very well, so I am putting these in -- locally, of course.  They save
;; several :expand hints from needing to be attached to subgoals.

(local (defthm open-mrdepsmap-empty
         (implies (map::empty map)
                  (equal (mrdepsmap map) 
                         (set::emptyset)))
         :hints(("Goal" :in-theory (enable mrdepsmap)))))

(local (defthm open-mrdepsmap-nonempty
         (implies (not (map::empty map))
                  (equal (mrdepsmap map)
                         (set::union (mrdeps (map::get (map::head map) map))
                                     (mrdepsmap (map::tail map)))))
         :hints(("Goal" :in-theory (enable mrdepsmap)))))


(encapsulate
 ()
 (local (defun my-induction (flag path x)
          (declare (xargs :measure (if (equal flag :dtree)
                                       (count x)
                                     (countmap x))))
          (if (equal flag :dtree)
              (my-induction :map path (children x))
            (if (map::empty x)
                path
              (list (my-induction :dtree 
                                  (cdr path) 
                                  (map::get (map::head x) x))
                    (my-induction :map path (map::tail x)))))))

 (local (defthm lemma
          (if (equal flag :dtree)
              (implies (and (in path x)
                            (set::in dep (localdeps (get path x))))
                       (set::in dep (mrdeps x)))
            (implies (and (consp path)
                          (map::in (car path) x)
                          (in (cdr path) (map::get (car path) x))
                          (set::in dep (localdeps 
                                         (get (cdr path) 
                                              (map::get (car path) x)))))
                     (set::in dep (mrdepsmap x))))
          :rule-classes nil
          :hints(("Goal" :in-theory (enable get)
                  :induct (my-induction flag path x)))))
       
 (defthm in-mrdeps-when-in-localdeps
   (implies (and (in path x)
                 (set::in dep (localdeps (get path x))))
            (set::in dep (mrdeps x)))
   :hints(("Goal" :use (:instance lemma (flag :dtree)))))
 )






;; FINDING THE CAUSES OF DEPENDENCIES
;;
;; To conduct a membership proof of equivalence between mrdeps and deps, we
;; would like show that any member of (mrdeps dtree) is also in (deps dtree),
;; and vice versa.  Recall that both mrdeps and deps are essentially big unions
;; of many localdeps within a tree.  This makes it difficult to relate, say,
;; (in a (mrdeps dtree)) versus (in a (deps dtree)), because we are never very
;; sure "where" a comes from, i.e., which localdeps was it part of originally?
;;
;; To help answer this question, we write two functions (one for deps, and one
;; for mrdeps) that will go and "find" the proper path for us to look at.  For
;; each of these functions, we want to establish the following properties:
;;
;;  (1) whenever a is in the deps of the dtree, the "find" function returns a
;;  valid path into the dtree when instructed to find a.
;;
;;  (2) whenever a is in the deps of the dtree, then a is also a member of the
;;  localdeps of the dtree obtained by looking up the path returned by "find"
;;  in the dtree.
;;
;; Our find function for deps is relatively straightforward, but the find
;; function for mrdeps is, itself, mutually recursive.

(defund depsource1 (a locs dtree)
  (declare (xargs :guard (and (set::setp locs)
                              (dtreep dtree))))
  (if (set::empty locs)
      nil
    (if (set::in a (localdeps (get (set::head locs) dtree)))
        (set::head locs)
      (depsource1 a (set::tail locs) dtree))))

(defund depsource (a dtree)
  (declare (xargs :guard (dtreep dtree)))
  (depsource1 a (domain dtree) dtree))


;; We first establish our desired properties for depsource.  Towards this
;; end, we prove the corresponding properties for deps1, and then the proofs
;; for deps are just simple consequences.

(defthm in-depsource1-when-in-deps1
  (implies (set::in a (deps1 locs dtree))
           (set::in (depsource1 a locs dtree) locs))
  :hints(("Goal" :in-theory (enable deps1 depsource1))))

(local (defthm true-listp-of-depsource1
         (implies (set::all<true-listp> locs)
                  (true-listp (depsource1 a locs dtree)))
         :hints(("Goal" :in-theory (enable depsource1)))))

(defthm in-deps1-is-in-localdeps-of-get-depsource1
  (implies (not (set::in a (localdeps dtree)))
           (equal (set::in a (deps1 locs dtree))
                  (set::in a (localdeps 
                               (get (depsource1 a locs dtree) dtree)))))
  :hints(("Goal" :in-theory (enable deps1 depsource1))))


(encapsulate
 ()

 (local (defthmd lemma
          (implies (set::in a (deps dtree))
                   (set::in (depsource a dtree) (domain dtree)))
          :hints(("Goal" :in-theory (enable depsource deps)))))
 
 (defthm in-depsource-when-in-deps
   (implies (set::in a (deps dtree))
            (in (depsource a dtree) dtree))
   :hints(("Goal" :use (:instance lemma))))

 )


(encapsulate
 ()

 (local (defthm lemma
          (implies (and (set::in a (localdeps dtree))
                        (set::in nil locs))
                   (set::in a (deps1 locs dtree)))
          :hints(("Goal" :in-theory (enable deps1)))))
 
 (local (defthm lemma2
          (implies (and (set::in a (localdeps dtree))                       
                        (set::in nil locs)
                        (set::all<true-listp> locs))
                   (set::in (depsource1 a locs dtree) (domain dtree)))
          :hints(("Goal" :in-theory (enable depsource1)))))
 
 (local (defthm lemma3
          (implies (and (set::in a (localdeps dtree))
                        (set::in nil locs))
                   (set::in a (localdeps (get (depsource1 a locs dtree)
                                               dtree))))
          :hints(("Goal" :in-theory (enable depsource1)))))
 
 (defthm in-localdeps-of-get-depsource
   (equal (set::in a (localdeps (get (depsource a dtree) dtree)))
          (set::in a (deps dtree)))          
   :hints(("Goal" 
           :in-theory (e/d (depsource deps)
                           (in-deps1-is-in-localdeps-of-get-depsource1))
           :use (:instance in-deps1-is-in-localdeps-of-get-depsource1
                           (locs (domain dtree))))))
 )




(mutual-recursion

 (defund mrdepsource (a dtree)
   (declare (xargs :guard (dtreep dtree)
                   :measure (count dtree)
                   :verify-guards nil))
   (if (set::in a (localdeps dtree))
       (mv t nil)
     (mrdepsourcemap a (children dtree))))
 
 (defund mrdepsourcemap (a map)
   (declare (xargs :guard (dtreemapp map)
                   :measure (countmap map)
                   :verify-guards nil))
   (if (map::empty-exec map)
       (mv nil nil)
     (mv-let (foundp path)
             (mrdepsource a (map::get (map::head map) map))
             (if foundp
                 (mv t (cons (map::head map) path))
               (mrdepsourcemap a (map::tail map))))))

 )

(local (in-theory (enable mrdepsource)))

;; Again we need some opener theorems in order to get these mutually recursive
;; definitions to expand properly.  We only define these locally because these
;; aren't good general purpose strategies.  Basically, these just save us a lot
;; of :expand hints.

(local (defthm open-mrdepsourcemap-empty
         (implies (map::empty map)
                  (equal (mrdepsourcemap a map)
                         (mv nil nil)))
         :hints(("Goal" :in-theory (enable mrdepsourcemap)))))

(local (defthm open-mrdepsourcemap-nonempty
         (implies (not (map::empty map))
                  (equal (mrdepsourcemap a map)
                         (mv-let (foundp path)
                                 (mrdepsource a (map::get (map::head map) map))
                                 (if foundp
                                     (mv t (cons (map::head map) path))
                                   (mrdepsourcemap a (map::tail map))))))
         :hints(("Goal" :in-theory (enable mrdepsourcemap)))))


(encapsulate
 ()

 ;; Now we turn our attention to mrdeps.  These theorems are more complicated.
 ;; We start by showing that whenever a is an element of (mrdeps x), the foundp
 ;; part of mrdepsources is true.

 (local (defthm lemma
          (if (equal flag :dtree)
              (equal (set::in a (mrdeps x))
                     (mv-nth 0 (mrdepsource a x)))             
            (equal (set::in a (mrdepsmap x))
                   (mv-nth 0 (mrdepsourcemap a x))))           
          :rule-classes nil
          :hints(("Goal" 
                  :in-theory (enable mrdeps)
                  :induct (mrdeps-induct flag x)))))
        

 ;; We next show that whenever the foundp part of mrdeps is true, the path part
 ;; is "in" the dtree.  This proof is actually rather complicated to state, and
 ;; we need our notion of in-map again.  Basically, we want the following:
 ;;
 ;;   Given a dtree, dtree.
 ;;   Given an element, a, such that (mv-nth 0 (mrdepsource a dtree))
 ;;   Show that (in (mv-nth 1 (mrdepsource a dtree)) dtree)
 ;;
 ;; To make this work, we will need the corresponding property for maps.  Of
 ;; course, in-map is ill defined, but we use it below anyway:
 ;;
 ;;   Given a dtree map, map.
 ;;   Given an element, a, such that (mv-nth 0 (mrdepsourcemap a map))
 ;;   Show that (in-map (mv-nth 1 (mrdepsourcemap a map)) map)
 ;;
 ;; Where (in-map e map) is understood to mean 
 ;;  (and (set::in (car e) (map::domain map))
 ;;       (in (cdr e) (map::get (car e) map)))

 (local (defthm lemma2
          (if (equal flag :dtree)
              (implies (mv-nth 0 (mrdepsource a x))
                       (in (mv-nth 1 (mrdepsource a x)) x))
            (implies (mv-nth 0 (mrdepsourcemap a x))
                     (and (set::in (car (mv-nth 1 (mrdepsourcemap a x)))
                                    (map::domain x))
                          (in (cdr (mv-nth 1 (mrdepsourcemap a x)))
                              (map::get (car (mv-nth 1 (mrdepsourcemap a x)))
                                      x)))))
          :rule-classes nil
          :hints(("Goal" :in-theory (enable in)
                  :induct (mrdeps-induct flag x)))))


 ;; Our domain property can now be obtained just by chaining together these
 ;; lemmas.

 (defthm mrdepsource-in-dtree
   (implies (set::in a (mrdeps dtree))
            (in (mv-nth 1 (mrdepsource a dtree)) dtree))
   :hints(("Goal" 
           :use ((:instance lemma
                            (flag :dtree)
                            (x dtree))
                 (:instance lemma2
                            (flag :dtree)
                            (x dtree))))))


 ;; The get proof is similar.  For the dtree case, we want:
 ;;
 ;;  Given a dtree, dtree.
 ;;  Given an element, a, such that (mv-nth 0 (mrdepsource a dtree))
 ;;  Show that (set::in a (localdeps (get path dtree)))
 ;;    Where path = (mv-nth 1 (mrdepsource a dtree))
 ;;
 ;; And for the map case, we need to use the idea of get-map, which is 
 ;; similar to in-map above.
 ;;
 ;;  Given a map, map.
 ;;  Given an element, a, such that (mv-nth 0 (mrdepsourcemap a map))
 ;;  Show that (set::in a (localdeps (get-map path map)))
 ;;    Where path = (mv-nth 1 (mrdepsourcemap a map))
 ;;    Where (get-map e map) = (get (cdr e) 
 ;;                                       (map::get (car e) map))

 (local (defthm lemma3
          (if (equal flag :dtree)
              (implies (mv-nth 0 (mrdepsource a x))
                       (set::in a (localdeps 
                                    (get (mv-nth 1 (mrdepsource a x))
                                            x))))
            (implies (mv-nth 0 (mrdepsourcemap a x))
                     (and (consp (mv-nth 1 (mrdepsourcemap a x)))
                          (map::in (car (mv-nth 1 (mrdepsourcemap a x))) x)
                          (set::in a (localdeps 
                                       (get 
                                        (cdr (mv-nth 1 (mrdepsourcemap a x)))
                                        (map::get (car (mv-nth 1 (mrdepsourcemap a x)))
                                                   x)))))))
          :rule-classes nil
          :hints(("Goal" :in-theory (enable get)
                  :induct (mrdeps-induct flag x)))))


 ;; And again, our property is an easy consequence of these lemmas.

 (defthm in-localdeps-of-get-when-in-mrdeps
   (implies (set::in a (mrdeps dtree))
            (set::in a (localdeps (get 
                                    (mv-nth 1 (mrdepsource a dtree))
                                    dtree))))
   :hints(("Goal" 
           :use ((:instance lemma
                            (flag :dtree)
                            (x dtree))
                 (:instance lemma3
                            (flag :dtree)
                            (x dtree))))))

 )




;; THE EQUIVALENCE PROOF
;;
;; We are now ready to prove the equivalence of mrdeps and deps.  Since both
;; are sets, all we need to do to prove their equality is prove that membership
;; in one is the same as membership in the other.
;;
;; Given: (set::in a (deps dtree))
;; Show:  (set::in a (mrdeps dtree))
;;
;; Let PATH = (depsource a dtree).  Then, by thm:depsource-get, we see
;; that since (in a (deps dtree)), it must also be the case that (in a
;; (localdeps (get PATH dtree))))) as well.  Also, note that by
;; thm:depsource-in-domain, we see that (in PATH dtree).  These two facts
;; together relieve the hyps of thm:in-mrdeps-by-localdeps, which concludes
;; that (set::in a (mrdeps dtree)), and we are done. QED.
;;
;; The vice-versa case is just the same, but with mrdepsource instead.
      
(local (defthm in-mrdeps-when-in-deps
         (implies (set::in a (deps dtree))
                  (set::in a (mrdeps dtree)))
         :hints(("Goal" :in-theory (disable in-mrdeps-when-in-localdeps)
                 :use ((:instance in-mrdeps-when-in-localdeps
                                  (dep a)
                                  (path (depsource a dtree))
                                  (x dtree)))))))

(local (defthm in-deps-when-in-mrdeps
         (implies (set::in a (mrdeps dtree))
                  (set::in a (deps dtree)))
         :hints(("Goal" :in-theory (disable in-deps-when-in-localdeps-of-get)
                 :use ((:instance in-deps-when-in-localdeps-of-get
                                  (a a)
                                  (path (mv-nth 1 (mrdepsource a dtree)))
                                  (dtree dtree)))))))
         
(defthm mrdeps-is-deps
  (equal (mrdeps dtree)
         (deps dtree)))

(defthm mrdepsmap-is-depsmap
  (equal (mrdepsmap map)
         (depsmap map))
  :hints(("Goal" :in-theory (e/d (mrdepsmap depsmap)
                                 (set::double-containment)))))

(verify-guards deps
  :hints(("Goal" :in-theory (enable deps)
          :use ((:instance mrdeps-is-deps)))))

(verify-guards depsmap
  :hints(("Goal" :in-theory (enable depsmap)
          :use ((:instance mrdepsmap-is-depsmap)))))





;; GENERAL PURPOSE REASONING ABOUT DEPS AND DEPSMAP
;;
;; Most of what we have done so far has been bent on proving the above
;; equivalence between the mutually recursive and domain-oriented versions of
;; deps.  We now provide some more general purpose rewrite rules.

(defthm deps1-of-dtreefix
  (equal (deps1 locs (dtreefix dtree))
         (deps1 locs dtree))
  :hints(("Goal" :in-theory (e/d (deps1) 
                                 (set::double-containment)))))

(defthm deps-of-dtreefix
  (equal (deps (dtreefix dtree))
         (deps dtree))
  :hints(("Goal" :in-theory (enable deps))))

(defthm depsmap-when-empty
  (implies (map::empty map)
           (equal (depsmap map) 
                  (set::emptyset)))
  :hints(("Goal" :in-theory (enable depsmap))))

(defthm in-depsmap-when-in-deps-of-get
  (implies (and (map::in key map)
                (set::in a (deps (map::get key map))))
           (set::in a (depsmap map)))
  :hints(("Goal" :in-theory (enable depsmap))))

(defthm in-deps-of-get-when-not-in-depsmap
  (implies (and (map::in key map)
                (not (set::in a (depsmap map))))
           (equal (set::in a (deps (map::get key map)))
                  nil)))

(defthm in-depsmap-when-submap
  (implies (and (submap sub super)
                (set::in a (depsmap sub)))
           (set::in a (depsmap super)))
  :hints(("Goal" :in-theory (enable depsmap))
         ("Subgoal *1/3" 
          :in-theory (e/d (depsmap) 
                          (equal-of-gets-when-submap))
          :use (:instance equal-of-gets-when-submap
                          (map::key (map::head sub))
                          (map::sub sub)
                          (map::super super)))
         ("Subgoal *1/2" 
          :in-theory (e/d (depsmap) 
                          (map::submap-transitive-one
                           map::submap-transitive-two))
          :use (:instance map::submap-transitive-one
                          (x (map::tail sub))
                          (y sub)
                          (z super)))))

(defcong map::equiv equal (depsmap map) 1
  :hints(("Goal" :in-theory (enable map::equiv))))



(local (defund findtree (a map)
         (if (map::empty map)
             nil
           (if (set::in a (deps (map::get (map::head map) map)))
               (map::head map)
             (findtree a (map::tail map))))))
 
(local (defthm findtree-works
         (implies (set::in a (depsmap map))
                  (and (map::in (findtree a map) map)
                       (set::in a (deps (map::get (findtree a map) map)))))
         :hints(("Goal" :in-theory (enable depsmap findtree)))))
 
(defthm in-depsmap-when-in-depsmap-of-erase
  (implies (set::in a (depsmap (map::erase name map)))
           (set::in a (depsmap map)))
  :hints(("Goal" :in-theory (enable depsmap))
         ("Subgoal *1/2"
          :use (:instance findtree-works
                          (a a)
                          (map (map::erase name map))))))
                            
(defthm in-deps-when-not-in-erase-from-map
  (implies (and (set::in a (depsmap map))
                (not (set::in a (depsmap (map::erase name map)))))
           (set::in a (deps (map::get name map))))
  :hints(("Goal" :in-theory (enable depsmap))
         ("Subgoal *1/3"
          :use (:instance findtree-works
                          (a a)
                          (map (map::erase name (map::tail map)))))
         ("Subgoal *1/2"
          :use (:instance in-depsmap-when-in-deps-of-get
                          (key (map::head map))
                          (map (map::erase name map))))))








