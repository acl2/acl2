#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;;
;; Extending Maps with Types
;; Jared Davis 
;;
;;
;; INTRODUCTION
;;
;; We build off of the work in maps.lisp, providing a generic theory of typed
;; maps along with several theorems that can be functionally instantiated to
;; prove concrete theorems about typed maps.
                                   
(in-package "MAP")
(include-book "maps")

;; We first set up a generic predicate that should be used to describe the
;; relationship between key and value.  Note that you don't need to actually
;; write a separate function for your predicate, e.g., look how the "lambda" is
;; used in the example above.

(encapsulate
 (((predicate * *) => *))

 (local (defun predicate (key val)
          (declare (ignore key val))
          t))

 (defthmd predicate-boolean
   (or (equal (predicate key val) nil)
       (equal (predicate key val) t))
   :rule-classes :type-prescription)
 )

(local (in-theory (enable predicate-boolean)))

;; Originally tried to force typed-mapp to also check that its argument was a
;; map.  However, I have found that dropping this requirement makes it much
;; easier to work with typed maps.  For example, equiv is now an equivalence
;; relation over typed-mapp.

(defun typed-mapp (map)
  (or (empty map)
      (and (predicate (head map) (get (head map) map))
           (typed-mapp (tail map)))))

(defthm predicate-when-in-typed-mapp
  (implies (and (typed-mapp map)
                (in a map))
           (predicate a (get a map))))

(defthm not-typed-mapp-when-bad-member
  (implies (and (in a map)
                (not (predicate a (get a map))))
           (not (typed-mapp map))))

(encapsulate
 (((typed-mapp-hyps) => *)
  ((typed-mapp-map) => *))
 
 (local (defun typed-mapp-hyps () nil))
 (local (defun typed-mapp-map () nil))
 
 (defthm typed-mapp-membership-constraint
   (implies (and (typed-mapp-hyps)
                 (in typed-mapp-key (typed-mapp-map)))
            (predicate typed-mapp-key
                       (get typed-mapp-key (typed-mapp-map))))))
 
(local (defun typed-mapp-badguy (map)
         (if (empty map)
             nil
           (if (predicate (head map) (get (head map) map))
               (typed-mapp-badguy (tail map))
             (head map)))))

(local (defthm typed-mapp-badguy-witnesses
         (implies (and (not (typed-mapp map)))
                  (and (in (typed-mapp-badguy map) map)
                       (not (predicate (typed-mapp-badguy map)
                                       (get (typed-mapp-badguy map) map)))))
         :rule-classes nil))

(defthmd typed-mapp-by-membership
  (implies (typed-mapp-hyps)
           (typed-mapp (typed-mapp-map)))
  :hints(("Goal" :use (:instance typed-mapp-badguy-witnesses
                                 (map (typed-mapp-map))))))
 

(encapsulate
 ()

 (local (defthm lemma1
          (implies (and (typed-mapp map)
                        (predicate key val))
                   (typed-mapp (set key val map)))
          :hints(("Goal" 
                  :use (:functional-instance
                        typed-mapp-by-membership
                        (typed-mapp-hyps 
                         (lambda () (and (typed-mapp map)
                                         (predicate key val))))
                        (typed-mapp-map 
                         (lambda () (set key val map))))))))

 (local (defthm lemma2
          (implies (not (predicate key val))
                   (not (typed-mapp (set key val map))))
          :hints(("Goal"
                  :use (:instance not-typed-mapp-when-bad-member
                                  (a key)
                                  (map (set key val map)))))))

 (defthm typed-mapp-of-set
   (implies (typed-mapp map)
            (equal (typed-mapp (set key val map))
                   (predicate key val)))
   :hints(("Goal" :use ((:instance lemma1)
                        (:instance lemma2)))))
 
 )
                                 
(defthm typed-mapp-of-erase
  (implies (typed-mapp map)
           (typed-mapp (erase key map)))
  :hints(("Goal" :use (:functional-instance
                       typed-mapp-by-membership
                       (typed-mapp-hyps 
                        (lambda () (typed-mapp map)))
                       (typed-mapp-map 
                        (lambda () (erase key map)))))))


(encapsulate
 ()

 (local (defthm lemma1
          (implies (and (equiv x y)
                        (typed-mapp x))
                   (typed-mapp y))
          :hints(("Goal" 
                  :use (:functional-instance
                        typed-mapp-by-membership
                        (typed-mapp-hyps 
                         (lambda () (and (equiv x y)
                                         (typed-mapp x))))
                        (typed-mapp-map
                         (lambda () y)))))))

 (local (defthm lemma2
          (implies (and (equiv x y)
                        (not (typed-mapp x)))
                   (not (typed-mapp y)))))

 ;; This generates a theorem named equiv-implies-equal-typed-mapp-1,
 ;; in case you want to functionally instantiate it.
 (defcong equiv equal (typed-mapp map) 1
   :hints(("Goal" :cases ((typed-mapp map)))))

 )

