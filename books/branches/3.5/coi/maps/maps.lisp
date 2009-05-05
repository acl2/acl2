#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;;
;; Simple Equivalence-Based Maps for ACL2
;; Jared Davis 
;;
;;
;; INTRODUCTION
;;
;; We provide a straightforward implementation of maps (commonly called records
;; or finite functions).  We provide the following basic operations:
;;
;;   (mapp map)              a simple map recognizer function
;;   (emptymap)              macro, an empty map with no elements (nil)
;;   (fix map)               standard "fixing" function, returns a map
;;   (optimize map)          like fix, but more expensive and compresses map
;;   (domain map)            returns the set of all keys bound by the map
;;   (get key map)           returns the value that key is bound to in map
;;   (set key val map)       creates a new map with key bound to val
;;   (erase key map)         removes key from the domain of map
;;   (in key map)            macro, abbreviates (set::in key (domain map))
;;
;;
;; We also provide the following relations between maps:
;;
;;   (submap sub super)      returns true iff both:
;;                            (1) sub's domain is a subset of super's domain
;;                            (2) every key in sub has the same value in sub
;;                                as it does in super
;;
;;   (equiv x y)             returns true iff both:
;;                            (1) x and y have the same domain, and
;;                            (2) every key in this shared domain has the 
;;                                same value in both maps
;;
;;
;; Finally, we provide some utilities to allow you to recur down maps.
;;
;;   (head map)              returns some arbitrary key from the map
;;   (tail map)              macro, abbreviation for (erase (head map) map)
;;   (empty map)             macro, abbreviation for (set::empty (domain map))
;;   (empty-exec map)        faster executing function which rewrites to empty
;;
;;
;; NORMAL FORMS AND OUR INTENDED REWRITING STRATEGY
;;
;; When using the maps library, you should be aware that the functions
;; emptymap, empty, in, and tail are just macros that will be expanded away.
;; However, we add untranslate patterns to make the output look more readable,
;; so that these macros feel like they are real functions.  These are "simple
;; abbreviations" that still work well in rewrite rules, although you should
;; probably avoid using "tail" in rewrite rules if you can prove more general
;; rules about "empty" itself.
;;
;; When you are writing functions that recur over maps, you should prefer to
;; write "empty-exec" instead of "empty" in your base cases.  This function
;; should never be the target of rewrite rules -- instead, it will be always
;; unconditionally rewritten into "empty" immediately.  We only define this
;; function because it avoids calling "domain", effectively reducing an O(n log
;; n) operation to a fast O(1) check.
;;
;; When you load the maps library, every function above is disabled.  And, with
;; the exceptions of "submap" and "equiv", we expect that this should always
;; be the case.  A theory invariant will complain if you ever try to enable
;; these functions, but it will not go so far as to stop you.  You are strongly
;; discouraged from enabling them.
;;
;;
;;
;; COMPARISON WITH MISC/RECORDS
;;
;; Our library is similar to the efforts in misc/records.lisp, but is different
;; in a few notable ways.
;;
;;
;; 1.  Equality versus Equivalence Reasoning
;;
;; Perhaps most visibly, our library gives up the persuit of equal in favor of
;; equivalence based reasoning.  As a result, our variations of the five major
;; record theorems are not quite as nice as those rules in the misc/records
;; book, and our users will need to be mindful of proving the appropriate
;; congruence rules.
;;
;; In exchange for this sacrifice, we are able to provide many "sensible" rules
;; that misc/records has a hard time proving or cannot even prove.  An example:
;; we can prove that (get key map) has is "smaller" than map, allowing users to
;; write mutually-recursive functions that operate over maps.  In contrast, g
;; (the get function in misc/records) has bizarre properties when faced with
;; the nil key, such as (g nil 0) = 0.  As a result, reasoning admitting
;; mutually recursive functions over records can be quite difficult.
;;
;;
;; 2. Map Domains versus Record Key Sets
;; 
;; Our library also provides a well defined notion of a map's domain.  In the
;; records book, there is no such explicit notion.
;; 
;; With some work, we can define, say, "keys" which returns the set of keys
;; which have a non-nil value in a record.  But, this is not really as flexible
;; as we would like -- for example, we cannot (s a val r) and expect a to be a
;; member of r's domain, because val might have been nil.
;;
;; Whereas the records library only has one updating function, s, our library
;; provides two: set and erase.  We define our maps' domains as the set of keys
;; which are bound to some value in the map, and we allow our keys to be bound
;; even to the default value, (default).  As a result, the domain of our maps
;; are predictable: after (set key val map), one is sure that key is a member
;; of the domain no matter what val is, and after (erase key map), one can be
;; sure that the key is gone.
;;
;;
;; 3. The Default Value and Unbound Keys
;;
;; Another difference is our treatment of unbound keys in maps.  The records
;; book treats all unbound keys as if they had the value nil.  Instead, we
;; interpret unbound keys as having the value (default), where default is a
;; constrained function of zero arguments which we know nothing about.
;;
;; As a result, in our library it is an error to call (get key map) at runtime
;; if key is not in the domain of map.  We hope that this is sensible and may
;; help catch errors: after all, typically data should be initialized before it
;; is used.
;;
;;
;;
;; GENERAL COMMENTS ABOUT OUR IMPLEMENTATION
;;
;; Our hope is that our actual implementation need not be examined by the user
;; of the map library.  Furthermore, we strongly discourage relying upon the
;; specific details of our implementation in "external" code, because this
;; violates the principle of abstraction.  
;;
;; Nevertheless, surely there are choices we have made that we should document
;; for anyone who is interested in reimplementing maps or modifying this file
;; and so forth.  We explain these decisions here.
;;
;; Internally our maps are just alists.  We don't use any tricks to try to
;; standardize them or order them, because we are primarily interested in our
;; equivalence relation alone and not in demonstrating equality.
;;
;; Our functions "expect" to receive proper alists as inputs, but in order to
;; achieve better rules, we coerce bad objects into alists by treating any
;; atomic objects as nil, coercing any non true-lists into true-lists, and
;; ignoring all non-pairs that might occur in our input lists.
;;
;; This "non-pair" convention has been useful, and seems to be "more right"
;; than treating non-pairs as (nil . nil).  Particularly, it allows one to
;; maintain the count theorems we are interested in.  For example, if we give
;; the "erase" function the list (1 2 3 4 (a . b)) and tell it to erase key c,
;; then our implementation simply drops the atoms and returns ((a . b)).  We
;; are thus assured that erasing elements from a list will always decrease its
;; acl2-count.
;;
;; You might recall that the alists library takes the opposite approach, using
;; (nil . nil) as its standardization of atoms.  This has the nice property
;; that the length of the alist is always the same after standardization.  We
;; don't have any such rule, but then we never talk about the "length" of a
;; map.  The cardinality of the map's domain serves a similar function.  Maybe
;; this is an insight -- len makes sense when applied to lists, but maybe there
;; should be some kind of alist-len function instead.
;; 
;; We have not concerned ourselves much with runtime efficiency.  Originally we
;; wrote our primitive list-like operations (head, tail) using the set
;; operations on the domain of the map.  In other words, (empty map) was
;; (set::empty (domain map)), (head map) was (set::head (domain map)), and
;; (tail map) was (erase (head map) map).  This was very inefficient because we
;; had to reconstruct the entire domain for each operation, although at least
;; we could define empty-exec to be a faster version of empty that just asked
;; (null map).
;;
;; We have since then changed our implementations of head and tail, so that
;; instead of returning the set::head of the domain, head simply returns the
;; first element that happens to be in the alist.  Because "set" is like acons,
;; this order is unpredictable, but it allows head to be O(1) rather than O(n
;; log n).  Tail also benefits, since it calls head, but is still O(n) since it
;; must walk down the rest of the list (to erase all instances of the head.)
;; Inductive proofs might sometimes be harder because of this lack of order.
;;
;; Another issue is that our "set" function is essentially an abbreviation for
;; acons.  This makes updating records quite fast, but potentially means that
;; records could become very large!  The optimize function can be used to eat
;; these duplicates, but of course it is O(n^2) and so it should really only be
;; used if space is really an issue.  For this reason, none of our functions
;; "optimize" their results.

(in-package "MAP")

(include-book "../osets/sets")
(include-book "../adviser/adviser")
(include-book "misc/untranslate-patterns" :dir :system)

(local (defthm equal-of-booleans-rewrite
         (implies (and (booleanp x)
                       (booleanp y))
                  (equal (equal x y)
                         (iff x y)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(encapsulate
 (((default) => *))
 (local (defun default () nil)))




(defmacro emptymap ()
  nil)

(defund mapp (map)
  (declare (xargs :guard t))
  (alistp map))

;; We don't want to export this theorem, because we don't want to expose the
;; underlying implementation of maps.
(local (defthm alistp-when-mapp
         (implies (mapp x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable mapp)))))


(defund domain (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map) 
                     (set::emptyset))
                    ((atom (car map)) 
                     (domain (cdr map)))
                    (t (set::insert (caar map)
                                     (domain (cdr map)))))
       :exec (set::mergesort (strip-cars map))))

(verify-guards domain
  :hints(("Goal" :in-theory (enable mapp domain))))

(defthm setp-of-domain
  (set::setp (domain map))
  :hints(("Goal" :in-theory (enable domain))))


(defmacro in (key map)
  `(set::in ,key (domain ,map)))



(defund erase (key map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     (emptymap))
                    ((atom (car map))
                     (erase key (cdr map)))
                    ((equal (caar map) key)
                     (erase key (cdr map)))
                    (t (cons (car map)
                             (erase key (cdr map)))))
       :exec (cond ((atom map)
                    nil)
                   ((equal (caar map) key)
                    (erase key (cdr map)))
                   (t (cons (car map)
                            (erase key (cdr map)))))))

(verify-guards erase
  :hints(("Goal" :in-theory (enable mapp erase))))

(defthm mapp-of-erase
  (mapp (erase key map))
  :hints(("Goal" :in-theory (enable mapp erase))))

(defthm domain-of-erase
  (equal (domain (erase key map))
         (set::delete key (domain map)))
  :hints(("Goal" :in-theory (enable erase domain))))

(defthm acl2-count-of-erase-strong-linear
  (implies (in key map)
           (< (acl2-count (erase key map))
              (acl2-count map)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable erase domain)
          :induct (erase key map))))                

(defthm acl2-count-of-erase-weak-linear
  (<= (acl2-count (erase key map))
      (acl2-count map))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable erase)
          :induct (erase key map))))



(defund fix (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     nil)
                    ((atom (car map))
                     (fix (cdr map)))
                    (t (cons (car map)
                             (fix (cdr map)))))
       :exec map))

(defthm mapp-of-fix
  (mapp (fix map))
  :hints(("Goal" :in-theory (enable mapp fix))))

(defthm fix-when-mapp
  (implies (mapp map)
           (equal (fix map)
                  map))
  :hints(("Goal" :in-theory (enable mapp fix))))

(verify-guards fix
  :hints(("Goal" :in-theory (enable mapp fix))))

;; We will soon prove a stronger congruence rule, so we don't need to export
;; this theorem.
(local (defthm domain-of-fix
         (equal (domain (fix map))
                (domain map))
         :hints(("Goal" :in-theory (enable domain fix)))))

(defthm acl2-count-of-fix-weak-linear
  (<= (acl2-count (fix map))
      (acl2-count map))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable fix))))



(defund set (key val map)
  (declare (xargs :guard (mapp map)))
  (mbe :logic (acons key val (fix map))
       :exec (cons (cons key val) map)))

(defthm mapp-of-set
  (mapp (set key val map))
  :hints(("Goal" :in-theory (enable mapp set))))

(defthm domain-of-set
  (equal (domain (set key val map))
         (set::insert key (domain map)))
  :hints(("Goal" :in-theory (enable domain set))))

;; We will soon prove a stronger congruence rule, so we don't need to export
;; this theorem.
(local (defthm set-of-fix
         (equal (set key val (fix map))
                (set key val map))
         :hints(("Goal" :in-theory (enable set fix)))))


;; DAG The default thing was too strong.

(defund get (key map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     (emptymap))
                    ((atom (car map))
                     (get key (cdr map)))
                    ((equal (caar map) key)
                     (cdar map))
                    (t (get key (cdr map))))
       :exec (cond ((atom map)
                    (emptymap))
                   ((equal (caar map) key)
                    (cdar map))
                   (t (get key (cdr map))))))

(verify-guards get
  :hints(("goal" :in-theory (enable mapp get))))

(defthm get-when-not-in
  (implies (not (in key map))
           (equal (get key map)
                  (emptymap)))
  :hints(("Goal" :in-theory (enable domain get))))

;; We will soon prove a stronger congruence rule, so we don't need to export
;; this theorem.
(local (defthm get-of-fix
         (equal (get key (fix map))
                (get key map))
         :hints(("Goal" :in-theory (enable get fix)))))

(defthm get-of-set
  (equal (get key1 (set key2 val map))
         (if (equal key1 key2)
             val
           (get key1 map)))
  :hints(("Goal" :in-theory (enable get set))))

(defthm get-of-erase
  (equal (get key1 (erase key2 map))
         (if (equal key1 key2)
             (emptymap)
           (get key1 map)))
  :hints(("Goal" :in-theory (enable get erase))))

(defthm acl2-count-of-get-strong-linear
  (implies (in key map)
           (< (acl2-count (get key map))
              (acl2-count map)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable get domain))))



(defund optimize (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     nil)
                    ((atom (car map))
                     (optimize (cdr map)))
                    (t (cons (car map)
                             (optimize
                              (erase (caar map) (cdr map))))))
       :exec (cond ((atom map)
                     nil)
                    (t (cons (car map)
                             (optimize 
                              (erase (caar map) (cdr map))))))))

(verify-guards optimize
  :hints(("Goal" :in-theory (enable mapp optimize))))

(defthm acl2-count-of-optimize-weak-linear
  (<= (acl2-count (optimize map))
      (acl2-count map))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable optimize))))

;; We don't export this because our congruence rule for domain is better.
(local (defthm domain-of-optimize
         (equal (domain (optimize map))
                (domain map))
         :hints(("Goal" :in-theory (enable domain optimize)))))

;; We don't export this because our congruence rule for get is better.
(local (defthm get-of-optimize
         (equal (get key (optimize map))
                (get key map))
         :hints(("Goal" :in-theory (enable get optimize)))))




;; Defining "empty" properly has taken a lot of thought.  On one hand, for the
;; purposes of reasoning, I'd prefer to never talk about "empty maps", rather
;; I'd prefer to talk about "maps with empty domains".  But, for the purposes
;; of execution, we'd prefer to MBE in a simple test that the map is null.
;; Eventually, I decided to make "empty-exec" a function that can be used for
;; fast execution, and hopefully the "exec" in its name will prevent anyone
;; from mistakenly writing rules about it.  We immediately rewrite it to
;; "empty", a simple macro abbreviation for emptiness of its domain.

(defmacro empty (map)
  `(set::empty (domain ,map)))

(defund empty-exec (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (empty map)
       :exec (null map)))

(verify-guards empty-exec
  :hints(("Goal" :in-theory (enable empty-exec mapp domain))))

(defthm empty-exec-is-empty
  (equal (empty-exec map)
         (empty map))
  :hints(("Goal" :in-theory (enable empty-exec))))

;; We impose a strong theory invariant that causes an error if anyone should
;; ever try to enable empty-exec.  Surely you should reason about "empty"
;; instead.

;; DAG -- we really shouldn't bomb out when nothing really bad will happen.

(theory-invariant
 ;(not (member-equal '(:definition empty-exec) theory))
 (not (active-runep '(:definition empty-exec)))
 :error nil)


(defund head (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     nil)
                    ((atom (car map))
                     (head (cdr map)))
                    ((caar map)))
       :exec (caar map)))

(verify-guards head
  :hints(("Goal" :in-theory (enable head mapp))))

(defthm in-head
  (equal (in (head map) map)
         (not (empty map)))
  :hints(("Goal" :in-theory (enable head domain))))



;; I've decided to make tail a macro rather than a function.  
;; Erasing the head of the map is no different than erasing any other
;; key, but this is a convenience abbreviation.

(defmacro tail (map)
  `(erase (head ,map) ,map))

;; We want to preserve our abstraction.  We implement the following
;; theory invariant which does not create errors, but will at least warn people
;; that the basic map functions should stay disabled.  If they violate this
;; that is sort of their own fault.

(theory-invariant
;;  (null (intersectp-equal '((:definition mapp)
;;                            (:definition domain)
;;                            (:definition erase)
;;                            (:definition fix)
;;                            (:definition set)
;;                            (:definition get)
;;                            (:definition compress)
;;                            (:definition head))
;;                          theory))
 (and (not (active-runep '(:definition mapp)))
      (not (active-runep '(:definition domain)))
      (not (active-runep '(:definition erase)))
      (not (active-runep '(:definition fix)))
      (not (active-runep '(:definition set)))
      (not (active-runep '(:definition get)))
      (not (active-runep '(:definition compress)))
      (not (active-runep '(:definition head))))
 :key basic-map-functions-should-stay-disabled
 :error nil)



                  
(defund submap (sub super)
  (declare (xargs :guard (and (mapp sub)
                              (mapp super))))
  (or (empty sub)
      (let ((head (head sub)))
        (and (in head super)
             (equal (get head sub)
                    (get head super))
             (submap (erase head sub) super)))))

(defthm in-when-in-submap
  (implies (and (submap sub super)
                (in key sub))
           (in key super))
  :hints(("Goal" :in-theory (enable submap))))

(defthm not-in-when-not-in-supermap
  (implies (and (submap sub super)
                (not (in key super)))
           (not (in key sub))))

(defthm subset-of-submap-domain-with-supermap-domain
  (implies (submap sub super)
           (set::subset (domain sub) 
                         (domain super))))


(defthm equal-of-gets-when-submap
  (implies (submap sub super)
           (equal (equal (get key sub) (get key super))
                  (if (in key sub)
                      t
                    (equal (get key super) (emptymap)))))
  :hints(("Goal" :in-theory (enable submap))))

(defthm empty-when-submap-of-empty-map
  (implies (and (submap sub super)
                (empty super))
           (empty sub))
  :hints(("Goal" :in-theory (enable submap))))

(defthm submap-of-anything-when-empty
  (implies (empty sub)
           (submap sub super))
  :hints(("Goal" :in-theory (enable submap))))

(defthm submap-of-empty-means-empty
  (implies (empty super)
           (equal (submap sub super)
                  (empty sub)))
  :hints(("Goal" :in-theory (enable submap))))



;; SUBMAP BY MEMBERSHIP
;;
;; A really powerful way to prove submap relationships is to employ the pick a
;; point method like the one used in the ordered sets library.  Here we set up
;; such a strategy and install the necessary computed hints in order to apply
;; it.  (See the "adviser" library for details.)

(encapsulate
 ()

 (encapsulate
  (((submap-hyps) => *)
   ((submap-sub) => *)
   ((submap-super) => *))
  
  (local (defun submap-hyps () nil))
  (local (defun submap-sub () nil))
  (local (defun submap-super () nil))
  
  (defthmd submap-membership-constraint
    (implies (submap-hyps)
             (implies (in submap-key (submap-sub))
                      (and (in submap-key (submap-super))
                           (equal (get submap-key (submap-sub))
                                  (get submap-key (submap-super)))))))
  
  )

 (local (defund submap-badguy (sub super)
          (declare (xargs :guard (and (mapp sub)
                                      (mapp super))))
          (cond ((empty sub)
                 nil)
                ((and (in (head sub) super)
                      (equal (get (head sub) sub)
                             (get (head sub) super)))
                 (submap-badguy (erase (head sub) sub)
                                super))
                (t (head sub)))))

 (local (defthmd submap-badguy-witness
          (equal (not (submap sub super))
                 (and (in (submap-badguy sub super) sub)
                      (or (not (in (submap-badguy sub super) super))
                          (not (equal (get (submap-badguy sub super) sub)
                                      (get (submap-badguy sub super) super))))))
          :hints(("Goal" 
                  :in-theory (enable submap submap-badguy)
                  :induct (submap-badguy sub super)))))
  
 (defthmd submap-by-membership-driver
   (implies (submap-hyps)
            (submap (submap-sub) (submap-super)))
   :hints(("Goal" 
           :use ((:instance submap-badguy-witness 
                            (sub (submap-sub))
                            (super (submap-super)))
                 (:instance submap-membership-constraint
                            (submap-key (submap-badguy (submap-sub) 
                                                       (submap-super))))))))

 (defadvice submap-by-membership
   (implies (submap-hyps)
            (submap (submap-sub) (submap-super)))
   :rule-classes (:pick-a-point :driver submap-by-membership-driver))
)

(defthm submap-reflexive
  (submap map map))

(defthm submap-transitive-one
  (implies (and (submap x y)
                (submap y z))
           (submap x z))
  :hints(("Goal" :in-theory (enable submap))))

(defthm submap-transitive-two
  (implies (and (submap x y)
                (submap y z))
           (submap x z)))

(defthm submap-of-erase-with-self
  (submap (erase key map) map))

(defthm submap-of-erase-with-erase-when-submap
  (implies (submap sub super)
           (submap (erase key sub)
                   (erase key super))))

(defthm submap-of-set-with-set-when-submap
  (implies (submap sub super)
           (submap (set key val sub)
                   (set key val super))))
               


(defund equiv (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y))))
  (and (submap x y)
       (submap y x)))

(defequiv equiv
  :hints(("Goal" :in-theory (enable equiv))))

(defthm fix-under-equiv
  (equiv (fix map)
         map)
  :hints(("Goal" :in-theory (enable equiv))))

(defthm optimize-under-equiv
  (equiv (optimize map)
         map)
  :hints(("Goal" :in-theory (enable equiv))))

(defthm equiv-with-empty-one
  (implies (empty x)
           (equal (equiv x y)
                  (empty y)))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm equiv-with-empty-two
  (implies (empty y)
           (equal (equiv x y)
                  (empty x)))
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equal (domain map) 1
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equal (get key map) 2
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equiv (erase key map) 2
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equiv (set key val map) 3
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equal (submap sub super) 1
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equal (submap sub super) 2
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equiv (fix map) 1
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equiv (optimize map) 1
  :hints(("Goal" :in-theory (enable equiv))))
   


;; The following rule is necessarily weaker than its variant in misc/records,
;; because of the way that the map's domain has been separated from its range.
          
(defthm set-of-get-same
  (equiv (set key (get key map) map)
         (if (in key map)
             map
           (set key (emptymap) map)))
  :hints(("Goal" :in-theory (enable equiv))))


;; bzo - We might want to add a rule like this?  
;;
;;  (implies (and (set::in key (domain map))
;;                (equal (get key map) val)))
;;           (equiv (set key val map) map))

;; Essay on Simplifying Erase/Erase Nests
;;
;; Eric and I spent a lot of time looking at how large nests of erases might be
;; most effectively simplified.  The best way to go is not entirely clear.  I
;; have gone ahead and written down some of our thoughts on the matter here.
;;
;;
;; BACKGROUND
;; 
;; Suppose you are trying to simplify a nest of erases, such as:
;;
;;  (erase k1 (erase k2 (erase k3 (erase k4 ... (erase kn X) ... ))))
;;
;; Becuase it really doesn't matter what order erases occur in, imagine a 
;; function ERASE* which erases a whole set of keys.  In other words, instead
;; of thinking of the above as a nest of erases, think of it as a single
;; function call (ERASE* {k1, k2, ..., kn} X).
;;
;; Our notion of progress is basically that, whenever A is a proper subset of
;; B, then (ERASE* A X) is better than (ERASE* B X).  So, our goal is to make
;; progress by noticing that keys can be eliminated.  What we would ideally 
;; like to do is ask, for every ki, 
;;
;;   Is ki in (dom (ERASE* {k1, k2, ..., k_{i-1}, k_{i+1}, ..., kn} X))?
;;
;; Because if we can show that it isn't, then we will know that we can remove
;; it from the set of keys to be erased, and hence we will have made progress.
;; There are two ways to establish that ki is not in this domain.
;;
;;   (1) show that ki is not even a member of X
;;   (2) show that ki is equal to kj for some j != i.
;;
;; We will largely ignore (1), since after all it should more or less be
;; handled by erase-nonmember.
;;
;; Given N keys, fully checking (1) would require N queries, and fully checking
;; (2) would require (N choose 2) = N * N-1 / 2 queries, i.e., O(n^2) queries.
;; Aside from the question of how to actually perform such queries, this could
;; potentially be an expensive operation as N grows large.
;;
;; One way to "query" the system is to aggressively case-split so that, for 
;; each query we would like to make (e.g., is k3 == k4?), we consider two
;; cases: (1) where k3 == k4 and (2) where k3 != k4.  These become explicit
;; hypotheses for the prover to consider, and now if it can show, say, that
;; k3 == k4, then case (2) becomes vacuously true and case (1) has a nice
;; piece of additional information which can be used to simplify the erase 
;; nest.
;;
;; But taken literally, this case splitting would introduce 2^|queries| cases.
;; And, since we said |queries| = N * N-1 / 2, this algorithm would be
;; O(2^{N^2}).  That's not encouraging at all, and furthermore -- these are
;; cases that the end user is going to have to wade through.  So, it seems
;; clear that we can't really take this approach.
;;
;; 
;; RESTRAINED SIMPLIFICATION
;;
;; Is it even our job to try to ask these questions?  After all, our goal is to
;; simplify a nest of erases.  If two of the keys happen to be equal, why
;; hasn't our user normalized them into a syntactically equal form?  After all,
;; if we have syntactic equality, then the job of removing redundant keys
;; becomes quite simple.  (All we need to do is sort the keys then eliminate
;; adjacent ones).
;;
;; We take the above paragraph as our "default position" on the matter.  And,
;; by default, we employ a simplification strategy that we call "restrained
;; simplification", which involves basically one new rule:
;;
;;   (equiv (erase key1 (erase key2 map))
;;          (erase key2 (erase key1 map)))
;;
;; It's important to note that this rule is used in concert with Theorem
;; erase-nonmember above.
;;
;; If the user has "done their job" and all semantically equal keys have been
;; rendered syntactically equal by other rewrite rules, then we believe this
;; strategy should be sufficient to render semantically equal erase nests
;; syntactically equal as well.  To see why this works, consider that the above
;; rule will fully order the keys under the term order (which is a total order
;; on terms? we hope?) and thus as long as there are no duplicate keys, the
;; nests will have been rendered syntactically identical.  Furthermore, we know
;; there will be no duplicate keys, because, of the theorems erase-nonmember,
;; domain-erase, and the simple membership properties of delete.
;;
;; We have found restrained simplification to be quite fast and effective at
;; solving many "reasonable" problems.
;;
;;
;; AGGRESSIVE SIMPLIFICATION
;;
;; We considered providing alternative rules which we call "aggressive."  These
;; rules are incompatible with the restrained versions (they target the same
;; term), and are thus disabled by default.  The aggressive rule is the
;; following:
;;
;;   (equiv (erase key1 (erase key2 map))
;;          (if (equal key1 key2)
;;              (erase key1 map)
;;            (erase key2 (erase key1 map))))
;;
;; The idea here is to force case splits.  Instead of simply reordering key1
;; and key2 if they are out of term order, we would like to force a case split
;; so that ACL2 will consider whether or not key1 and key2 are equal.  We
;; choose not to use this approach by default because it can quickly lead to a
;; large number of cases, and it can cause splits even when we know nothing
;; about the quality of key1 and key2 (i.e., bad splits that don't give us any
;; additional information).
;;
;; To aide our discussion, consider the following events:
;;
;;   (in-theory (disable equiv))
;;   (defstub foo1 (*) => *)
;;   (defstub foo2 (*) => *)
;;   (defstub foo3 (*) => *)
;;   (defstub foo4 (*) => *)
;;   (defstub foo5 (*) => *)
;;   (defstub foo6 (*) => *)
;;
;; Then, we might axiomatize rules, such as:
;;
;; Version 1.
;;   (equal (equal (foo1 x) (foo3 x))
;;          t)
;;
;; Version 2.
;;   (equal (foo1 x)
;;          (foo3 x))
;;
;; Version 1 will allow us to simulate what happens if the system can prove
;; (foo1 x) and (foo3 x) are equal, but has not been given an explicit rewrite
;; rule to choose one of these as a normal form.  Version 2 is what happens if
;; the user "correctly" chooses a normal form.
;;
;; To begin with, suppose we only enable Version 1.  As a simple benchmark, we
;; might consider the following theorem:
;;
;; (thm
;;   (equiv (erase (foo1 x) 
;;                 (erase (foo2 x) 
;;                        (erase (foo3 x) 
;;                               (erase (foo4 x)
;;                                      (erase (foo5 x) 
;;                                             (erase (foo6 x) 
;;                                                    Y))))))
;;          (erase (foo3 x) 
;;                 (erase (foo2 x) 
;;                        (erase (foo4 x) 
;;                               (erase (foo6 x) 
;;                                      (erase (foo5 x) 
;;                                             Y)))))))
;;
;; When the restrained strategy is used, the goal is dispatched automatically
;; with no splitting.  With the aggressive strategy, four subgoals are created,
;; and ACL2 considers whether or not it can prove (foo3 x) = (foo2 x) and also
;; whether or not (foo6 x) = (foo5 x).  These are bad case splits because they
;; will not help us.  They are generated becuase (foo3 x) and (foo2 x) are out
;; of order in the right hand side, and (foo6 x) and (foo5 x) are also out of
;; order.
;;
;; It seems that there might be cases wherein aggressive splitting might
;; stumble upon just the right cases to consider.  However, I find the entire
;; idea distasteful because there is no conceptual tie between out of order
;; terms and whether or not explicit cases ought to be considered.  And, I have
;; not yet been able to invent a theorem that the aggressive strategy could
;; solve, but the restrained strategy could not.  So, I have not even included
;; the aggressive strategy at all.
;;
;;
;; LOOP STOPPING FOR SET/ERASE SIMPLIFICATION
;;
;; We rewrite nests of Sets and Erases to normalize them such that they are
;; interleaved with one another in the term order of their keys.  For example,
;; we would rewrite the following nest as follows:
;;
;;   (set k4 v (erase k3 (set k1 v (erase k5 (set k2 v X)))))
;;       ======>
;;   (set k1 v (set k2 v (erase k3 (set k4 v (erase k5 X)))))
;;
;; In order to achieve this, our reordering rules will have loop stoppers in
;; place so that swaps will only be made if the terms are out of order.
;; 
;; When we write rules such as 
;;
;;     (equiv (erase key1 (erase key2 map))
;;            (erase key2 (erase key1 map))))
;;
;; The loop stopper we will use is always going to be (key1 key2 set).  The use
;; of key1 and key2 should be fairly obvious -- we only want to reorder the
;; terms if key2 is "smaller" than key1.  But, what does "set" mean?
;;
;; If you take a look at :doc loop-stopper, you can read about the "invisible
;; functions table."  The basic idea is that, when deciding whether or not key1
;; or key2 is smaller, we might want to ignore some functions that occur within
;; key1 or key2, and not count them.
;;
;; In order to keep track of what functions should be ignored in this way,
;; (table invisible-fns-table) is used.  This table is basically an alist that
;; maps function symbols to lists of functions that should be considered
;; invisible under them.  "set" in our loop stoppers, then, is just how we say
;; that the functions listed under "set" in the invisible functions table
;; should be ignored when counting key1 and key2.
;;
;; I have no idea what functions we actually want to ignore, and furthermore, I
;; don't add any functions to the table.  In other words, the "set" key will be
;; empty if you just include this book, indicating that no functions should be
;; ignored.
;;
;; But, if in the future we ever want to consider a function to be invisible
;; for use in these reorderings, we will surely want it to be considered
;; invisible both for "erase" and for "set".  So, using "set" here is just a
;; way of ensuring that no matter what happens, we will always use the "set"
;; key in the table for invisible functions, even for erase, because set and
;; erase are intricately tied and must use the same order to avoid loops.

(defthm erase-when-not-in
  (implies (not (in key map))
           (equiv (erase key map)
                  map))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm erase-of-erase
  (equiv (erase key1 (erase key2 map))
         (erase key2 (erase key1 map)))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

;; We add the following rule to cancel out adjacent erases.  This maybe isn't
;; strictly necessary, because ACL2 can easily figure this out using rewriting,
;; but we add the rule anyway because it is potentially faster to have a simple
;; rule like this than to have to do all of the otherwise-necessary
;; backchaining.

(defthm erase-of-erase-same
  (equiv (erase key (erase key map))
         (erase key map)))

;; Simplifying Set-of-Set Nests
;;
;; I had hoped that we could use the same strategy to simplify set nests as we
;; could for erase nests, particular since we spent so long thinking about the
;; right way to simplify erase of erase.  But, "set"s can't just be arbitrarily
;; reordered like "erase"s, unless they are to different locations.
;;
;; I thought for awhile that maybe the best thing to do for set-of-set would 
;; then be to just do the case split.  But, I found that this doesn't work.  In
;; particular, we need a loop stopper in order to prevent ourselves from going
;; into infinite loops on the not-equal case.  But then the rule won't fire on
;; the equal case either!
;;
;; So, here is what I am going to do.  I will just write two rules: a simple
;; (hypothesis free) rewrite to handle the "same" case, and a conditional 
;; rewrite rule to handle the "different" case.  But, I'll add a "case-split" 
;; to the set-of-set case, so that even if the hypothesis fails, we'll break
;; into cases.  This way, we have an the aggressive splitting strategy that
;; nonetheless still applies to "same" addresses.

(defthm set-of-set-different
  (implies (case-split (not (equal key1 key2)))
           (equiv (set key1 val1 (set key2 val2 map))
                  (set key2 val2 (set key1 val1 map))))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm set-of-set-same
  (equiv (set key val1 (set key val2 map))
         (set key val1 map))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm set-of-erase-different
  (implies (case-split (not (equal key1 key2)))
           (equiv (set key1 val (erase key2 map))
                  (erase key2 (set key1 val map))))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm set-of-erase-same 
  (equiv (set key val (erase key map))
         (set key val map))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm erase-of-set-different
  (implies (case-split (not (equal key1 key2)))
           (equiv (erase key1 (set key2 val map))
                  (set key2 val (erase key1 map))))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm erase-of-set-same
  (equiv (erase key (set key val map))
         (erase key map))
  :hints(("Goal" :in-theory (enable equiv))))

;; We finally install untranslate patterns to make maintain our abstractions
;; of in, tail, and empty during proofs.

(ACL2::add-untranslate-pattern (set::in ?key (domain ?map)) 
                               (in ?key ?map))

(ACL2::add-untranslate-pattern (set::empty (domain ?map)) 
                               (empty ?map))

(ACL2::add-untranslate-pattern (erase (head ?map) ?map) 
                               (tail ?map))

(ACL2::optimize-untranslate-patterns)

;; DAG theorems

(defthm map-erase-set
  (equal (map::erase key (map::set key v r))
         (map::erase key r))
  :hints (("goal" :in-theory (enable map::fix map::set map::erase))))

(defthm head-of-set
  (equal (map::head (map::set k v r))
         k)
  :hints (("goal" :in-theory (enable map::fix map::set map::head))))

(defthm tail-of-set
  (equal (map::tail (map::set k v r))
         (erase k (map::fix r)))
  :hints (("goal" :in-theory (enable map::fix map::set map::head map::erase))))
