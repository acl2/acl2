; Ordered Maps (Omaps) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(local (include-book "misc/total-order" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "tools/rulesets" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ omaps
  :parents (acl2::kestrel-utilities set::std/osets acl2::alists)
  :short "A library of omaps (ordered maps),
          i.e. finite maps represented as strictly ordered alists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is related to the library of "
    (xdoc::seetopic "set::std/osets" "osets (ordered sets)")
    ", i.e. finite sets represented as strictly ordered lists.
     Like osets capture (up to isomorphism)
     the mathematical notion of finite sets (over ACL2 objects),
     omaps capture (up to isomorphism)
     the mathematical notion of finite maps (over ACL2 objects).
     In particular, omap equality is @(tsee equal).")
   (xdoc::p
    "Since the "
    (xdoc::seetopic "<<" "total order on ACL2 values")
    " is lexicographic on @(tsee cons) pairs,
     an omap is an oset of @(tsee cons) pairs;
     furthermore, an omap is an alist.
     While then, in principle,
     some oset and alist operations could be used on omaps,
     this library provides versions of those oset and alist operations
     that have stronger guards
     (i.e. requiring omaps instead of just osets or alists)
     and that treat non-omaps as the empty omap.
     That is, the omap operations respect a `non-map convention'
     analogous to the "
    (xdoc::seetopic "set::primitives" "non-set convention")
    " respected by the oset operations;
     some of the latter are, analogously,
     versions of list operations (e.g. @(tsee set::head) for @(tsee car)),
     motivated by the fact that the list operations
     do not respect the non-set convention.")
   (xdoc::p
    "The omap operations
     @(tsee mapp),
     @(tsee mfix),
     @(tsee empty),
     @(tsee head),
     @(tsee tail), and
     @(tsee update)
     are ``primitive'' in the same sense as the "
    (xdoc::seetopic "set::primitives" "oset primitives")
    ": their logical definitions depend on
     the underlying representation as alists,
     and provide replacements of alist operations
     that respect the `non-map convention'.
     The logical definitions of the other omap operations
     are in terms of the primitive operations,
     without reference to the underlying alist representation.")
   (xdoc::p
    "There are different logically equivalent ways to define omap operations.
     The current definitions (as well as their names) are preliminary
     and could be improved if needed;
     these definitions favor ease of reasoning over efficiency of execution,
     but, as done in osets, @(tsee mbe) could be used to provide
     provably equivalent efficient definitions for execution.
     As it is often possible to reason about osets abstractly
     (i.e. without regard to their underlying list representation),
     it should be often possible to reason about omaps abstractly
     (i.e. without regard to their underlying alist representation),
     using the theorems provided by this library.
     The current theorems are preliminary
     and could be improved and extended if needed.
     The empty omap is @('nil'), like the empty oset;
     there is no separate operation for the empty omap,
     as there is none for the empty oset.")
   (xdoc::p
    "Since osets are in the @('\"SET\"') package,
     it would be natural to use a @('\"MAP\') package for omaps.
     However, a package with this name is already defined
     in @('[books]/coi/maps/package.lsp') (see below).
     So, we use @('\"OMAP\"') for omaps
     to allow interoperability with this @('coi') map library,
     in the sense that an application can use both @('coi') maps and omaps.
     Perhaps the @('\"SET\"') package for osets
     could be renamed to @('\"OSET\"') at some point,
     for consistency.
     (A similar issue applies to the library of obags, i.e. ordered bags,
     and the @('[books]/coi/bags') library,
     which defines a @('\"BAG\"') package.)")
   (xdoc::p
    "This omap library could become a new @('std/omaps') library,
     part of @(csee std), parallel to @(tsee set::std/osets).")
   (xdoc::p
    "Compared to using the built-in @(see acl2::alists) to represent maps,
     omaps are closer to the mathematical notion of maps,
     at the cost of maintaining their strict order.
     These tradeoffs are analogous to the ones between using osets
     and using the built-in @(see acl2::lists) to represent sets.
     The map library in @('[books]/coi/maps/')
     operates on possibly unordered alists.")
   (xdoc::p
    "Compared to the records in "
    (xdoc::seetopic "acl2::misc/records" "@('[books]/misc/records.lisp')")
    " and @('[books]/coi/records/'),
     omaps allow any value to be associated to keys,
     without having to exclude @('nil') or some other fixed value.
     Furthermore, as noted in the comments in @('[books]/coi/maps/maps.lisp'),
     the `get' operation on those records
     does not always yield a value smaller than the map.
     On the other hand, theorems about omaps have generally more hypotheses
     than the theorems about records."))
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mapp (x)
  :returns (yes/no booleanp)
  :short "Recognize omaps."
  :long
  (xdoc::topstring-p
   "This is similar to the definition of @(tsee set::setp),
    but each element of the list is checked to be a @(tsee cons) pair
    and the ordering comparison is performed on the @(tsee car)s.")
  (if (atom x)
      (null x)
    (and (consp (car x))
         (or (null (cdr x))
             (and (consp (cdr x))
                  (consp (cadr x))
                  (fast-<< (caar x) (caadr x))
                  (mapp (cdr x))))))
  ///

  (defrule setp-when-mapp
    (implies (mapp x)
             (set::setp x))
    :rule-classes (:rewrite :forward-chaining)
    :enable (set::setp << lexorder))

  (defrule alistp-when-mapp
    (implies (mapp x)
             (alistp x))
    :rule-classes (:rewrite :forward-chaining))

  (defruled consp-car-when-non-empty-mapp
    (implies (and map (mapp map))
             (consp (car map))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mfix ((x mapp))
  :returns (fixed-x mapp)
  :short "Fixing function for omaps."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::sfix) for osets.")
  (mbe :logic (if (mapp x) x nil)
       :exec x)
  ///

  (defrule mfix-when-mapp
    (implies (mapp x)
             (equal (mfix x) x)))

  (defrule mfix-implies-mapp
    (implies (mfix x)
             (mapp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ((map mapp))
  :returns (yes/no booleanp)
  :short "Check if an omap is empty."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::empty) for osets.")
  (null (mfix map))
  ///

  (defrule mapp-when-not-empty
    (implies (not (empty map))
             (mapp map))
    :enable mfix)

  (defrule mfix-when-empty
    (implies (empty x)
             (equal (mfix x) nil)))

  (defrule mapp-non-nil-implies-non-empty
    (implies (and (mapp map) map)
             (not (empty map))))
  
  (defrule acl2-count-head-when-non-empty
    (implies (not (empty map))
             (< (+ (acl2-count (car (car map)))
                   (acl2-count (cdr (car map))))
                (acl2-count map)))
    :hints (("Goal" :in-theory (enable mfix))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head ((map mapp))
  :guard (not (empty map))
  :returns (mv key val)
  :short "Smallest key, and associated value, of a non-empty omap."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::head) for osets.")
  (let ((pair (car (mfix map))))
    (mv (car pair) (cdr pair)))
  :guard-hints (("Goal" :in-theory (enable empty mapp)))
  ///

  (defrule head-key-when-empty
    (implies (empty map)
             (equal (mv-nth 0 (head map)) nil))
    :rule-classes (:rewrite :type-prescription)
    :enable (empty mfix mapp))

  (defrule head-value-when-empty
    (implies (empty map)
             (equal (mv-nth 1 (head map)) nil))
    :rule-classes (:rewrite :type-prescription)
    :enable (empty mfix mapp))

  (defrule head-key-count
    (implies (not (empty map))
             (< (acl2-count (mv-nth 0 (head map)))
                (acl2-count map)))
    :rule-classes (:rewrite :linear)
    :enable (empty mfix))

  (defrule head-value-count
    (implies (not (empty map))
             (< (acl2-count (mv-nth 1 (head map)))
                (acl2-count map)))
    :rule-classes (:rewrite :linear)
    :enable (empty mfix))

  (defrule head-key-count-built-in
    (implies (not (empty map))
             (o< (acl2-count (mv-nth 0 (head map)))
                 (acl2-count map)))
    :rule-classes :built-in-clause
    :enable (empty mfix))

  (defrule head-value-count-built-in
    (implies (not (empty map))
             (o< (acl2-count (mv-nth 1 (head map)))
                 (acl2-count map)))
    :rule-classes :built-in-clause
    :enable (empty mfix)))


(define head-key ((map mapp))
  :guard (not (empty map))
  :enabled t
  (mv-let (key val)
      (head map)
    (declare (ignore val))
    key))

(define head-val ((map mapp))
  :guard (not (empty map))
  :enabled t
  (mv-let (key val)
      (head map)
    (declare (ignore key))
    val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tail ((map mapp))
  :guard (not (empty map))
  :returns (map1 mapp :hints (("Goal" :in-theory (enable mfix mapp))))
  :short "Rest of a non-empty omap after removing its smallest pair."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::tail) for osets.")
  (cdr (mfix map))
  :guard-hints (("Goal" :in-theory (enable empty)))
  ///

  (defrule tail-when-empty
    (implies (empty map)
             (equal (tail map) nil))
    :rule-classes (:rewrite :type-prescription)
    :enable (empty mfix mapp))

  (defrule tail-count
    (implies (not (empty map))
             (< (acl2-count (tail map))
                (acl2-count map)))
    :rule-classes (:rewrite :linear)
    :enable (empty mfix))

  (defrule tail-count-built-in
    (implies (not (empty map))
             (o< (acl2-count (tail map))
                 (acl2-count map)))
    :rule-classes :built-in-clause
    :enable (empty mfix)))


(defruled head-tail-order
  (implies (not (empty (tail X)))
           (<< (mv-nth 0 (head X))
               (mv-nth 0 (head (tail X)))))
  :enable (mapp head tail mfix))
(defruled head-tail-order-contrapositive
  (implies (not (<< (mv-nth 0 (head X))
                    (mv-nth 0 (head (tail X)))))
           (empty (tail X)))
  :enable head-tail-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update (key val (map mapp))
  :returns (map1 mapp
                 :hints (("Goal"
                          :in-theory (enable mapp mfix empty head tail))))
  :short "Set a key to a value in an omap."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the key is not already in the map, it is added, with the value.
     If the key is already in the map, the new value overrides the old value.")
   (xdoc::p
    "This is similar to @(tsee set::insert) for osets."))
  (cond ((empty map) (list (cons key val)))
        (t (mv-let (key0 val0)
             (head map)
             (cond ((equal key key0) (cons (cons key val)
                                           (tail map)))
                   ((<< key key0) (cons (cons key val) map))
                   (t (cons (cons key0 val0)
                            (update key val (tail map))))))))
  ///
  (defrule update-of-head-and-tail
    (implies (not (empty map))
             (equal (update (mv-nth 0 (head map))
                            (mv-nth 1 (head map))
                            (tail map))
                    map))
    :rule-classes :elim
    :enable (head tail empty mfix mapp))

  (defrule update-not-empty
    (not (empty (update key val map)))
    :enable empty)

  (defrule update-same
    (equal (update key val1 (update key val2 map))
           (update key val1 map))
    :enable (head tail empty mfix mapp))

  (defrule update-different
    (implies (not (equal key1 key2))
             (equal (update key1 val1 (update key2 val2 map))
                    (update key2 val2 (update key1 val1 map))))
    :enable (head tail empty mfix mapp))

  (defrule update-when-empty
    (implies (and (syntaxp (not (equal map ''nil)))
                  (empty map))
             (equal (update key val map)
                    (update key val nil)))
    :enable update)

  (defrule head-key-of-update-of-nil
    (equal (mv-nth 0 (head (update key val nil)))
           key)
    :enable (update head mapp))

  (defrule head-value-of-update-of-nil
    (equal (mv-nth 1 (head (update key val nil)))
           val)
    :enable (update head mapp))

  (defrule tail-of-update-of-nil
    (equal (tail (update key val nil))
           nil)
    :enable (update tail mfix))

  (defrule head-of-update
    (equal (head (update key val map))
           (cond ((empty map) (mv key val))
                 ((<< (mv-nth 0 (head map)) key) (head map))
                 (t (mv key val))))
    :enable (update head tail))

  (defruled head-key-of-update
    (equal (mv-nth 0 (head (update key val map)))
           (cond ((empty map) key)
                 ((<< (mv-nth 0 (head map)) key) (mv-nth 0 (head map)))
                 (t key)))
    :enable (head-of-update))

  (defruled head-value-of-update
    (equal (mv-nth 1 (head (update key val map)))
           (cond ((empty map) val)
                 ((<< (mv-nth 0 (head map)) key) (mv-nth 1 (head map)))
                 (t val)))
    :enable (head-of-update))

  (defrule tail-of-update
    (equal (tail (update key val map))
           (cond ((empty map) nil)
                 ((<< key (mv-nth 0 (head map))) map)
                 ((equal key (mv-nth 0 (head map))) (tail map))
                 (t (update key val (tail map)))))
    :enable (update tail))
 )

(defrule head-value-of-update-empty
  (implies (empty map)
           (equal (mv-nth 1 (head (update key val map)))
                  val))
  :enable (head-value-of-update))
(defrule head-value-of-update-key-<<
  (implies (and (not (empty map))
                (or (<< key (mv-nth 0 (head map)))
                    (equal key (mv-nth 0 (head map)))))
           (equal (mv-nth 1 (head (update key val map)))
                  val))
  :enable (head-value-of-update))

(defrule head-value-of-update-when-head-key-equal
  (implies (equal (mv-nth 0 (head (update key val x)))
                  key)
           (equal (mv-nth 1 (head (update key val x)))
                           val))
  :hints (("Goal" :in-theory (enable acl2::<<-irreflexive head-of-update))))

(defrule head-value-of-update-not-<<
  (implies (and (not (empty map))
                (<< (mv-nth 0 (head map)) key))
           (equal (mv-nth 1 (head (update key val map)))
                  (mv-nth 1 (head map))))
  :enable (head-value-of-update))

(defrule tail-of-update-empty
  (implies (empty map)
           (equal (tail (update key val map))
                  nil))
  :enable (tail-of-update))
(defrule tail-of-update-<<
  (implies (and (not (empty map))
                (<< key (mv-nth 0 (head map))))
           (equal (tail (update key val map))
                  map))
  :enable (tail-of-update))
(defrule tail-of-update-equal
  (implies (and (not (empty map))
                (equal key (mv-nth 0 (head map))))
           (equal (tail (update key val map))
                  (tail map)))
  :enable (tail-of-update))
(defrule tail-of-update-<<-rev
  (implies (and (not (empty map))
                (<< (mv-nth 0 (head map)) key))
           (equal (tail (update key val map))
                  (update key val (tail map))))
  :enable (tail-of-update))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update* ((new mapp) (old mapp))
  :returns (map mapp)
  :short "Update a map with another map."
  :long
  (xdoc::topstring-p
   "This lifts @(tsee update) from a single key and value
    to a set of key-value pairs, passed as the first argument map.
    If a key is in the second but not in the first map,
    the key is present in the result, with the same value as in the second map.
    If a key is in the first but not in the second map,
    the key is present in the result, with the same value as in the first map.
    If a key is present in both maps,
    it is present in the result, with the same value as in the first map;
    i.e. the first map ``wins''.
    There are no other keys in the result.")
  (cond ((empty new) (mfix old))
        (t (mv-let (new-key new-val)
             (head new)
             (update new-key new-val
                     (update* (tail new) old)))))
  :verify-guards nil ; done below
  ///
  (verify-guards update*)

  (defrule update*-when-left-empty
    (implies (empty new)
             (equal (update* new old)
                    (mfix old))))

  (defrule update*-when-right-empty
    (implies (empty old)
             (equal (update* new old)
                    (mfix new)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete (key (map mapp))
  :returns (map1 mapp)
  :short "Remove a key, and associated value, from an omap."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::delete) for osets.")
  (cond ((empty map) nil)
        (t (mv-let (key0 val0)
             (head map)
             (cond ((equal key key0) (tail map))
                   (t (update key0
                              val0
                              (delete key (tail map))))))))
  :verify-guards nil ; done below
  ///
  (verify-guards delete)

  (defrule delete-when-empty
    (implies (empty map)
             (equal (delete key map) nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete* ((keys set::setp) (map mapp))
  :returns (map1 mapp)
  :short "Remove keys, and associated values, from an omap."
  :long
  (xdoc::topstring-p
   "This lifts @(tsee delete) from a single key to a set of keys.")
  (cond ((set::empty keys) (mfix map))
        (t (delete (set::head keys) (delete* (set::tail keys) map))))
  :verify-guards nil ; done below
  ///
  (verify-guards delete*)

  (defrule delete*-when-left-empty
    (implies (set::empty keys)
             (equal (delete* keys map)
                    (mfix map))))

  (defrule delete*-when-right-empty
    (implies (empty map)
             (equal (delete* keys map)
                    nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in (key (map mapp))
  :returns (pair? listp)
  :short "Check if a key is in an omap."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the key is present, return the @(tsee cons) pair with the key.
     Otherwise, return @('nil').")
   (xdoc::p
    "This is similar to @(tsee set::in) for osets."))
  (cond ((empty map) nil)
        (t (mv-let (key0 val0)
             (head map)
             (cond ((equal key key0) (cons key0 val0))
                   (t (in key (tail map)))))))
  ///

  (defrule in-when-empty
    (implies (empty map)
             (equal (in key map) nil))
    :rule-classes (:rewrite :type-prescription))

  (defrule in-of-head
    (iff (in (mv-nth 0 (head map)) map)
         (not (empty map))))

  (defrule in-when-in-tail
    (implies (in key (tail map))
             (in key map)))

  (defrule acl2-count-in-<-map
    (implies (not (empty map))
             (< (acl2-count (in key map))
                (acl2-count map)))
    :enable (mv-nth head empty mfix consp-car-when-non-empty-mapp))

  (defrule in-of-update
    (equal (in key1 (update key val map))
           (if (equal key1 key)
               (cons key val)
             (in key1 map)))
    :enable (update head tail empty mfix mapp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in* ((keys set::setp) (map mapp))
  :returns (yes/no booleanp)
  :short "Check if every key in a non-empty set is in an omap."
  :long
  (xdoc::topstring-p
   "This lifts @(tsee in) to sets of keys.
    However, this returns a boolean,
    while @(tsee in) returns a @(tsee listp).")
  (cond ((set::empty keys) t)
        (t (and (in (set::head keys) map)
                (in* (set::tail keys) map))))
  ///

  (defrule in*-when-left-empty
    (implies (set::empty keys)
             (in* keys map)))

  (defrule in*-when-rigth-empty
    (implies (empty map)
             (equal (in* keys map)
                    (set::empty keys))))

  (defrule in*-of-tail
    (implies (in* keys map)
             (in* (set::tail keys) map))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ruleset order-rules
  '(acl2::<<-irreflexive
    acl2::<<-transitive
    acl2::<<-asymmetric
    acl2::<<-trichotomy
    acl2::<<-implies-lexorder
    (:induction update)
  ;  update-induction-case
  ;  head-update
    head-of-update
    head-key-of-update
    head-value-of-update
    head-tail-order
    head-tail-order-contrapositive))

(defthm weak-update-induction-helper-1
  (implies (and (mapp M)
                (not (in key M))
                (not (equal (mv-nth 0 (head (update key val M))) key)))
           (equal (head (update key val M))
                  (head M)))
  :hints (("Goal" :in-theory (acl2::enable* order-rules))))

(defthm weak-update-induction-helper-2
  (implies (and (not (in key M))
                (not (equal (mv-nth 0 (head (update key val M))) key)))
           (equal (tail (update key val M))
                  (update key val (tail M))))
  :hints (("Goal" :in-theory (acl2::enable* order-rules))))

(defthm weak-update-induction-helper-3
  (implies (and (not (in key M))
                (equal (mv-nth 0 (head (update key val M))) key))
           (equal (tail (update key val M))
                  (mfix M)))
  :hints(("Goal" :in-theory (acl2::enable* order-rules))))

(defun weak-update-induction (key val M)
  (declare (xargs :guard (mapp M)))
  (cond ((empty M) nil)
        ((in key M) nil)
        ((equal (head-key (update key val M)) key) nil)
        (t (list (weak-update-induction key val (tail M))))))

(defthm use-weak-update-induction t
  :rule-classes ((:induction
                  :pattern (update key val M)
                  :scheme (weak-update-induction key val M))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup (key (map mapp))
  :guard (in key map)
  :returns (val)
  :short "Value associated to a key in an omap."
  (cdr (in key map))
  ///

  (defrule lookup-when-empty
    (implies (empty map)
             (not (lookup key map)))
    :rule-classes (:rewrite :type-prescription))

  (defrule acl2-count-lookup-<-map
    (implies (not (empty map))
             (< (acl2-count (lookup key map))
                (acl2-count map)))
    :hints (("Goal" :in-theory (disable acl2-count-in-<-map)
             :use acl2-count-in-<-map)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup* ((keys set::setp) (map mapp))
  :guard (in* keys map)
  :returns (vals set::setp)
  :short "Set of values associated to a set of keys in an omap."
  :long
  (xdoc::topstring-p
   "This lifts @(tsee lookup) to sets of keys.")
  (cond ((set::empty keys) nil)
        ((mbt (if (in (set::head keys) map) t nil))
         (set::insert (lookup (set::head keys) map)
                      (lookup* (set::tail keys) map)))
        (t (lookup* (set::tail keys) map)))
  :verify-guards nil ; done below
  ///
  (verify-guards lookup* :hints (("Goal" :in-theory (enable in*))))

  (defrule lookup*-when-left-empty
    (implies (set::empty keys)
             (equal (lookup* keys map)
                    nil))
    :rule-classes (:rewrite :type-prescription))

  (defrule lookup*-when-right-empty
    (implies (empty map)
             (equal (lookup* keys map)
                    nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlookup (val (map mapp))
  :returns (keys set::setp)
  :short "Set of keys to which a value is associated."
  :long
  (xdoc::topstring
   (xdoc::p
    "The resulting set is empty if the value is not in the omap.
     The resulting set is a singleton
     if the value is associated to exactly one key.
     Otherwise, the resulting set contains two or more keys.")
   (xdoc::p
    "This is the ``reverse'' of @(tsee lookup),
     which motivates the @('r') in the name."))
  (cond ((empty map) nil)
        (t (mv-let (key0 val0)
             (head map)
             (if (equal val val0)
                 (set::insert key0 (rlookup val (tail map)))
               (rlookup val (tail map))))))
  :verify-guards nil ; done below
  ///
  (verify-guards rlookup)

  (defrule rlookup-when-empty
    (implies (empty map)
             (equal (rlookup val map) nil))
    :rule-classes (:rewrite :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlookup* ((vals set::setp) (map mapp))
  :returns (keys set::setp)
  :short "Set of keys to which any value in a set is associated."
  :long
  (xdoc::topstring-p
   "This lifts @(tsee rlookup*) to sets of values.")
  (cond ((set::empty vals) nil)
        (t (set::union (rlookup (set::head vals) map)
                       (rlookup* (set::tail vals) map))))
  :verify-guards nil ; done below
  ///
  (verify-guards rlookup*)

  (defrule rlookup*-when-left-empty
    (implies (set::empty vals)
             (equal (rlookup* vals map) nil))
    :rule-classes (:rewrite :type-prescription))

  (defrule rlookup*-when-right-empty
    (implies (empty map)
             (equal (rlookup* vals map) nil))
    :rule-classes (:rewrite :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict ((keys set::setp) (map mapp))
  :returns (map1 mapp)
  :short "Restrict an omap to a set of keys."
  :long
  (xdoc::topstring-p
   "This drops all the keys of the omap
    that are not in the given set of keys.")
  (cond ((empty map) nil)
        (t (mv-let (key val)
             (head map)
             (if (set::in key keys)
                 (update key val (restrict keys (tail map)))
               (restrict keys (tail map))))))
  :verify-guards nil ; done below
  ///
  (verify-guards restrict)

  (defrule restrict-when-left-empty
    (implies (set::empty keys)
             (equal (restrict keys map) nil))
    :rule-classes (:rewrite :type-prescription))

  (defrule restrict-when-right-empty
    (implies (empty map)
             (equal (restrict keys map) nil))
    :rule-classes (:rewrite :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keys ((map mapp))
  :returns (keys set::setp
                 :hints (("Goal" :in-theory (enable mfix mapp set::setp))))
  :short "Oset of the keys of an omap."
  (cond ((empty map) nil)
        (t (mv-let (key val)
             (head map)
             (declare (ignore val))
             (set::insert key (keys (tail map))))))
  ///

  (defrule keys-when-empty
    (implies (empty map)
             (equal (keys map) nil))
    :rule-classes (:rewrite :type-prescription)
    :enable empty))

(defthm keys-of-update
  (equal (keys (update key val m))
         (set::insert key (keys m)))
  ;; This ugly list suggests a need for useful lemmas!
  :hints (("Goal" :in-theory (enable keys update empty insert head tail mfix mapp set::insert
                                     set::head set::tail set::empty setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define values ((map mapp))
  :returns (vals set::setp)
  :short "Oset of the values of an omap."
  (cond ((empty map) nil)
        (t (mv-let (key val)
             (head map)
             (declare (ignore key))
             (set::insert val (values (tail map))))))
  :verify-guards nil ; done below
  ///
  (verify-guards values)

  (defrule values-when-empty
    (implies (empty map)
             (equal (values map) nil))
    :rule-classes (:rewrite :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compatiblep ((map1 mapp) (map2 mapp))
  :returns (yes/no booleanp)
  :short "Check if two omaps are compatible, in the sense that
          they map their common keys to the same values."
  :long
  (xdoc::topstring-p
   "This definition is not optimal for execution.
    The compatibility of two omaps can be checked
    by linearly scanning through them in order.
    A future version of this operation should have that definition,
    at least for execution.")
  (cond ((empty map1) t)
        ((mv-let (key1 val1)
           (head map1)
           (let ((pair2 (in key1 map2)))
             (and pair2
                  (not (equal val1 (cdr pair2))))))
         nil)
        (t (compatiblep (tail map1) map2)))
  ///

  (defrule compatiblep-when-left-empty
    (implies (empty map1)
             (compatiblep map1 map2)))

  (defrule compatiblep-when-right-empty
    (implies (empty map2)
             (compatiblep map1 map2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define submap ((sub mapp) (sup mapp))
  :returns (yes/no booleanp)
  :short "Check if an omap is a submap of another omap."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is true when every key in the first omap is also in the second omap,
     and the two omaps agree on the common keys.")
   (xdoc::p
    "This is similar to @(tsee set::subset) for osets."))
  (cond ((empty sub) t)
        (t (mv-let (key val)
             (head sub)
             (and (equal (in key sup)
                         (cons key val))
                  (submap (tail sub) sup)))))
  ///

  (defrule submap-when-left-empty
    (implies (empty sub)
             (submap sub sup)))

  (defrule submap-when-right-empty
    (implies (empty sup)
             (equal (submap sub sup)
                    (empty sub)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define size ((map mapp))
  :returns (size natp)
  :short "Size of an omap."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the number of keys in the omap.")
   (xdoc::p
    "The @('unfold-...-size-const') are useful to turn
     assertions about sizes and constants
     into assertions about @(tsee empty) and @(tsee tail);
     the expansion terminates because of the @(tsee syntaxp) restriction.
     These theorems are disabled by default.
     These are the omap analogous of "
    (xdoc::seetopic "acl2::list-len-const-theorems" "these theorems")
    " for lists."))
  (cond ((empty map) 0)
        (t (1+ (size (tail map)))))
  ///

  (defruled unfold-equal-size-const
    (implies (syntaxp (quotep c))
             (equal (equal (size map) c)
                    (if (natp c)
                        (if (equal c 0)
                            (empty map)
                          (and (not (empty map))
                               (equal (size (tail map))
                                      (1- c))))
                      nil))))

  (defruled unfold-gteq-size-const
    (implies (syntaxp (quotep c))
             (equal (>= (size map) c)
                    (or (<= (fix c) 0)
                        (and (not (empty map))
                             (>= (size (tail map))
                                 (1- c)))))))

  (defruled unfold-gt-size-const
    (implies (syntaxp (quotep c))
             (equal (> (size map) c)
                    (or (< (fix c) 0)
                        (and (not (empty map))
                             (> (size (tail map))
                                (1- c))))))
    :use lemma
    :prep-lemmas
    ((defrule lemma
       (implies (and (not (empty map))
                     (or (< (fix c) 0)
                         (> (size (tail map))
                            (1- c))))
                (> (size map) c))
       :rule-classes nil)))
  ;; (defrule size-update
  ;;   (equal (size (update key val m))
  ;;          (if (in key m)
  ;;              (size m)
  ;;            (1+ (size m)))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-lists ((keys true-listp) (vals true-listp))
  :guard (= (len keys) (len vals))
  :returns (map mapp)
  :short "Build an omap from
          a list of keys and a list of corresponding values."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are duplicate keys in the first list,
     the leftmost key, and the corresponding value,
     will be in the resulting omap."))
  (cond ((endp keys) nil)
        (t (update (car keys) (car vals) (from-lists (cdr keys) (cdr vals))))))
