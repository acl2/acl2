
(in-package "FTY")
(include-book "visitor")
(include-book "basetypes")
(include-book "centaur/misc/arith-equivs" :dir :system)


(logic)
(set-bogus-mutual-recursion-ok t)

(deftagsum simple-tree
  ;; Some simple kind of structure
  (:leaf ((name  stringp)
          (value natp)
          (cost  integerp)))
  (:branch ((left   simple-tree)
            (right  simple-tree)
            (hint   booleanp)
            (family stringp)
            (size   natp))))

; Example 1: Let's visit every LEAF and collect up the names.

;; First try: this is very simple but collects all the strings, even
;; the "family" strings, instead of just the leaf names. 
(defvisitor-template collect-strings ((x :object))
  :returns (names (:join (append names1 names)
                   :tmp-var names1
                   :initial nil)
                  string-listp)
  :type-fns ((string list))
  :fnname-template collect-strings-in-<type>)

(defvisitor collect-strings-in-simple-tree :type simple-tree :template collect-strings)


;; Second try: this targets exactly the LEAF structure and says what to do
;; there, but we don't have to write any code for the BRANCH structures.
(defvisitor-template collect-names ((x :object))
  :returns (names (:join (append names1 names)
                   :tmp-var names1
                   :initial nil)
                  string-listp)
  :prod-fns ((simple-tree-leaf (name list)))
  ;; :field-fns ((name list))
  :fnname-template collect-names<<type>> ;; C++ style
  )

(defvisitor collect-names<simple-tree> :type simple-tree :template collect-names)

(defvisitor-template collect-names-acc ((x :object)
                                        (names string-listp))
  :returns (names-out (:acc names)
                      string-listp :hyp (string-listp names))
  :prod-fns ((simple-tree-leaf (name cons)))
  :fnname-template collect-names-<type>-acc
  ;; :field-fns ((name list))
  )

(defvisitor :type simple-tree :template collect-names-acc)

; Example 2: Let's visit every LEAF and increment every value.

(defvisitor-template incr-val ((x :object))
  :returns (new-x :update)
  :prod-fns ((simple-tree-leaf (value 1+))))

(defvisitor incr-val-of-simple-tree :type simple-tree :template incr-val)


(defprod three-trees
  ((a simple-tree)
   (b simple-tree)
   (c simple-tree)))

(defvisitor :type three-trees :template collect-names-acc)






(local
 (progn
   (include-book "basetypes")
   (include-book "centaur/misc/arith-equivs" :dir :system)

   (define double-sum-nat ((x natp)
                           (incr natp)
                           (acc natp))
     :returns (mv (sum natp :rule-classes :type-prescription)
                  (new-x natp :rule-classes :type-prescription)
                  (new-acc natp :rule-classes :type-prescription))
     (b* ((x (acl2::lnfix x))
          (incr (acl2::lnfix incr))
          (acc (acl2::lnfix acc)))
       (mv x
           (+ (* 2 x) incr)
           (+ (* 2 x) acc))))


   (defvisitor-template double-sum-nats ((x :object)
                                         (incr natp)
                                         (acc natp))
     :returns (mv (sum (:join (+ sum sum1)
                        :tmp-var sum1
                        :initial 0)
                       natp :rule-classes :type-prescription)
                  (new-x :update)
                  (new-acc (:acc acc :fix (acl2::lnfix acc))
                           natp :rule-classes :type-prescription))
     :type-fns ((natp double-sum-nat)
                ;; (integerp double-sum-int)
                ))


   (defprod my-prod
     ((str stringp)
      (nat natp)
      (nat2 natp)))

   (defvisitor :type my-prod :template double-sum-nats)
   

   (local (in-theory (disable nfix natp)))

   (deftagsum nat-tree
     (:leaf ((first natp)
             (second natp)))
     (:branch ((left nat-tree)
               (right nat-tree)
               (content natp))))

   (defvisitor :type nat-tree :template double-sum-nats)

   (include-book "std/misc/two-nats-measure" :dir :system)

   (deftypes bunch-of-stuff
     (deftagsum foosum
       (:prod1  ((a my-prod-p)
                 (b natp)
                 (c nat-tree)))
       (:prod2 ((lst foosumlist)
                (lst2 unusedlist)))
       (:empty ())
       (:prod3 ((alst1 foosum-alist)
                (alst2 foosum-alist2)
                (alst3 foosum-alist3)
                (alst4 unused-alist)))
       :measure (two-nats-measure (acl2-count x) 0))
     (deftagsum unused-sum
       (:proda ((sum1 foosum-p)))
       (:prodb ((sum2 foosum-p)))
       :base-case-override :proda
       :measure (two-nats-measure (acl2-count x) 1))
     (deflist foosumlist :elt-type foosum :measure (two-nats-measure (acl2-count x) 1))
     (deflist unusedlist :elt-type unused-sum :measure (two-nats-measure (acl2-count x) 1))
     (defalist foosum-alist :key-type my-prod :val-type foosumlist :measure (two-nats-measure (acl2-count x) 1))
     (defalist foosum-alist2 :key-type foosum-p :val-type stringp :measure (two-nats-measure (acl2-count x) 1))
     (defalist foosum-alist3 :key-type integerp :val-type foosum-p :measure (two-nats-measure (acl2-count x) 1))
     (defalist unused-alist  :key-type stringp :val-type unused-sum :measure (two-nats-measure (acl2-count x) 1)))

   (defvisitor double-sum-nates-of-bunch-of-stuff
     :type  bunch-of-stuff :template double-sum-nats
     :type-fns ((unused-sum   :skip)
                (unused-alist :skip)
                (unusedlist   double-sum-nats-unusedlist))
     (define double-sum-nats-unusedlist ((x unusedlist-p)
                                         (incr natp)
                                         (acc natp))
       :returns (mv (sum natp :rule-classes :type-prescription)
                    (new-x unusedlist-p)
                    (new-acc natp :rule-classes :type-prescription))
       :measure (unusedlist-count x)
       (declare (ignorable x incr acc))
       (mv 555
           (list (make-unused-sum-proda :sum1 (make-foosum-empty)))
           333)))

   ;; (defvisitor bunch-of-stuff double-sum-nats)
   ))
