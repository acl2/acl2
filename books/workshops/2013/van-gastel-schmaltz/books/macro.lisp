#|$ACL2s-Preamble$;
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "perm")
(include-book "DefSpeC-reuse")
(defspec for-all-predicate ((predicate (x) t))
  (local (defun predicate (x) x)))
(DEFUN for-all (lst)
  (if (endp lst) t
    (and (predicate (car lst))
         (for-all (cdr lst)))))
(DEFTHM for-all-HOLDS-FOR-MEMBER
  (IMPLIES (AND (for-all LST)
                (MEMBER-EQUAL V LST))
           (predicate V)))#|ACL2s-ToDo-Line|#

(DEFCONG PERMP EQUAL (FOR-ALL LST) 1)
(DEFTHM for-all-HOLDS-FOR-MEMBER
  (IMPLIES (AND (for-all LST)
                (MEMBER-EQUAL V LST))
           (predicate V)))
(DEFTHM for-all-HOLDS-FOR-ASSOC
  (IMPLIES (AND (for-all (strip-cars LST))
                (assoc V LST))
           (predicate V)))
(DEFTHM for-all-REMOVING-MEMBER
  (IMPLIES (predicate V)
           (EQUAL (for-all (DEL V LST))
                  (for-all LST))))
(DEFTHM for-all-append
  (equal (for-all (append lst1 lst2))
         (and (for-all lst1) (for-all lst2))))
(DEFTHM for-all-subset
  (implies (AND (subsetp-equal lst lst2)
                (for-all lst2))
           (equal (for-all lst) t)))
(DEFTHM for-all-subset-append
  (implies (AND (for-all lst1)
                (for-all lst2)
                (subsetp lst (append lst1 lst2)))
           (equal (for-all lst) t)))
(DEFTHM for-all-cdr
  (implies (for-all lst)
           (equal (for-all (cdr lst)) t)))

; e.g. (create-for-all routing-invariant :extra (rs-param) :name A-V-ROUTING-INVARIANT :element-name v :map ((curv v) (frmv v) rs-param))
; generates for-all predicate function proofs (as listed above):
; - congruence over permutation
; - for all holds for superset, implies for subset
; - append rewrite rules
; - instantiation of predicate for members of for-all list
(defmacro create-for-all (predicate &key thmname extra name map element-name domain)
  (let* ((name (if name name (if domain (packn `(A- ,domain - ,predicate)) (packn `(A- ,predicate)))))
         (name (if extra `(lambda (LST) (,name LST . ,extra))
                               name))
         (element-name (if element-name element-name 'element))
         (lambda-predicate (if map `(lambda (,element-name) (,predicate . ,map))
                             (if extra `(lambda (,element-name) (,predicate ,element-name . ,extra))
                               predicate)))
         (thmname (if thmname thmname predicate)))
    `(instance-Of-defspec for-all-predicate ,thmname '((predicate ,lambda-predicate) (for-all ,name)))))

(defspec map-mappable ((mappable (x) t))
  (local (defun mappable (x) x)))

(defun do-map (lst) ; map has already been taken by lisp
  (if (endp lst) nil
    (cons (mappable (car lst))
          (do-map (cdr lst)))))
(defthm map-append
  (equal (do-map (append lst-A lst-B))
         (append (do-map lst-A) (do-map lst-B))))
(defthm member-of-map
  (implies (member-equal elm lst-a)
           (member-equal (mappable elm)
                         (do-map lst-a))))
(defthm member-of-map-equal
  (implies (and (member-equal element-a lst-a)
                (equal (mappable element-a)
                       (mappable element-b)))
           (member-equal (mappable element-b) (do-map lst-a))))
(defthm map-member-of-del
  (implies (and (member-equal x lst-a)
                (member-equal y (do-map (DEL X lst-A))))
           (member-equal y (DEL (mappable x) (do-map lst-A))))
  )
(defcong permp permp (do-map x0) 1)
(defthm map-len
  (equal (len (do-map lst))
         (len lst)))
(defthm map-true-listp
  (true-listp (do-map lst))
  :rule-classes :type-prescription)
(defthm map-subsetp-implies-member-v
  (implies (and (subsetp (do-map lst-a) (do-map lst-b))
                (member-equal x (do-map lst-a)))
           (member-equal x (do-map lst-b))))
(defthm subsetp-implies-subset-of-map
      (implies (subsetp lst-a lst-b)
               (equal (subsetp (do-map lst-a) (do-map lst-b)) t)))

(defmacro create-map (mapfunc &key extra name map element-name domain)
  (let* ((name (if name name (if domain (packn `(map- ,domain - ,mapfunc)) (packn `(map- ,mapfunc)))))
         (name (if extra `(lambda (LST) (,name LST . ,extra))
                               name))
         (element-name (if element-name element-name 'element))
         (lambda-mapfunc (if map `(lambda (,element-name) (,mapfunc . ,map))
                             (if extra `(lambda (,element-name) (,mapfunc ,element-name . ,extra))
                               mapfunc))))
    `(instance-Of-defspec map-mappable ,mapfunc '((mappable ,lambda-mapfunc) (do-map ,name)))))
;(create-map V-id :name V-ids)

(defun to-symbol-name (name)  (if (stringp name) name (symbol-name name)))
(defun A-concatenate (names)  (if (endp names) "" (concatenate 'string "-" (to-symbol-name (car names)) (A-concatenate (cdr names)))))
(defmacro make-name (prefix &rest names) `(intern-in-package-of-symbol (concatenate 'string (symbol-name ,prefix) (A-concatenate (list ,@names))) ,prefix))
(defun create-mapping-for-map (extra n) (if (endp extra) nil (cons `(,(car extra) (nth ,n values)) (create-mapping-for-map (cdr extra) (1+ n))) ))

(defspec mapping-mappable ((mappingable (x) t))
  (local (defun mappingable (x) x)))

(defun mapping (lst)
  (if (endp lst)
    nil
    (binary-append (mappingable (car lst))
                   (mapping (cdr lst)))))
(defthm mapping-append
  (equal (mapping (append lst-A lst-B))
         (append (mapping lst-A) (mapping lst-B))))
(defthm set-is-subset-of-appending-itself
  (implies (consp a)
           (subsetp-equal a (binary-append a b)))
  )
(defthm mapping-member-of-map
      (implies (member-equal v lst-a)
               (subsetp-equal (mappingable v)
                              (mapping lst-a)))
      :HINTS (("Subgoal *1/2''" :use (:instance set-is-subset-of-appending-itself
                                      (a (mappingable (CAR LST-A)))
                                      (b (mapping (CDR LST-A))))))
      )
(defthm mapping-member-of-map-equal
  (implies (and (member-equal element-a lst-a)
                (equal (mappingable element-a)
                       (mappingable element-b)))
           (subsetp-equal (mappingable element-b)
                          (mapping lst-a))))
(defcong permp permp (mapping x0) 1)
(defthm mapping-true-listp (true-listp (mapping lst)) :rule-classes :type-prescription)
(defthm subset-stable-under-append-v2 ; there is a similar theory in sets.lisp which is defined on the second argument instead
  (equal (subsetp (binary-append x y) a)
         (and (subsetp x a) (subsetp y a))))
(defthm mapping-subsetp-implies-subset-of-map
  (implies (subsetp lst-a lst-b)
           (subsetp (mapping lst-a) (mapping lst-b)))
  )

(defthm subset-stable-under-append
  (implies (or (subsetp a x) (subsetp a y))
           (subsetp a (binary-append x y))))
(defthm set-is-subset-of-appending-itself-alt
  (implies (consp a)
           (subsetp-equal a (binary-append b a)))
  :hints (("Goal" :induct (binary-append a b)))
  )

(defmacro create-mapping (mapfunc &key extra name map element-name domain)
  (let* ((name (if name name (if domain (packn `(map- ,domain - ,mapfunc)) (packn `(map- ,mapfunc)))))
         (name (if extra `(lambda (LST) (,name LST . ,extra))
                               name))
         (element-name (if element-name element-name 'element))
         (lambda-mapfunc (if map `(lambda (,element-name) (,mapfunc . ,map))
                             (if extra `(lambda (,element-name) (,mapfunc ,element-name . ,extra))
                               mapfunc))))
    `(instance-Of-defspec mapping-mappable ,mapfunc '((mappingable ,lambda-mapfunc) (mapping ,name)))))

(defspec filtering ((filterable (x) t) (filtermap (x) t))
  (local (defun filterable (x) x))
  (local (defun filtermap (x) x))
  )


(defun filter (lst)
  (if (endp lst)
    nil
    (if (filterable (car lst))
      (cons (filtermap (car lst)) (filter (cdr lst)))
      (filter (cdr lst)))))
(defthm filter-append
  (equal (filter (append lst-a lst-b))
         (append (filter lst-a) (filter lst-b))))
(defthm filter-member-of-filter
  (implies (and (member-equal a lst-a)
                (filterable a))
           (member-equal (filtermap a) (filter lst-a))))
(defthm filter-member-of-del
  (implies (and (member-equal a lst-a)
                (filterable a)
                (member-equal y (filter (del a lst-a))))
           (member-equal y (del (filtermap a) (filter lst-a)))))
(defcong permp permp (filter x0) 1)
(defthm filter-true-listp (true-listp (filter lst)) :rule-classes :type-prescription)
(defthm filter-len (<= (len (filter lst)) (len lst)))
(defthm filter-subsetp-implies-subset-of-map
  (implies (subsetp lst-a lst-b)
           (subsetp (filter lst-a) (filter lst-b))))

(defmacro create-filter (filter &key extra name map element-name domain trans)
  (let* ((name (if name name (if domain (packn `(map- ,domain - ,filter)) (packn `(map- ,filter)))))
         (name (if extra `(lambda (LST) (,name LST . ,extra))
                               name))
         (element-name (if element-name element-name 'element))
         (lambda-filter (if map `(lambda (,element-name) (,filter . ,map))
                             (if extra `(lambda (,element-name) (,filter ,element-name . ,extra))
                               filter)))
         (trans-result (if trans trans `(lambda (x) x)))
         )
    `(instance-Of-defspec filtering ,filter '((filterable ,lambda-filter) (filtermap ,trans-result) (filter ,name)))))
