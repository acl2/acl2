;UTILITY forms for the Alloy Comparision.
 
(in-package "ACL2")
(include-book "std/osets/top" :dir :system)


;get macro
(defmacro g (k r)
  `(mget ,k ,r))

;set macro
(defmacro s (k v r)
  `(mset ,k ,v ,r))

(defun up-macro (pairs ans)
  (if (endp pairs)
      ans
    (up-macro (cddr pairs) `(s ,(car pairs)
                               ,(cadr pairs)
                               ,ans))))
(defmacro up (st &rest pairs)
  "do the update in the sequence of pairs"
  (up-macro pairs st))
(defmacro s- (A B)
  `(set::difference ,A ,B))
(defmacro s+ (A B)
  `(set::union ,A ,B))


(defthm non-nil-=>-not-empty
  (implies (and (set::setp v)
                (not (equal v nil)))
           (not (set::empty v)))
  :hints (("Goal" :in-theory (enable set::empty)))
  :rule-classes :forward-chaining)

(include-book "defexec/other-apps/records/records" :dir :system)

(defthm simple-record-lemma
  (implies (equal (mget a r) v)
           (equal (mset a v r) r)))

(defthm simpler-record-lemma
  (implies (not (mget a r))
           (equal (mset a nil r) r)))

(defun dom (R)
  ;R is a binary relation, gives its domain
  (strip-cars R))

;Let R be a binary relation A -> B where B has some overlap with A,
;let a in A, find all x in A, where a -^^-> x. Here i
;keeps track of members of domain of map not yet reached/seen from 
;a via R. At the worst a can reach every member of dom(R), therefore
;we set i initially as = cardinality of dom(R)
;seen is the members of dom(R) reach function has seen (first arg)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(set-well-founded-relation l<)

(defuns
  (reach (a R i seen)
    (declare (xargs :measure (list (nfix i) (acl2-count a))))
    (if (zp i)
      (mv i seen)
      (let* ((bs (g a R))
             (bs (if (atom bs) (list bs) bs))
             (bs-not-seen (set::difference bs seen)))
        (if (consp bs-not-seen)
          (reach-lst bs-not-seen R (- i (len bs-not-seen)) 
                     (set::union bs-not-seen seen))
          (mv i seen)))))
  (reach-lst (as R i seen)
    (declare (xargs :measure (list (nfix i) (acl2-count as))))
    (if (endp as)
      (mv i seen)
      (mv-let (i1 seen1)
              (reach (car as) R i seen)
              (if (> (nfix i1) (nfix i)) ;not possible
                  (reach-lst (cdr as) R i seen1) 
                (reach-lst (cdr as) R i1 seen1)))))) 


(defun reachable (a R)
  (mv-let (i reached)
          (reach a R (len (dom R)) nil)
          (declare (ignore i))
          reached))

(defun delete-entries (map keys)
  (if (endp keys)
    map
    (if (g (car keys) map)
      (delete-entries (s (car keys) nil map) (cdr keys))
      (delete-entries map (cdr keys)))))

;jared's oset implementation
(defun set::non-empty-setp (x)
  (declare (xargs :guard t))
  (and (set::setp x)
       (not (set::empty x))))
(include-book "acl2s/defdata/top" :dir :system)
(defdata::register-data-constructor (SET::non-empty-setp SET::insert)
  ((acl2s::allp SET::head) (set::setp SET::tail))
  :proper nil
  :rule-classes nil)

