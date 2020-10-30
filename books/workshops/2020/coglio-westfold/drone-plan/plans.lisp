; Simple plan data type for use by drone planner
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

#| Plans are maps from agents to possible paths |#

(include-book "graph")

(include-book "kestrel/sequences/defmap" :dir :system)

(include-book "coi/adviser/adviser" :dir :system)


(in-theory (enable subsequencep-equal-subsetp-equal no-duplicatesp-equal))

(defthm intersection-equal-of-cons-iff
  (iff (intersection-equal x (cons a y))
       (or (memberp a (double-rewrite x))
           (intersection-equal (double-rewrite x) y)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

;;; Drone ids

(define drone-id-p (x)
  (natp x)
  :returns (b booleanp)
///
(defthm drone-id-p-zero
  (drone-id-p 0))

(defun drone-id-fix (x)
  (declare (xargs :guard t))
  (if (drone-id-p x)
      x
    0))

(defthm drone-id-p-drone-id-fix
  (drone-id-p (drone-id-fix x)))

(defthm drone-id-p-drone-id-fix-id
  (implies (drone-id-p x)
           (equal (drone-id-fix x) x)))

(defun drone-id-equiv (n1 n2)
  (declare (xargs :guard t))
  (equal (drone-id-fix n1) (drone-id-fix n2)))

(defequiv drone-id-equiv)

(fty::deffixtype drone-id :pred drone-id-p :fix drone-id-fix :equiv drone-id-equiv)

(fty::deflist drone-id-list :elt-type drone-id :true-listp t)
) ; drone-id-p


(in-theory (disable drone-id-fix drone-id-equiv))

(defund coord-id-p (x)
  (declare (xargs :guard t))
  (natp x))

;; Auxiliary fn abstracting from hons
(defun get-assoc (k l)
  (declare (xargs :guard t))
  (cdr (hons-assoc-equal k l)))

(define no-duplicate-alist-p (m)
  :returns (b booleanp)
  (no-duplicatesp-equal (alist-keys m))
///
(defthm no-duplicate-alist-cdr
  (implies (no-duplicate-alist-p m)
           (no-duplicate-alist-p (cdr m))))
(defthm no-duplicate-alist-acons
  (implies (and (no-duplicate-alist-p m)
                (not (memberp x (alist-keys (double-rewrite m)))))
           (no-duplicate-alist-p (acons x y m))))
(defthm no-duplicate-alist-cons    ; not sure if this helpful as essentially equiv to prev
  (implies (and (no-duplicate-alist-p m)
                (not (member x (alist-keys (double-rewrite m)))))
           (no-duplicate-alist-p (cons (cons x y) m)))
  :hints (("Goal" :use no-duplicate-alist-acons)))
(defthm no-duplicate-alist-caar-alist-keys-cdr
  (implies (and (no-duplicate-alist-p m)
                (consp m)
                (consp (car m)))
           (not (member (caar m) (alist-keys (cdr m)))))) ; Proof doesn't go through with memberp!
) ; no-duplicate-alist-p

(define disjoint-alists-p (m1 m2)
  :returns (b booleanp)
  (null (intersection-equal (alist-keys m1) (alist-keys m2)))
///
(defthm disjoint-alists-p-acons-caar
  (implies (and (disjoint-alists-p m1 m2)
                (no-duplicate-alist-p m1)
                (no-duplicate-alist-p m2)
                (consp m1)
                (consp (car m1)))
           (no-duplicate-alist-p (acons (caar m1) y m2)))
  :hints (("Goal" :in-theory (enable no-duplicate-alist-p))))
)

(defthm not-assoc-equal-lemma
  (implies (and (disjoint-alists-p lst acc)
                (memberp key (alist-keys (double-rewrite lst)))
                (alistp acc))
           (not (assoc-equal key acc)))
  :hints (("Goal"
           :cases ((memberp key (alist-keys acc)))
           :in-theory (enable disjoint-alists-p))))

(defthm disjoint-alists-p-of-cons-arg2
  (implies (consp (double-rewrite pair))
           (equal (disjoint-alists-p alist1 (cons pair alist2))
                  (and (not (memberp (car (double-rewrite pair)) (alist-keys (double-rewrite alist1))))
                       (disjoint-alists-p alist1 alist2))))
  :hints (("Goal" :in-theory (enable disjoint-alists-p))))

;; path maps
(fty::defalist path-map
  :key-type drone-id
  :val-type node-list-p
  :pred path-map-p0
  :true-listp t)

(define path-map-p (pm)
  :enabled t
  :returns (b booleanp)
  (and (path-map-p0 pm)
       (no-duplicate-alist-p pm)))

(define path-map-pair-p (map-pair)
  :returns (b booleanp)
  (and (consp map-pair)
       (drone-id-p (car map-pair))
       (node-list-p (cdr map-pair))))

(defthm drone-id-list-p-alist-keys-path-map
  (implies (path-map-p pm1)
           (drone-id-list-p (alist-keys pm1)))
  :hints (("Goal" :in-theory (enable alist-keys no-duplicate-alist-p))))

(defthm path-map-p-alist
  (implies (path-map-p x)
           (alistp x)))

(define path-map-non-empty-paths-p0 (pm)
  :returns (b booleanp)
  :enabled t
  (or (null pm)
      (and (consp pm)
           (consp (car pm))
           (drone-id-p (caar pm))
           (node-list-p (cdar pm))
           (consp (cdar pm))            ; Like path-map-p with this addition
           (path-map-non-empty-paths-p0 (cdr pm)))))

(define path-map-non-empty-paths-p (pm)
  :returns (b booleanp)
  :enabled t
  (and (path-map-non-empty-paths-p0 pm)
       (no-duplicate-alist-p pm)))

;;; plan map functions
(define plan-map-pair-p (pr)
  :returns (b booleanp)
  :enabled t
  (and (consp pr)
       (b* (((cons id nd-plans) pr))
         (and (drone-id-p id)
              (all-node-list-p nd-plans)))))

(fty::defalist plan-map
  :key-type drone-id
  :val-type all-node-list
  :pred plan-map-p0
  :true-listp t)

(defthm plan-map-p0-alist
  (implies (plan-map-p0 x)
           (alistp x))
  :rule-classes (:forward-chaining))

(defun plan-map-p (pm)
  (declare (xargs :guard t))
  (and (plan-map-p0 pm)
       (no-duplicate-alist-p pm)))

(defthm plan-map-p-cdr
  (implies (plan-map-p plan-map)
           (plan-map-p (cdr plan-map))))

(defthm plan-map-p-alist
  (implies (plan-map-p x)
           (alistp x))
  :rule-classes (:forward-chaining))

(define non-trivial-plan-map-p ((pm plan-map-p))
  :verify-guards t
  (and (consp pm)
       (or (consp (cdar pm))
           (non-trivial-plan-map-p (cdr pm))))
///
(defthm non-trivial-plan-map-p-cons
  (implies (and (consp (double-rewrite pl))
                (non-trivial-plan-map-p pm) (drone-id-p drn) (node-list-p pl))
           (non-trivial-plan-map-p (acons drn pl pm))))
)

(defthm drone-id-list-p-alist-keys-plan-map-p
  (implies (plan-map-p pm1)
           (drone-id-list-p (alist-keys pm1)))
  :hints (("Goal" :in-theory (enable alist-keys))))

(define plan-for-id-equal-p ((id drone-id-p) (pm1 plan-map-p) (pm2 plan-map-p))
  :returns (b booleanp)
  (equal (get-assoc id pm1) (get-assoc id pm2))
///
(defthm plan-for-id-equal-p-reflexive
  (plan-for-id-equal-p id x x)))

(define plan-for-id-subset-p ((id drone-id-p) (pm1 plan-map-p) (pm2 plan-map-p))
  :returns (b booleanp)
  (subsetp-equal (get-assoc id pm1) (get-assoc id pm2))
///
(defthm plan-for-id-subset-p-reflexive
  (plan-for-id-subset-p id x x)))

(defforall subset-for-map-elts (ids pm1 pm2) (plan-for-id-subset-p ids pm1 pm2) :fixed (pm1 pm2)
  :true-listp t
  :guard (and (drone-id-list-p ids) (plan-map-p pm1) (plan-map-p pm2)))

(defthm subset-for-map-elts-refl
  (implies (drone-id-list-p ids)
           (subset-for-map-elts ids x x))
  :hints (("Goal" :in-theory (enable subset-for-map-elts))))

(define sub-plan-map-p ((pm1 plan-map-p) (pm2 plan-map-p))
  :returns (b booleanp)
  (subset-for-map-elts (alist-keys pm1) pm1 pm2)
///
(defthm sub-plan-map-p-reflexive
  (implies (plan-map-p x)
           (sub-plan-map-p x x)))
)

(encapsulate
 ()

 (encapsulate
  (((sub-plan-map-p-hyps) => *)
   ((sub-plan-map-p-sub) => *)
   ((sub-plan-map-p-super) => *))

  (local (defun sub-plan-map-p-hyps () nil))
  (local (defun sub-plan-map-p-sub () nil))
  (local (defun sub-plan-map-p-super () nil))

  (defthmd sub-plan-map-p-membership-constraint
    (implies (sub-plan-map-p-hyps)
             (plan-for-id-subset-p sub-plan-map-p-key (sub-plan-map-p-sub) (sub-plan-map-p-super))))
  )

 (local (defund sub-plan-map-p-badguy-aux (keys sub super)
          (declare (xargs :guard (and (drone-id-list-p keys)
                                      (plan-map-p sub)
                                      (plan-map-p super))))
          (cond ((endp keys)
                 nil)
                ((plan-for-id-subset-p (car keys)  sub super)
                 (sub-plan-map-p-badguy-aux (cdr keys) sub super))
                (t (car keys)))))
 (local (defthm sub-plan-map-p-badguy-aux-witness
          (implies (and (true-listp keys)
                        (not (subset-for-map-elts keys sub super)))
                   (not (plan-for-id-subset-p (sub-plan-map-p-badguy-aux keys sub super)
                                              sub super)))
          :hints (("Goal" :in-theory (enable sub-plan-map-p-badguy-aux subset-for-map-elts)))))

 (local (defund sub-plan-map-p-badguy (sub super)
          (declare (xargs :guard (and (plan-map-p sub)
                                      (plan-map-p super))))
          (sub-plan-map-p-badguy-aux (alist-keys sub) sub super)))

 (local (defthmd sub-plan-map-p-badguy-witness
          (implies (not (sub-plan-map-p sub super))
                   (not (plan-for-id-subset-p (sub-plan-map-p-badguy sub super) sub super)))
          :hints (("Goal"
                   :in-theory (enable sub-plan-map-p sub-plan-map-p-badguy)))))

 (defthmd sub-plan-map-p-by-membership-driver
   (implies (sub-plan-map-p-hyps)
            (sub-plan-map-p (sub-plan-map-p-sub) (sub-plan-map-p-super)))
   :hints (("Goal" :use ((:instance sub-plan-map-p-badguy-witness
                                    (sub (sub-plan-map-p-sub))
                                    (super (sub-plan-map-p-super)))
                         (:instance sub-plan-map-p-membership-constraint
                                    (sub-plan-map-p-key (sub-plan-map-p-badguy (sub-plan-map-p-sub)
                                                                               (sub-plan-map-p-super))))))))

 (adviser::defadvice sub-plan-map-p-by-membership
     (implies (sub-plan-map-p-hyps)
              (sub-plan-map-p (sub-plan-map-p-sub) (sub-plan-map-p-super)))
   :rule-classes (:pick-a-point :driver sub-plan-map-p-by-membership-driver))
)

(define true-alistp (l)
  :returns (b booleanp)
  (or (null l)
      (and (consp l)
           (consp (car l))
           (true-listp (cdar l))
           (true-alistp (cdr l))))
///
(defthm true-alistp-implies-cons-or-nil
   (implies (true-alistp l)
            (or (consp l)
                (null l)))
   :rule-classes (:forward-chaining))
(defthm true-alistp-cdr
  (implies (and (true-alistp m)
                (consp m))
           (true-alistp (cdr m))))
(defthm true-alistp-car
  (implies (and (true-alistp m)
                (consp m))
           (consp (car m))))
(defthm true-alistp-cdar
  (implies (and (true-alistp m)
                (consp m))
           (true-listp (cdar m))))
) ; true-alistp

(define collect-locs ((m true-alistp ;; path-map-p
                         ))
 ; :returns (locs node-list-p :hyp :guard)
  (if (endp m)
      ()
    (append (if (consp (first m))
                (rest (first m))
              ())
            (collect-locs (rest m)))))

(define max-plan-length ((m true-alistp) (max-len natp))
  :returns (m natp :hyp (natp max-len))
  (if (endp m)
      max-len
    (max-plan-length (rest m)
                     (max max-len (if (consp (first m))
                                      (len (rest (first m)))
                                    0)))))

(define print-plan-stats ((m true-alistp ;path-map-p
                             ))
  (b* ((all-paths (collect-locs m))
       (all-locs (remove-duplicates-equal all-paths))
       (longest-plan (max-plan-length m 0)))
    (cw "Plan stats: ~x0 locs, ~x1 steps, ~x2 redundant, ~x3 longest path.~%"
        (len all-locs)
        (len all-paths)
        (- (len all-paths) (len all-locs))
        longest-plan)))

;;; Functions for coordinating plan maps to avoid redundancy

(defthm nodep-car-last-node-list
  (implies (and (consp l) (node-list-p l))
           (nodep (car (last l))))
  :rule-classes :type-prescription)

(define destination-of-path ((pl node-list-p))
  :returns (nd nodep)
  (let ((pl (node-list-fix pl)))
    (if (endp pl)
        0
      (car (last pl)))))

(define destinations-of-paths ((pm all-node-list-p))
  :returns (rnodes node-list-p)
  (if (endp pm)
      ()
    (cons (destination-of-path (car (all-node-list-fix pm)))
          (destinations-of-paths (rest pm)))))


(defmap filter-unproductive-plans (plan-map visited-nodes)
  (cons (car plan-map)                  ; plan-map is actually plan-map-pair here!
        (or (paths-not-ending-in-set (cdr plan-map) visited-nodes)
            (cdr plan-map)))
  :fixed (visited-nodes)
  :declares ((xargs :guard (and (plan-map-p plan-map)
                                (node-list-p visited-nodes)))))

(defthm filter-unproductive-plans-preserves-alist-keys
  (implies (and (plan-map-p pm)
                ;;(node-list-p visited-nodes)
                )
           (equal (alist-keys (filter-unproductive-plans pm visited-nodes))
                  (alist-keys (double-rewrite pm))))
  :hints (("Goal" :in-theory (enable filter-unproductive-plans))))

(defthm non-trivial-plan-map-p-filter-unproductive-plans
  (implies (and (plan-map-p plan-map)
                (non-trivial-plan-map-p plan-map))
           (non-trivial-plan-map-p (filter-unproductive-plans plan-map ())))
  :hints (("Goal" :in-theory (enable non-trivial-plan-map-p filter-unproductive-plans))))

(defthm filter-unproductive-plans-plan-for-id-subset-p
  (implies (and (plan-map-p pm) (node-list-p visited-nodes))
           (plan-for-id-subset-p key (filter-unproductive-plans pm visited-nodes)
                                 pm))
  :hints (("Goal" :in-theory (enable plan-for-id-subset-p filter-unproductive-plans))))



(defthm filter-unproductive-plans-sub-plan-map-p
  (implies (and (plan-map-p pm) (node-list-p visited-nodes))
           (sub-plan-map-p (filter-unproductive-plans pm visited-nodes)
                           pm)))


(define filter-redundant-destination-plans-1-aux ((pm plan-map-p) (seen-dest-nodes node-list-p))
  :measure (len (plan-map-fix pm))
  :returns (r-pm plan-map-p0 :hyp (node-list-p seen-dest-nodes))
  :verify-guards nil ;done below
  (let ((pm (plan-map-fix pm)))
    (if (endp pm)
        ()
      (b* (((cons (cons drn plans) r-pm) pm)
           (new-plans (or (paths-not-ending-in-set plans seen-dest-nodes)
                          plans))
           (new-dest-node (destination-of-path (first new-plans))))
        (acons drn new-plans
               (filter-redundant-destination-plans-1-aux r-pm (cons new-dest-node
                                                                    seen-dest-nodes)))))))

(defthm alistp-of-filter-redundant-destination-plans-1-aux
  (alistp (filter-redundant-destination-plans-1-aux pm seen-dest-nodes))
  :hints (("Goal" :in-theory (enable filter-redundant-destination-plans-1-aux))))

(verify-guards filter-redundant-destination-plans-1-aux :hints (("Goal" :expand ((plan-map-p0 pm)))))

(defthm filter-redundant-destination-plans-1-aux-preserves-alist-keys
  (implies (and (plan-map-p pm)
                ;;(node-list-p seen-dest-nodes)
                )
           (equal (alist-keys (filter-redundant-destination-plans-1-aux pm seen-dest-nodes))
                  (alist-keys (double-rewrite pm))))
  :hints (("Goal" :in-theory (enable filter-redundant-destination-plans-1-aux))))

(defthm non-trivial-plan-map-p-filter-redundant-destination-plans-1-aux
  (implies (and (plan-map-p plan-map)
                (non-trivial-plan-map-p plan-map))
           (non-trivial-plan-map-p (filter-redundant-destination-plans-1-aux plan-map seen-dest-nodes)))
  :hints (("Goal" :in-theory (enable non-trivial-plan-map-p filter-redundant-destination-plans-1-aux))))

(defthm filter-redundant-destination-plans-1-aux-plan-for-id-subset-p
  (implies (and (plan-map-p pm) (node-list-p seen-dest-nodes))
           (plan-for-id-subset-p key (filter-redundant-destination-plans-1-aux pm seen-dest-nodes)
                                 pm))
  :hints (("Goal" :in-theory (enable plan-for-id-subset-p filter-redundant-destination-plans-1-aux))))

(defthm filter-redundant-destination-plans-1-aux-sub-plan-map-p
  (implies (and (plan-map-p pm) (node-list-p seen-dest-nodes))
           (sub-plan-map-p (filter-redundant-destination-plans-1-aux pm seen-dest-nodes)
                           pm)))


(define filter-redundant-destination-plans-1 ((pm plan-map-p))
  :returns (ret-pm plan-map-p0 :hyp :guard)
  (filter-redundant-destination-plans-1-aux pm ())
///
(defthm non-trivial-plan-map-p-filter-redundant-destination-plans-1
  (implies (and (plan-map-p plan-map)
                (non-trivial-plan-map-p plan-map))
           (non-trivial-plan-map-p (filter-redundant-destination-plans-1 plan-map))))

(defthm filter-redundant-destination-plans-1-sub-plan-map-p
  (implies (plan-map-p plan-map)
           (sub-plan-map-p (filter-redundant-destination-plans-1 plan-map)
                           plan-map))
  :hints (("Goal" :in-theory (enable filter-redundant-destination-plans-1-aux)))))
