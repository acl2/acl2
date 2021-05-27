; Support functions and theorems for dp-impl.
; Includes definition of drone state (dr-state) and coordinator state (coord-state) data types
; and higher-level functions that use them.
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "plans")

(include-book "kestrel/sequences/defexists" :dir :system)

(include-book "kestrel/lists-light/member-equal" :dir :system)

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(in-theory (disable true-listp))

(defforall loc-map-p0 (l)
  (and (consp l)
       (drone-id-p (car l))
       (nodep (cdr l)))
  :guard t
  :true-listp t)

(define loc-map-p (l)
  :enabled t
  (and (loc-map-p0 l)
       (no-duplicate-alist-p l)))

(defun loc-map-fix (m)
  (declare (xargs :guard t))
  (if (loc-map-p m)
      m
    ()))

(defun loc-map-equiv (m1 m2)
  (declare (xargs :guard t))
  (equal (loc-map-fix m1) (loc-map-fix m2)))

(defequiv loc-map-equiv)

(fty::deffixtype loc-map :pred loc-map-p :fix loc-map-fix :equiv loc-map-equiv)

(defthmd loc-map-p-alistp
  (implies (loc-map-p m)
           (alistp m))
  :rule-classes :forward-chaining)

(defmap loc-map-from-path-map (pm)
  (cons (car pm)
        (car (last pm)))
  :declares ((xargs :guard (path-map-non-empty-paths-p pm))))

;;; Drone state

(fty::defprod dr-state
  ((drone-id drone-id)
   (dgraph dgraph-p)
   (visited-nodes node-list)
   (path-taken node-list)))

(define dr-state*-p (x)
  :returns (b booleanp)
  :enabled t
  (or (null x)
      (dr-state-p x)))

(defforall all-dr-state-p (drn-sts) (dr-state-p drn-sts)
  :guard t :true-listp t)

(defconst *null-state*
  (dr-state 0 (dgraph '(0) (list (connection 0 0 0))) () '(0)))

(define good-dr-state-p (drn-st)
  :returns (b booleanp)
  (and (dr-state-p drn-st)
       (wf-dgraph-p (dr-state->dgraph drn-st))
       (consp (dr-state->path-taken drn-st))
       (node-path-p (dr-state->path-taken drn-st)
                    (dr-state->dgraph drn-st))
       (subsetp-equal (dr-state->visited-nodes drn-st)
                      (dgraph->nodes (dr-state->dgraph drn-st))))
///
(defthm good-dr-state-p-dr-state-p
  (implies (good-dr-state-p drn-st)
           (dr-state-p drn-st)))
(defthm good-dr-state-p-wf-dgraph-p
  (implies (good-dr-state-p drn-st)
           (wf-dgraph-p (dr-state->dgraph drn-st))))
(defthm good-dr-state-p-consp->path-taken
  (implies (good-dr-state-p drn-st)
           (consp (dr-state->path-taken drn-st))))
(defthm good-dr-state-p-node-path-p
  (implies (good-dr-state-p drn-st)
           (node-path-p (dr-state->path-taken drn-st)
                        (dr-state->dgraph drn-st))))
(defthm good-dr-state-p-visited-nodes-in-dgraph
  (implies (good-dr-state-p drn-st)
           (subsetp-equal (dr-state->visited-nodes drn-st)
                          (dgraph->nodes (dr-state->dgraph drn-st)))))
(defthm good-dr-state-p-dr-state
  (implies (and (drone-id-p drn-id)
                (wf-dgraph-p g)
                (node-path-p path-taken g)
                (consp (double-rewrite path-taken))
                (node-list-p v-nds)
                (subsetp-equal (double-rewrite v-nds) (dgraph->nodes g)))
           (good-dr-state-p (dr-state drn-id g v-nds path-taken))))
) ; good-dr-state-p

(define good-dr-state*-p (x)
  :returns (b booleanp)
  :enabled t
  (or (null x)
      (good-dr-state-p x)))

(defthm good-dr-state*-p-dr-state*-p
  (implies (good-dr-state*-p x)
           (dr-state*-p x)))

(defthm node-path-p-path-taken
  (implies (and (dr-state-p drn-st)
                (consp (dr-state->path-taken drn-st))
                (node-path-p (dr-state->path-taken drn-st)
                             (dr-state->dgraph drn-st)))
           (node-path-p (dr-state->path-taken drn-st)
                        (dr-state->dgraph drn-st))))

(defforall all-good-dr-state-p (drn-sts) (good-dr-state-p drn-sts)
  :guard t :true-listp t)

(defthm all-good-dr-state-p-all-dr-state-p
  (implies (all-good-dr-state-p drn-sts)
           (all-dr-state-p drn-sts))
  :hints (("Goal" :in-theory (enable all-good-dr-state-p))))

(defexists exists-dr-state-with-id-p (drn-id drn-sts) (equal drn-id (dr-state->drone-id drn-sts))
  :fixed (drn-id) :guard (all-dr-state-p drn-sts))

(defmap dr-state-drone-ids (drn-sts) (dr-state->drone-id drn-sts)
  :declares ((xargs :guard (all-dr-state-p drn-sts))))

(defthm memberp-of-dr-state->drone-id-and-dr-state-drone-ids
  (implies (memberp drn-st (double-rewrite drn-sts))
           (memberp (dr-state->drone-id drn-st)
                          (dr-state-drone-ids drn-sts)))
  :hints (("Goal" :in-theory (enable dr-state-drone-ids))))

(defthm subsequencep-equal-of-dr-state-drone-ids-of-cdr-of-member-equal-of-lemma
  (subsequencep-equal (dr-state-drone-ids (cdr (member-equal drn-st drn-sts)))
             (cdr (member-equal (dr-state->drone-id drn-st)
                                (dr-state-drone-ids drn-sts))))
  :hints (("Goal" :in-theory (enable dr-state-drone-ids))))

(defthm subsequencep-equal-of-dr-state-drone-ids-and-dr-state-drone-ids
  (implies (subsequencep-equal (double-rewrite drn-sts1)
                      (double-rewrite drn-sts2))
           (subsequencep-equal (dr-state-drone-ids drn-sts1)
                      (dr-state-drone-ids drn-sts2)))
  :hints (("Goal" :in-theory (enable dr-state-drone-ids
                                     subsequencep-equal))))

(define unique-id-dr-state-list-p ((drn-sts all-dr-state-p))
  :returns (b booleanp)
  (no-duplicatesp-equal (dr-state-drone-ids drn-sts))
///
(defthm unique-id-dr-state-list-p-cdr
  (implies (and (unique-id-dr-state-list-p drn-sts)
                (consp (double-rewrite drn-sts)))
           (unique-id-dr-state-list-p (cdr drn-sts))))
(defthm unique-id-dr-state-list-p-replace-car
  (implies (and (unique-id-dr-state-list-p (cons drn-st1 drn-sts))
                (equal (dr-state->drone-id (double-rewrite drn-st1))
                       (dr-state->drone-id (double-rewrite drn-st2))))
           (unique-id-dr-state-list-p (cons drn-st2 drn-sts))))
(defthm unique-id-dr-state-list-p-all-dr-state-p-not-member
  (implies (unique-id-dr-state-list-p drn-sts)
           (not (memberp (dr-state->drone-id (car drn-sts))
                               (dr-state-drone-ids (cdr drn-sts))))))
(defthm unique-id-dr-state-list-subsequencep-equal
  (implies (and (subsequencep-equal (double-rewrite drn-sts1) drn-sts)
                (unique-id-dr-state-list-p drn-sts))
           (unique-id-dr-state-list-p drn-sts1))
  :hints (("Goal" :use (:instance no-duplicatesp-equal-when-subsequencep-equal
                                  (x (dr-state-drone-ids drn-sts1))
                                  (y (dr-state-drone-ids drn-sts)))
           :in-theory (disable no-duplicatesp-equal-when-subsequencep-equal))))
(defthm unique-id-dr-state-list-p-cons-equal-drone-id
  (implies (and (unique-id-dr-state-list-p (cons drn-st drn-sts))
                (equal (dr-state->drone-id (double-rewrite drn-st1))
                       (dr-state->drone-id (double-rewrite drn-st))))
           (unique-id-dr-state-list-p (cons drn-st1 drn-sts))))
) ; unique-id-dr-state-list-p

(defthm memberp-but-not-cdr
  (implies (and (consp (double-rewrite l))
                (not (memberp x (cdr l))))
           (equal (memberp x l)
                  (equal x (car (double-rewrite l))))))

(defthmd not-member-dr-state-drone-ids
  (implies (not (memberp (dr-state->drone-id (double-rewrite drn-st))
                         (dr-state-drone-ids drn-sts)))
           (not (memberp drn-st drn-sts)))
  :hints (("Goal" :in-theory (enable dr-state-drone-ids))))

;; 10/19/18: Doesn't seem to be used
(defthmd not-member-drone-ids-member
  (implies (and (all-dr-state-p drn-sts)
                (consp (double-rewrite drn-sts))
                (not (memberp (dr-state->drone-id (double-rewrite drn-st))
                              (dr-state-drone-ids (cdr drn-sts)))))
           (equal (memberp drn-st drn-sts)
                  (equal drn-st (car (double-rewrite drn-sts))))))

(defthm not-member-cdr-not-equal-car-drone-id-not-member
  (implies (and (not (equal drn-st (car drn-sts)))
                (not (memberp (dr-state->drone-id drn-st)
                                    (dr-state-drone-ids (cdr drn-sts)))))
           (not (memberp drn-st drn-sts)))
  :hints (("Goal" :in-theory (enable dr-state-drone-ids))))

(defthmd memberp-but-not-cdr-drone-ids
  (implies (and ;(unique-id-dr-state-list-p drn-sts)
                (consp drn-sts)
                (not (memberp (dr-state->drone-id drn-st) (dr-state-drone-ids (cdr drn-sts)))))
           (equal (memberp drn-st drn-sts)
                  (equal drn-st (car drn-sts))))
  :hints (("Goal" :in-theory (enable unique-id-dr-state-list-p no-duplicatesp-equal))))

(defthm unique-id-dr-state-list-p-equal-drone-ids
  (implies (and (unique-id-dr-state-list-p drn-sts)
                (memberp drn-i drn-sts)
                (memberp drn-j drn-sts))
         (iff (equal (dr-state->drone-id drn-i)
                     (dr-state->drone-id drn-j))
              (equal drn-i drn-j)))
  :hints (("Goal" :in-theory (enable unique-id-dr-state-list-p dr-state-drone-ids))))

(define good-dr-state-list-p (drn-sts)
   :returns (b booleanp)
   :enabled t
   (and (all-good-dr-state-p drn-sts)
        (unique-id-dr-state-list-p drn-sts))
///
(defthm good-dr-state-list-p-all-good-dr-state-p
  (implies (good-dr-state-list-p drn-sts)
           (all-good-dr-state-p drn-sts)))
(defthm good-dr-state-list-p-unique-id-dr-state-list-p
  (implies (good-dr-state-list-p drn-sts)
           (unique-id-dr-state-list-p drn-sts)))
(defthm good-dr-state-list-p-not-consp
  (implies (not (consp drn-sts))
           (equal (good-dr-state-list-p drn-sts)
                  (not drn-sts))))
(defthm good-dr-state-list-p-cdr
  (implies (good-dr-state-list-p drn-sts)
           (good-dr-state-list-p (cdr drn-sts)))
  :hints (("Goal" :in-theory (enable unique-id-dr-state-list-p))))
(defthm exists-dr-state-with-id-p-member-drone-id
  (implies (good-dr-state-list-p drn-sts)
           (equal (exists-dr-state-with-id-p drn-id drn-sts)
                  (memberp drn-id (dr-state-drone-ids drn-sts))))
  :hints (("Goal" :in-theory (enable exists-dr-state-with-id-p dr-state-drone-ids))))
(defthm not-exists-dr-state-with-id-p-car-cdr
  (implies (good-dr-state-list-p drn-sts)
           (not (exists-dr-state-with-id-p (dr-state->drone-id (car drn-sts))
                                           (cdr drn-sts))))
  :hints (("Goal" :in-theory (enable unique-id-dr-state-list-p))))
(defthm good-dr-state-list-p-equal-drone-ids
  (implies (and (good-dr-state-list-p drn-sts)
                (memberp drn-i drn-sts)
                (memberp drn-j drn-sts))
           (iff (equal (dr-state->drone-id drn-i)
                       (dr-state->drone-id drn-j))
                (equal drn-i drn-j))))
(defthm good-dr-state-list-p-member-good-dr-state-p
  (implies (and (good-dr-state-list-p drn-sts)
                (memberp drn-st drn-sts))
           (good-dr-state-p drn-st)))
) ; good-dr-state-list-p

(defthm good-dr-state-list-p-cons
  (implies (good-dr-state-list-p (cons drn-st drn-sts))
           (good-dr-state-list-p drn-sts))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable good-dr-state-list-p unique-id-dr-state-list-p))))

(defthm good-dr-state-list-p-cons-equal-drone-id
  (implies (and (good-dr-state-list-p (cons drn-st drn-sts))
                (good-dr-state-p drn-st1)
                (equal (dr-state->drone-id drn-st1)
                       (dr-state->drone-id drn-st)))
           (good-dr-state-list-p (cons drn-st1 drn-sts)))
  :hints (("Goal" :in-theory (enable good-dr-state-list-p))))

(define drn-st-with-id ((drn-id drone-id-p) (drn-sts good-dr-state-list-p))
  :returns (drn-st* good-dr-state*-p :hyp (good-dr-state-list-p drn-sts))
  (if (endp drn-sts)
      nil
    (if (equal drn-id (dr-state->drone-id (first drn-sts)))
        (first drn-sts)
      (drn-st-with-id drn-id (rest drn-sts))))
///
(defthm drn-st-with-id-empty
  (equal (drn-st-with-id id nil)
         nil))
(defthm good-dr-state-p-drn-st-with-id
  (implies (and (good-dr-state-list-p drn-sts)
                (drn-st-with-id drn-id drn-sts))
           (good-dr-state-p (drn-st-with-id drn-id drn-sts))))
(defthm dr-state->drone-id-of-drn-st-with-id
  (implies (drn-st-with-id drn-id drn-sts)
           (equal (dr-state->drone-id (drn-st-with-id drn-id drn-sts))
                  drn-id)))
(defthm drn-st-with-id-memberp
  (implies (drn-st-with-id drn-id drn-sts)
           (memberp (drn-st-with-id drn-id drn-sts) drn-sts)))
(defthm drn-st-with-id-drone-id-car
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts))
           (equal (drn-st-with-id (dr-state->drone-id (car drn-sts))
                                  drn-sts)
                  (car drn-sts))))
(defthm good-dr-state*-p-drn-st-with-id
  (implies (good-dr-state-list-p drn-sts)
           (good-dr-state*-p (drn-st-with-id id drn-sts))))
) ; drn-st-with-id

(defthm drn-st-with-id-memberp-dr-state-ext-drone-ids
  (implies (and (good-dr-state-list-p drn-sts)
                (memberp drn-id (dr-state-drone-ids drn-sts)))
           (drn-st-with-id drn-id drn-sts))
  :hints (("Goal" :in-theory (enable drn-st-with-id dr-state-drone-ids))))

(defthm drn-st-with-id-empty-cdr
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts)
                (not (equal drn-id
                            (dr-state->drone-id (car drn-sts)))))
           (equal (drn-st-with-id drn-id drn-sts)
                  (drn-st-with-id drn-id (cdr drn-sts))))
  :hints (("Goal" :use drn-st-with-id)))

(define replace-dr-st ((drn-sts good-dr-state-list-p)
                       (new-drn-st good-dr-state-p))
  :returns (new-drn-sts all-good-dr-state-p :hyp :guard)
  (if (endp drn-sts)
      nil
    (if (equal (dr-state->drone-id new-drn-st) (dr-state->drone-id (first drn-sts)))
        (cons new-drn-st (rest drn-sts))
      (cons (first drn-sts)
            (replace-dr-st (rest drn-sts) new-drn-st))))
///
(defthm exists-dr-state-with-id-p-of-replace-dr-st-1
  (implies (not (exists-dr-state-with-id-p drn-id drn-sts))
           (not (exists-dr-state-with-id-p drn-id (replace-dr-st drn-sts new-drn-st)))))
(defthm dr-state-drone-ids-replace-dr-st
  (equal (dr-state-drone-ids (replace-dr-st drn-sts new-drn-st))
         (dr-state-drone-ids drn-sts)))
(defthm unique-id-dr-state-list-p-of-replace-dr-st
  (implies (unique-id-dr-state-list-p drn-sts)
           (unique-id-dr-state-list-p (replace-dr-st drn-sts new-drn-st)))
  :hints (("Goal" :in-theory (enable unique-id-dr-state-list-p))))
) ; replace-dr-st

(defthm good-dr-state-list-p-of-replace-dr-st
  (implies (and (good-dr-state-list-p drn-sts)
                (good-dr-state-p new-drn-st))
           (good-dr-state-list-p (replace-dr-st drn-sts new-drn-st))))

(defthm exists-dr-state-with-id-p-drn-st-with-id
  (implies (good-dr-state-list-p drn-sts)
           (iff (drn-st-with-id id drn-sts)
                (exists-dr-state-with-id-p id drn-sts)))
  :hints (("Goal" :in-theory (enable drn-st-with-id exists-dr-state-with-id-p))))

(defthm exists-dr-state-with-id-p-not-member-drone-ids
  (implies (and (good-dr-state-list-p drn-sts)
                (exists-dr-state-with-id-p id drn-sts))
           (memberp id (dr-state-drone-ids drn-sts)))
  :hints (("Goal" :in-theory (e/d (exists-dr-state-with-id-p) (exists-dr-state-with-id-p-drn-st-with-id)))))

(defthm good-dr-state-list-p-not-exists-dr-state-with-id-p-car-cdr
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts))
           (not (exists-dr-state-with-id-p (dr-state->drone-id (car drn-sts))
                                           (cdr drn-sts))))
  :hints (("Goal" :in-theory (enable unique-id-dr-state-list-p no-duplicatesp-equal dr-state-drone-ids))))

(defthm good-dr-state-list-p-not-drn-st-with-id-car-cdr
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts))
           (not (drn-st-with-id (dr-state->drone-id (car drn-sts))
                               (cdr drn-sts)))))

(in-theory (disable good-dr-state-list-p))

(defthm good-dr-state-list-p-not-drn-st-with-id-cons
  (implies (good-dr-state-list-p (cons drn drn-sts))
           (not (drn-st-with-id (dr-state->drone-id drn)
                               drn-sts)))
  :hints (("Goal" :in-theory (disable good-dr-state-list-p-not-drn-st-with-id-car-cdr)
           :use (:instance good-dr-state-list-p-not-drn-st-with-id-car-cdr
                           (drn-sts (cons drn drn-sts))))))

(defthm good-dr-state-list-p-drn-st-with-id-cons
  (implies (and (good-dr-state-list-p (cons drn drn-sts))
                (drn-st-with-id id drn-sts))
           (equal (drn-st-with-id id (cons drn drn-sts))
                  (drn-st-with-id id drn-sts)))
  :hints (("Goal" :in-theory (e/d (drn-st-with-id) (good-dr-state-list-p-cons)))))

(defthm unique-id-dr-state-list-p-drone-id
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts)
                (drn-st-with-id id (cdr drn-sts)))
           (not (equal (dr-state->drone-id (car drn-sts))
                       (dr-state->drone-id (drn-st-with-id id (cdr drn-sts))))))
  :hints (("Goal" :in-theory (enable exists-dr-state-with-id-p ))))

(defthm unique-id-dr-state-list-p-drone-id-2
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts)
                (drn-st-with-id id (cdr drn-sts)))
           (not (equal (dr-state->drone-id (car drn-sts))
                       id)))
  :hints (("Goal" :in-theory (enable exists-dr-state-with-id-p drn-st-with-id))))

(defthm replace-dr-st-drn-st-with-id
  (implies (and (good-dr-state-list-p drn-sts)
                (drn-st-with-id id drn-sts))
           (equal (replace-dr-st drn-sts (drn-st-with-id id drn-sts))
                  drn-sts))
  :hints (("Goal" :in-theory (enable replace-dr-st drn-st-with-id dr-state-drone-ids-opener))))

(defthm drn-st-with-id-replace-dr-st
  (implies (and (good-dr-state-list-p drn-sts)
                (not (equal drn-id (dr-state->drone-id new-drn-st))))
           (equal (drn-st-with-id drn-id (replace-dr-st drn-sts new-drn-st))
                  (drn-st-with-id drn-id drn-sts)))
  :hints (("Goal" :in-theory (enable replace-dr-st drn-st-with-id))))

(define init-loc-map-to-drn-states ((m loc-map-p) (g dgraph-p))
  :guard (and (no-duplicatesp-equal (alist-keys m))
              (subsetp-equal (alist-vals m) (dgraph->nodes g)))
  :returns (drn-sts all-dr-state-p)
  (let ((m (loc-map-fix m)))
    (if (endp m)
        ()
      (let ((init-path (list (cdar m))))
        (cons (dr-state (caar m) g init-path init-path)
              (init-loc-map-to-drn-states (rest m) g)))))
///
(defthm dr-state-drone-ids-init-loc-map-to-drn-states
  (implies (loc-map-p m)
           (equal (dr-state-drone-ids (init-loc-map-to-drn-states m g))
                  (alist-keys m))))
(defthm all-good-dr-state-p-init-loc-map-to-drn-states
  (implies (and (loc-map-p m)
                (wf-dgraph-p g)
                (subsetp-equal (alist-vals m) (dgraph->nodes g)))
           (all-good-dr-state-p (init-loc-map-to-drn-states m g))))
) ; init-loc-map-to-drn-states

(defthm unique-id-dr-state-list-p-init-loc-map-to-drn-states
  (implies (and (loc-map-p m)
                (no-duplicatesp-equal (alist-keys m))
                (dgraph-p g))
           (unique-id-dr-state-list-p (init-loc-map-to-drn-states m g)))
  :hints (("Goal" :in-theory (enable unique-id-dr-state-list-p))))

(defthm good-dr-state-list-p-init-loc-map-to-drn-states
  (implies (and (loc-map-p m)
                (wf-dgraph-p g)
                (no-duplicatesp-equal (alist-keys m))
                (subsetp-equal (alist-vals m) (dgraph->nodes g)))
           (good-dr-state-list-p (init-loc-map-to-drn-states m g)))
  :hints (("Goal" :in-theory (enable good-dr-state-list-p))))

(define dr-state-path-map ((drn-sts good-dr-state-list-p))
  :returns (pm true-alistp;; path-map-p :hyp :guard
              :hints (("Goal" :in-theory (enable true-alistp))))
  (if (endp drn-sts)
      ()
    (cons (cons (dr-state->drone-id (first drn-sts))
                (dr-state->path-taken (first drn-sts)))
          (dr-state-path-map (rest drn-sts)))))

;;; Coordinator state

(fty::defprod coord-state
              ((visited-nodes node-list)
               (dgraph dgraph-p))
              :verbosep t)

(define coord-state-new-visited-nodes ((new-visited-nodes node-list-p) (coord-st coord-state-p))
  :returns (new-coord-st coord-state-p)
  (change-coord-state coord-st
                      :visited-nodes
                      (union-equal (coord-state->visited-nodes coord-st)
                                   new-visited-nodes)))

(define drone-location ((drn-st dr-state-p))
  :returns (loc (or (null loc) (nodep loc)))
  (let ((path (dr-state->path-taken drn-st)))
    (if (consp path)
        (car (last path))
      nil))
///
(defthm nodep-drone-location-when-not-null
  (implies (drone-location drn-st)
           (nodep (drone-location drn-st))))
(defthm good-dr-state-p-drone-location-nodep
  (implies (good-dr-state-p drn-st)
           (nodep (drone-location drn-st))))
(defthm node-path-p-list-drone-location
  (implies (good-dr-state-p drn-st)
           (node-path-p (list (drone-location drn-st)) (dr-state->dgraph drn-st)))
  :hints (("Goal" :in-theory (disable node-path-p-sublistp-member)
           :use (:instance node-path-p-sublistp-member
                           (x (car (last (dr-state->path-taken drn-st))))
                           (l (dr-state->path-taken drn-st))
                           (g (dr-state->dgraph drn-st))))))
) ; drone-location

;;; Plans

(define valid-plan-p (n plan (drn-st good-dr-state-p))
  (node-path-from-p n plan (dr-state->dgraph drn-st))
///
(defthm valid-plan-p-node-path-from-p
  (implies (valid-plan-p n plan drn-st)
           (node-path-from-p n plan (dr-state->dgraph drn-st))))
(defthm not-valid-plan-p-node-path-from-p
  (implies (not (valid-plan-p n plan drn-st))
           (not (node-path-from-p n plan (dr-state->dgraph drn-st)))))
(defthm valid-plan-p-node-path-p
  (implies (valid-plan-p n plan drn-st)
           (node-path-p plan (dr-state->dgraph drn-st)))
  :rule-classes (:rewrite :forward-chaining))
) ; valid-plan-p

(define extend-path-taken ((drn-st good-dr-state-p) (plan node-list-p))
  :guard (valid-plan-p (drone-location drn-st) plan drn-st)
  :no-function t
  :returns (new-drn-st (good-dr-state-p new-drn-st)
                       :hyp (good-dr-state-p drn-st)
                       :hints (("Goal" :in-theory (enable valid-plan-p good-dr-state-p
                                                          drone-location))))
  (if (mbt (and (good-dr-state-p drn-st)
                (valid-plan-p (drone-location drn-st) plan drn-st)))
      (let ((new-visited-nodes (union-equal (dr-state->visited-nodes drn-st)
                                                  plan))
            (new-path-taken (append (dr-state->path-taken drn-st)
                                          plan)))
        (dr-state (dr-state->drone-id drn-st)
                  (dr-state->dgraph drn-st)
                  new-visited-nodes
                  new-path-taken))
    drn-st)
///
(defthm path-taken-extend-path-taken
  (implies (and (good-dr-state-p drn-st)
                (or (null plan)
                    (valid-plan-p (drone-location drn-st)
                                  plan drn-st)))
           (equal (dr-state->path-taken (extend-path-taken drn-st plan))
                  (append (dr-state->path-taken drn-st)
                          plan)))
  :hints (("Goal" :in-theory (enable valid-plan-p good-dr-state-p drone-location))))
(defthm subsetp-equal-plan-extend-path-taken
  (implies (and (good-dr-state-p drn-st)
                (or (null plan)
                    (valid-plan-p (drone-location drn-st)
                                  plan drn-st)))
           (subsetp-equal plan (dr-state->visited-nodes (extend-path-taken drn-st plan)))))
(defthm visited-nodes-extend-path-taken
  (implies (and (good-dr-state-p drn-st)
                (or (null plan)
                    (valid-plan-p (drone-location drn-st)
                                  plan drn-st)))
           (equal (dr-state->visited-nodes (extend-path-taken drn-st plan))
                  (union-equal (dr-state->visited-nodes drn-st)
                               plan))))
) ; extend-path-taken

(defthm dr-state->drone-id-of-extend-path-taken
  (equal (dr-state->drone-id (extend-path-taken drn-st plan))
         (dr-state->drone-id drn-st))
  :hints (("Goal" :in-theory (enable extend-path-taken))))
(defthm dgraph-extend-path-taken
  (equal (dr-state->dgraph (extend-path-taken drn-st plan))
         (dr-state->dgraph drn-st))
  :hints (("Goal" :in-theory (enable extend-path-taken))))


(defforall all-valid-plan-p (n plans drn-st) (valid-plan-p n plans drn-st) :fixed (n drn-st) :true-listp t
  :guard (good-dr-state-p drn-st))

(defthm all-valid-plan-p-all-node-path-p
  (implies (all-valid-plan-p n plans drn-st)
           (all-node-path-p plans (dr-state->dgraph drn-st)))
  :hints (("Goal" :in-theory (enable all-valid-plan-p all-node-path-p))))

(defthm all-node-path-from-p-all-valid-plan-p
  (implies (all-node-path-from-p n plans (dr-state->dgraph drn-st))
           (all-valid-plan-p n plans drn-st))
  :hints (("Goal" :in-theory (enable all-valid-plan-p all-node-path-from-p))))

(defthm all-valid-plan-p-all-node-list-p
  (implies (all-valid-plan-p n plans drn-st)
           (all-node-list-p plans))
  :hints (("Goal" :in-theory (disable all-node-path-p-all-node-list-p)
           :use (:instance all-node-path-p-all-node-list-p (l plans) (g (dr-state->dgraph drn-st))))))

(defthm valid-plan-p-member-adj
  (implies (and (consp plan)
                (valid-plan-p (drone-location drn-st)
                             plan drn-st))
           (memberp (car plan)
                          (adj-nodes (drone-location drn-st)
                                     (dr-state->dgraph drn-st))))
  :hints (("Goal" :in-theory (enable node-path-from-p valid-plan-p))))

;;; plan maps are from drone-id's to lists of plans
(defun valid-plan-map-pair-p (pm-pair drn-sts)
  (declare (xargs :guard (good-dr-state-list-p drn-sts)))
  (and (consp pm-pair)
       (drone-id-p (car pm-pair))
       (all-node-list-p (cdr pm-pair))
       ;(good-dr-state-list-p drn-sts)
       (let ((drn-st (drn-st-with-id (car pm-pair) drn-sts)))
         (and drn-st
              (all-valid-plan-p (drone-location drn-st)
                               (cdr pm-pair)
                               drn-st)))))

(defthm valid-plan-map-pair-p-all-valid-plan-p-drn-st-with-id
  (implies (valid-plan-map-pair-p pm-pair drn-sts)
           (all-valid-plan-p (drone-location (drn-st-with-id (car pm-pair) drn-sts))
                            (cdr pm-pair)
                            (drn-st-with-id (car pm-pair) drn-sts))))

(defthm valid-plan-map-pair-p-true-p
  (implies (valid-plan-map-pair-p pm-pair drn-sts)
           (consp pm-pair)))

(defthm valid-plan-map-pair-p-all-node-list-p
  (implies (valid-plan-map-pair-p pm-pair drn-sts)
           (all-node-list-p (cdr pm-pair))))

(defthm valid-plan-map-pair-p-replace-dr-st
    (implies (and (valid-plan-map-pair-p drn-plan-pair drn-sts)
                  (good-dr-state-list-p drn-sts)
                  (good-dr-state-p new-drn-st)
                  (equal dr-id (car drn-plan-pair))
                  (not (equal (dr-state->drone-id new-drn-st) dr-id))
                  (drn-st-with-id dr-id drn-sts))
             (valid-plan-map-pair-p drn-plan-pair (replace-dr-st drn-sts new-drn-st))))

(defforall valid-plan-map-p0 (pm drn-sts) (valid-plan-map-pair-p pm drn-sts) :fixed (drn-sts)
  :guard (good-dr-state-list-p drn-sts) :true-listp t)

(defthm valid-plan-map-p0-plan-map-p0
  (implies (valid-plan-map-p0 pm drn-sts)
           (plan-map-p0 pm))
  :hints (("Goal" :in-theory (enable valid-plan-map-p0 plan-map-p))))

(defexists exists-pair-with-car-p (x l) (equal x (car l))
  :fixed x :guard (alistp l))

(defthm exists-pair-with-car-p-member
  (implies (force x)
           (iff (exists-pair-with-car-p x l)
                (memberp x (alist-keys l))))
  :hints (("Goal" :in-theory (enable alist-keys))))

(define unique-domain-map-p ((m alistp))
  :returns (b booleanp)
  (no-duplicatesp-equal (alist-keys m)))

(defthm unique-domain-map-p-no-duplicate-alist-p
  (implies (unique-domain-map-p m)
           (no-duplicate-alist-p m))
  :hints (("Goal" :in-theory (enable unique-domain-map-p no-duplicate-alist-p))))

(defthm unique-domain-map-p-cdr
  (implies (unique-domain-map-p m)
           (unique-domain-map-p (cdr m)))
  :hints (("Goal" :in-theory (enable unique-domain-map-p alist-keys))))

(defthm unique-domain-map-p-member-alist-keys-cdr
  (implies (and (unique-domain-map-p m)
                (consp m)
                (consp (car m)))
           (not (member (caar m)
                        (alist-keys (cdr m)))))
  :hints (("Goal" :in-theory (enable unique-domain-map-p alist-keys))))

(define valid-plan-map-p (pm (drn-sts good-dr-state-list-p))
  :returns (b booleanp)
  (and (valid-plan-map-p0 pm drn-sts)
       (unique-domain-map-p pm))
///
(defthm valid-plan-map-p-empty
  (valid-plan-map-p nil drn-sts))
(defthm valid-plan-map-plan-map-p
  (implies (valid-plan-map-p pm drn-sts)
           (plan-map-p pm)))
(defthm valid-plan-map-p-drn-st-with-id
  (implies (and (consp pm)
                (valid-plan-map-p pm drn-sts))
           (drn-st-with-id (caar pm) drn-sts)))
(defthm valid-plan-map-p-valid-plan-map-pair-p
  (implies (and (valid-plan-map-p pm drn-sts)
                (memberp pr pm))
           (valid-plan-map-pair-p pr drn-sts)))
(defthm valid-plan-map-p-not-consp
  (implies (not (consp plan-map))
           (equal (valid-plan-map-p plan-map drn-sts)
                  (not plan-map))))
(defthm valid-plan-map-p-drone-id-p-caar
  (implies (and (valid-plan-map-p plan-map drn-sts)
                (consp plan-map))
           (drone-id-p (car (car plan-map)))))
(defthm all-node-list-p-valid-plan-map-p-cdar
  (implies (valid-plan-map-p plan-map drn-sts)
           (all-node-list-p (cdar plan-map))))
(defthm valid-plan-map-p-not-car
  (implies (and (valid-plan-map-p plan-map drn-sts)
                (not (consp (car plan-map))))
           (not (car plan-map))))
) ; valid-plan-map-p

(defthm valid-plan-map-p-first-second-ids-differ
  (implies (and (valid-plan-map-p plan-map drn-sts)
                (good-dr-state-list-p drn-sts)
                (consp plan-map)
                (consp (cdr plan-map)))
           (not (equal (car (first plan-map))
                            (car (second plan-map)))))
  :hints (("Goal" :in-theory (enable valid-plan-map-p valid-plan-map-p0 unique-domain-map-p))))

(defthm valid-plan-map-p0-replace-dr-st
  (implies (and (valid-plan-map-p0 plan-map drn-sts)
                (not (exists-pair-with-car-p (dr-state->drone-id new-drn-st)
                                             plan-map))
                (good-dr-state-list-p drn-sts)
                (good-dr-state-p new-drn-st))
           (valid-plan-map-p0 plan-map
                              (replace-dr-st drn-sts new-drn-st)))
  :hints (("Goal" :in-theory (enable valid-plan-map-p0))))

(defthm valid-plan-map-p0-cdr-valid-plan-map-p0-not-exists-pair-with-car-p
  (implies (and (valid-plan-map-p0 plan-map drn-sts)
                (unique-domain-map-p plan-map)
                (good-dr-state-list-p drn-sts)
                (good-dr-state-p new-drn-st)
                (consp plan-map))
           (not (exists-pair-with-car-p (car (car plan-map))
                                        (cdr plan-map))))
  :hints (("Goal" :in-theory (disable unique-domain-map-p-member-alist-keys-cdr alist-keys-member-hons-assoc-equal)
           :use (:instance unique-domain-map-p-member-alist-keys-cdr (m plan-map)))))

(defthm valid-plan-map-p0-cdr-valid-plan-map-p0-replace-dr-st-1
  (implies (and (valid-plan-map-p0 plan-map drn-sts)
                (unique-domain-map-p plan-map)
                (good-dr-state-list-p drn-sts)
                (good-dr-state-p new-drn-st)
                (consp plan-map)
                (equal (dr-state->drone-id new-drn-st)
                       (car (car plan-map))))
           (valid-plan-map-p0 (cdr plan-map)
                              (replace-dr-st drn-sts new-drn-st)))
  :hints (("Goal" :in-theory (disable valid-plan-map-p0-cdr-valid-plan-map-p0-not-exists-pair-with-car-p)
           :use (:instance valid-plan-map-p0-cdr-valid-plan-map-p0-not-exists-pair-with-car-p))))

(defthm valid-plan-map-p-replace-dr-st-car-cdr
  (implies (and (valid-plan-map-p plan-map drn-sts)
                (good-dr-state-list-p drn-sts)
                (good-dr-state-p new-drn-st)
                (consp plan-map)
                (equal dr-id (caar plan-map))
                (equal (dr-state->drone-id new-drn-st) dr-id))
           (valid-plan-map-p (cdr plan-map)
                             (replace-dr-st drn-sts new-drn-st)))
  :hints (("Goal" :in-theory (enable valid-plan-map-p))))


(defthm compatible-dr-state-list-p-map-domain
  (implies (equal (alist-keys plan) (dr-state-drone-ids drn-sts))
           (iff (unique-domain-map-p plan)
                (unique-id-dr-state-list-p drn-sts)))
  :hints (("Goal" :in-theory (enable unique-domain-map-p unique-id-dr-state-list-p))))

(defthm compatible-dr-state-list-p-map-domain-1
  (implies (and (good-dr-state-list-p drn-sts)
                (equal (alist-keys plan) (dr-state-drone-ids drn-sts)))
           (unique-domain-map-p plan)))


(defthm unique-domain-map-p-good-dr-state-list-p
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts)
                (equal (alist-keys plan) (dr-state-drone-ids (cdr drn-sts))))
           (unique-domain-map-p (cons (cons (dr-state->drone-id (car drn-sts))
                                            plans)
                                      plan))))

(defthm valid-plan-map-p0-cons-drn-sts
  (implies
     (and (good-dr-state-list-p (cons drn-st drn-sts))
          (valid-plan-map-p0 plan drn-sts)
          (not (exists-dr-state-with-id-p (dr-state->drone-id drn-st) drn-sts)))
     (valid-plan-map-p0 plan (cons drn-st drn-sts)))
  :hints (("Goal" :in-theory (enable valid-plan-map-p0))))

(defthm valid-plan-map-p0-cdr
  (implies
     (and (good-dr-state-list-p drn-sts)
          (consp drn-sts)
          (valid-plan-map-p0 plan (cdr drn-sts))
          (equal (alist-keys plan)
                 (dr-state-drone-ids (cdr drn-sts))))
     (valid-plan-map-p0 plan drn-sts))
  :hints (("Goal" :in-theory (disable valid-plan-map-p0-cons-drn-sts)
           :use (:instance valid-plan-map-p0-cons-drn-sts
                           (drn-sts (cdr drn-sts))
                           (drn-st (car drn-sts) )))))

(defthm valid-map-p0-good-dr-state-list-p
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts)
                (valid-plan-map-p0 plan (cdr drn-sts))
                (all-valid-plan-p (drone-location (car drn-sts))
                                  plans
                                  (car drn-sts))
                (equal (alist-keys plan) (dr-state-drone-ids (cdr drn-sts))))
           (valid-plan-map-p0 (cons (cons (dr-state->drone-id (car drn-sts))
                                          plans)
                                    plan)
                              drn-sts))
  :hints (("Goal" :in-theory (enable valid-plan-map-p0)
           :do-not-induct t)))

(defthm valid-map-p-good-dr-state-list-p
  (implies (and (good-dr-state-list-p drn-sts)
                (consp drn-sts)
                (valid-plan-map-p plan (cdr drn-sts))
                (all-valid-plan-p (drone-location (car drn-sts))
                                 plans
                                 (car drn-sts))
                (equal (alist-keys plan) (dr-state-drone-ids (cdr drn-sts))))
           (valid-plan-map-p (cons (cons (dr-state->drone-id (car drn-sts))
                                         plans)
                                   plan)
                             drn-sts))
  :hints (("Goal" :in-theory (enable valid-plan-map-p))))
