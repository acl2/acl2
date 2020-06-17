; Basic implementation for Distributed Drone Surveillance
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dp-impl-support")

(define visitedp ((n nodep) (drn-st good-dr-state-p))
  ;:guard (memberp n (dgraph->nodes (dr-state->dgraph drn-st)))
  :returns (b booleanp)
  (memberp n (dr-state->visited-nodes drn-st)))

(define visited-by-some-p ((n nodep) (drn-sts good-dr-state-list-p))
  :returns (b booleanp)
  (if (endp drn-sts)
      nil
    (or (visitedp n (first drn-sts))
        (visited-by-some-p n (rest drn-sts)))))

(define all-visitedp ((l node-list-p) (drn-sts good-dr-state-list-p))
  ;; :guard (subsetp-equal l (dgraph->nodes (dr-state->dgraph drn-st)))
  :returns (b booleanp)
  ;; (subsetp-equal l (dr-state->visited-nodes drn-st))
  (if (endp l)
      (mbt (null l))
    (and (visited-by-some-p (first l) drn-sts)
         (all-visitedp (rest l) drn-sts)))
///
(defthm all-visitedp-nil
  (all-visitedp nil drn-sts))
)


(defmap initial-assign-fn (dr-ids nodes)
  (cons (drone-id-fix dr-ids)
        (node-fix (first nodes)))
  :fixed nodes
  :declares ((xargs :guard (and (drone-id-list-p dr-ids)
                                (node-list-p nodes)
                                (no-duplicatesp-equal dr-ids)
                                (consp nodes)))))
(defthm alist-keys-of-initial-assign-fn
  (implies (drone-id-list-p dr-ids)
           (equal (alist-keys (initial-assign-fn dr-ids nodes))
                  dr-ids))
  :hints (("Goal" :in-theory (enable initial-assign-fn))))
(defthm loc-map-p-of-initial-assign-fn
  (implies (and (drone-id-list-p dr-ids)
                (node-list-p nodes)
                (no-duplicatesp-equal (double-rewrite dr-ids))
                (consp (double-rewrite nodes)))
           (loc-map-p (initial-assign-fn dr-ids nodes)))
  :hints (("Goal" :in-theory (enable initial-assign-fn))))
(defthm no-duplicate-alist-p-of-initial-assign-fn
  (implies (and (consp (dgraph->nodes g))
                (consp (double-rewrite dr-ids))
                (no-duplicatesp-equal (double-rewrite dr-ids))
                (wf-dgraph-p g)
                (drone-id-list-p dr-ids))
           (no-duplicate-alist-p (initial-assign-fn dr-ids (dgraph->nodes g))))
  :hints (("Goal" :in-theory (enable no-duplicate-alist-p))))
(defthm loc-map-p0-of-initial-assign-fn
  (implies (and (consp (double-rewrite dr-ids))
                (consp (dgraph->nodes g))
                (wf-dgraph-p g)
                (drone-id-list-p dr-ids))
           (loc-map-p0 (initial-assign-fn dr-ids (dgraph->nodes g))))
  :hints (("Goal" :in-theory (enable initial-assign-fn))))

(defthm alist-keys-initial-assign-fn
  (implies (drone-id-list-p dr-ids)
           (equal (alist-keys (initial-assign-fn dr-ids nodes))
                  dr-ids)))
(defthm range-initial-assign-fn
  (implies (and (consp nodes)
                (node-list-p nodes))
           (subsetp-equal (alist-vals (initial-assign-fn dr-ids nodes))
                         nodes))
  :hints (("Goal" :in-theory (enable initial-assign-fn))))
(defthm node-list-p-alist-vals-initial-assign-fn
  (implies (and (consp (double-rewrite nodes))
                (node-list-p nodes))
           (node-list-p (alist-vals (initial-assign-fn dr-ids nodes))))
  :hints (("Goal" :in-theory (enable initial-assign-fn))))

(defthm drone-id-list-p-alist-keys-plan-map-p
  (implies (plan-map-p pm1)
           (drone-id-list-p (alist-keys pm1)))
  :hints (("Goal" :in-theory (enable alist-keys))))
(defthm drone-id-list-p-alist-keys-plan-map-p
  (implies (plan-map-p pm1)
           (drone-id-list-p (alist-keys pm1)))
  :hints (("Goal" :in-theory (enable alist-keys))))
(defthm drone-id-list-p-alist-keys-plan-map-p
  (implies (plan-map-p pm1)
           (drone-id-list-p (alist-keys pm1)))
  :hints (("Goal" :in-theory (enable alist-keys))))

(define initial-assign ((dr-ids drone-id-list-p) ; !!?
                        (g wf-dgraph-p))
  :guard (and (no-duplicatesp-equal dr-ids)
              (consp dr-ids)
              (consp (dgraph->nodes g)))
  :returns (mv (drn-sts good-dr-state-list-p)
               (coord-st coord-state-p))
  (if (mbt (and (drone-id-list-p dr-ids)
                (wf-dgraph-p g)
                (no-duplicatesp-equal dr-ids)
                (consp dr-ids)
                (consp (dgraph->nodes g))))
      (let* ((init-loc-map (initial-assign-fn dr-ids (dgraph->nodes g))))
        (mv (init-loc-map-to-drn-states init-loc-map g)
            (coord-state (alist-vals init-loc-map) g)))
    (mv () (coord-state () *empty-graph*))))

(define make-plans ((drn-st good-dr-state-p)) ; !!?
  :returns (plans (all-valid-plan-p (drone-location drn-st)
                                    plans
                                    drn-st)
                  :hyp :guard)
  (shortest-paths-not-ending-in-set (drone-location drn-st)
                                    1
                                    (dr-state->visited-nodes drn-st)
                                    (dr-state->dgraph drn-st)))

(defthm all-node-list-p-make-plans
  (implies (and (good-dr-state-list-p drn-sts)
                (drn-st-with-id (car (car plan-map)) drn-sts))
           (all-node-list-p (make-plans (drn-st-with-id (car (car plan-map)) drn-sts))))
  :hints (("Goal" :in-theory (disable all-valid-plan-p-all-node-list-p)
           :use (:instance all-valid-plan-p-all-node-list-p
                           (plans (make-plans (drn-st-with-id (car (car plan-map))
                                                              drn-sts)))
                           (drn-st (drn-st-with-id (car (car plan-map)) drn-sts))
                           (n (drone-location (drn-st-with-id (car (car plan-map))
                                                              drn-sts)))))))

(define choose-plan ((plans all-node-list-p) (drn-st good-dr-state-p))
  :guard (all-valid-plan-p (drone-location drn-st)
                           plans drn-st)
  :returns (plan (if (endp plans)
                     (null plan)
                   (memberp plan plans)))
  :ignore-ok t
  (if (endp plans)
      nil
    (car plans)))

(defthm choose-plan-nil
  (not (choose-plan nil drn-st))
  :hints (("Goal" :use (:instance return-type-of-choose-plan (plans nil)))))

(defthm member-choose-plan
  (implies (choose-plan plans drn-st)
           (memberp (choose-plan plans drn-st) plans))
  :hints (("Goal" :use (:instance return-type-of-choose-plan ))))

(defthm choose-plan-node-path-p
  (implies (all-node-path-p plans g)
           (node-path-p (choose-plan plans drn-st) g))
  :hints (("Goal" :in-theory (disable return-type-of-choose-plan)
           :use (:instance return-type-of-choose-plan))))

(defthm node-list-p-choose-plan
  (implies (all-node-list-p plans)
           (node-list-p (choose-plan plans drn-st)))
  :hints (("Goal" :in-theory (disable return-type-of-choose-plan)
           :use (:instance return-type-of-choose-plan))))

(defthm choose-plan-valid-plan-p
  (implies (and (all-valid-plan-p (drone-location drn-st)
                                  plans drn-st)
                (choose-plan plans drn-st))
           (valid-plan-p (drone-location drn-st)
                         (choose-plan plans drn-st)
                         drn-st))
  :hints (("Goal" :in-theory (disable return-type-of-choose-plan)
           :use (:instance return-type-of-choose-plan))))


(define execute-plan ((plan node-list-p) (drn-st good-dr-state-p))
  :guard (valid-plan-p (drone-location drn-st) plan drn-st)
  :returns (mv (new-visited-nodes node-list-p :hyp (or (null plan)
                                                       (valid-plan-p (drone-location drn-st)
                                                                     plan drn-st)))
               (new-drn-st (and (good-dr-state-p new-drn-st)
                                (equal (dr-state->drone-id new-drn-st)
                                       (dr-state->drone-id drn-st))
                                ;; (equal (dr-state->path-taken new-drn-st)
                                ;;        (append (dr-state->path-taken drn-st)
                                ;;                plan))
                                )
                           :hyp (good-dr-state-p drn-st)))
  (if (mbt (and (good-dr-state-p drn-st)
                (valid-plan-p (drone-location drn-st) plan drn-st)))
      (let* ((new-visited-nodes (set-difference-equal plan (dr-state->visited-nodes drn-st))))
        (prog2$ (cw "~x0: ~x1~%" (dr-state->drone-id drn-st) (or new-visited-nodes plan))
                (mv new-visited-nodes
                    (extend-path-taken drn-st plan))))
    (mv plan drn-st))
///
(defthm dr-state->drone-id-of-execute-plan
  (equal (dr-state->drone-id (mv-nth 1 (execute-plan plan drn-st)))
         (dr-state->drone-id drn-st)))
(defthm visitedp-execute-plan
  (implies (and (node-list-p plan)
                (memberp nd plan)
                (good-dr-state-p drn-st)
                (or (null plan)
                    (valid-plan-p (drone-location drn-st) plan drn-st)))
           (visitedp nd (mv-nth 1 (execute-plan plan drn-st))))
  :hints (("Goal" :in-theory (enable visitedp mv-nth-of-cons))))
) ; execute-plan

(defthm visited-by-some-p-execute-plan
  (implies (and (memberp drn-st (double-rewrite drn-sts))
                (visitedp nd drn-st))
           (visited-by-some-p nd drn-sts))
  :hints (("Goal" :in-theory (enable visited-by-some-p))))

(defthm dgraph-of-execute-plan
  (equal (dr-state->dgraph (mv-nth 1 (execute-plan plan drn-st)))
         (dr-state->dgraph (double-rewrite drn-st)))
  :hints (("Goal" :in-theory (enable execute-plan))))

(defthm visited-nodes-of-execute-plan
  (implies (and (good-dr-state-p drn-st)
                (or (null plan)
                    (valid-plan-p (drone-location drn-st)
                                  plan drn-st)))
           (equal (dr-state->visited-nodes (mv-nth 1 (execute-plan plan (double-rewrite drn-st))))
                  (union-equal (dr-state->visited-nodes (double-rewrite drn-st))
                               plan)))
  :hints (("Goal" :in-theory (enable execute-plan))))

(defthm all-visitedp-execute-plan-lemma
  (implies (and (node-list-p plan)
                (node-list-p plan2)
                (subsetp-equal (double-rewrite plan) (double-rewrite plan2))
                (good-dr-state-p drn-st)
                (or (null plan2)
                    (valid-plan-p (drone-location drn-st) plan2 drn-st)))
           (all-visitedp plan (list (mv-nth 1 (execute-plan plan2 drn-st)))))
  :hints (("Goal" :in-theory (enable all-visitedp visited-by-some-p))))


(defthm all-valid-plan-p-of-paths-not-ending-in-set
  (implies (all-valid-plan-p n plans dr-st)
           (all-valid-plan-p n (paths-not-ending-in-set plans nodes) dr-st))
  :hints (("Goal" :in-theory (enable paths-not-ending-in-set all-valid-plan-p))))

(defthm valid-plan-map-p-of-filter-redundant-destination-plans-1-aux
  (implies (and (valid-plan-map-p plan-map drn-sts)
                (coord-state-p coord-st)
                (plan-map-p plan-map))
           (valid-plan-map-p (filter-redundant-destination-plans-1-aux plan-map seen-dest-nodes)
                             drn-sts))
  :hints (("Goal" :in-theory (enable filter-redundant-destination-plans-1-aux valid-plan-map-p
                                     unique-domain-map-p valid-plan-map-p0))))

(define coordinate-plans ((plan-map plan-map-p) (coord-st coord-state-p))
  :returns (new-plan-map (and (sub-plan-map-p new-plan-map plan-map)
                              (implies (non-trivial-plan-map-p plan-map)
                                       (non-trivial-plan-map-p new-plan-map)))
                         :hyp :guard)
  :ignore-ok t
  (filter-redundant-destination-plans-1 plan-map)
///
(defthm coordinate-plans-valid-plan-map-p
  (implies (and (valid-plan-map-p plan-map drn-sts)
                (coord-state-p coord-st))
           (valid-plan-map-p (coordinate-plans plan-map coord-st) drn-sts))
  :hints (("Goal" :in-theory (enable coordinate-plans filter-redundant-destination-plans-1))))
)


(define drone-choose-and-execute-plan ((plans all-node-list-p)
                                       (drn-st good-dr-state-p)
                                       (coord-st coord-state-p))
  :guard (all-valid-plan-p (drone-location drn-st) plans drn-st)
                                        ; :guard-debug t
  :guard-hints (("Goal" :in-theory (disable use-all-valid-plan-p)
                 :use ((:instance use-all-valid-plan-p
                                  (n (drone-location drn-st))
                                  (x (choose-plan plans drn-st))
                                  (free-plans plans)))))
  :returns (mv (drn-st-new (and (good-dr-state-p drn-st-new)
                                (equal (dr-state->drone-id drn-st-new) (dr-state->drone-id drn-st)))
                           :hyp (good-dr-state-p drn-st)
                           :hints (("Goal" :in-theory (enable drone-choose-and-execute-plan))))
               (coord-st-new coord-state-p :hyp (coord-state-p coord-st)
                             :hints (("Goal" :in-theory (enable drone-choose-and-execute-plan)))))
  (if (mbt (all-valid-plan-p (drone-location drn-st)
                             plans drn-st))
      (let ((plan (choose-plan plans drn-st)))
        (if (null plan)
            (mv drn-st coord-st)
          (mv-let (new-visited-nodes new-drn-st)
              (execute-plan plan drn-st)
            (mv new-drn-st (coord-state-new-visited-nodes new-visited-nodes coord-st)))))
    (mv drn-st coord-st)))

(define drones-choose-and-execute-plans ((plan-map plan-map-p)
                                         (drn-sts good-dr-state-list-p)
                                         (coord-st coord-state-p))
  :guard (valid-plan-map-p plan-map drn-sts)
  :guard-hints (("Goal" :in-theory (disable all-good-dr-state-p
                                            drn-st-with-id plan-map-p ;; execute-plan
                                            use-all-valid-plan-p)
                 :use (:instance use-all-valid-plan-p
                                 (n (drone-location drn-st))
                                 (x (choose-plan plans drn-st))
                                 (free-plans plans))
                 :do-not-induct t))
  :returns (mv (drn-sts-new good-dr-state-list-p :hyp (good-dr-state-list-p drn-sts)
                            :hints (("Goal" :in-theory (disable all-good-dr-state-p drn-st-with-id plan-map-p)
                                     :induct (drones-choose-and-execute-plans plan-map drn-sts coord-st)
                                     :do-not-induct t)))
               (coord-st-new coord-state-p :hyp (coord-state-p coord-st)
                             :hints (("Goal" :in-theory (disable all-good-dr-state-p drn-st-with-id)
                                      :induct (drones-choose-and-execute-plans plan-map drn-sts coord-st)
                                      :do-not-induct t))))
  (if (mbt (and (valid-plan-map-p plan-map drn-sts)
                (plan-map-p plan-map)
                (coord-state-p coord-st)))
      (if (or (endp plan-map)
              (endp drn-sts))
          (mv drn-sts coord-st)
        (let* ((drn-id (caar plan-map))
               (drn-st (drn-st-with-id drn-id drn-sts))
               (plans (cdar plan-map)))
          (mv-let (drn-st-new coord-st-1)
              (drone-choose-and-execute-plan plans drn-st coord-st)
            (mv-let (drn-sts-new coord-st-2)
                (drones-choose-and-execute-plans (rest plan-map)
                                                 (replace-dr-st drn-sts drn-st-new)
                                                 coord-st-1)
              (mv drn-sts-new
                  ;; (replace-dr-st drn-sts-new drn-st-new)
                  coord-st-2)))))
    (mv () coord-st)))

(define get-plans-from-drones ((drn-sts good-dr-state-list-p))
  ;;:returns (plan-map (valid-plan-map-p plan-map drn-sts) :hyp :guard)
  (if (endp drn-sts)
      ()
    (cons (cons (dr-state->drone-id (first drn-sts))
                (make-plans (first drn-sts)))
          (get-plans-from-drones (rest drn-sts)))))

(defthm alist-keys-dr-state-drone-ids-get-plans-from-drones
  (implies (good-dr-state-list-p drn-sts)
           (equal (alist-keys (get-plans-from-drones drn-sts))
                  (dr-state-drone-ids drn-sts)))
  :hints (("Goal" :in-theory (enable get-plans-from-drones dr-state-drone-ids))))

(defthm return-type-of-get-plans-from-drones
  (implies (good-dr-state-list-p drn-sts)
           (valid-plan-map-p (get-plans-from-drones drn-sts)
                             drn-sts))
  :hints (("Goal" :in-theory (enable get-plans-from-drones valid-plan-map-p))))

(define run-coordinator-1 ((drn-sts good-dr-state-list-p)
                           (coord-st coord-state-p))
  :returns (mv (drn-sts-new good-dr-state-list-p :hyp (good-dr-state-list-p drn-sts)
                            :hints (("Goal" :in-theory (e/d (drones-choose-and-execute-plans)
                                                            (coordinate-plans-valid-plan-map-p))
                                     :use (:instance coordinate-plans-valid-plan-map-p
                                                     (plan-map (get-plans-from-drones drn-sts))
                                                     (drn-sts drn-sts)))))
               (coord-st-new coord-state-p :hyp (coord-state-p coord-st)
                             :hints (("Goal" :in-theory (disable coordinate-plans-valid-plan-map-p)
                                      :use (:instance coordinate-plans-valid-plan-map-p
                                                      (plan-map (get-plans-from-drones drn-sts))
                                                      (drn-sts drn-sts))))))
  :guard-hints (("Goal" :in-theory (disable return-type-of-get-plans-from-drones
                                            coordinate-plans-valid-plan-map-p
                                            get-plans-from-drones)
                 :use ((:instance return-type-of-get-plans-from-drones)
                       (:instance coordinate-plans-valid-plan-map-p
                                  (plan-map (get-plans-from-drones drn-sts))))))
  (if (mbt (coord-state-p coord-st))
      (let* ((plan-map (get-plans-from-drones drn-sts))
             (coord-plan-map (coordinate-plans plan-map coord-st)))
        (drones-choose-and-execute-plans coord-plan-map drn-sts coord-st))
    (mv drn-sts coord-st)))

(define run-coordinator-until-done ((drn-sts good-dr-state-list-p)
                                    (coord-st coord-state-p)
                                    (n natp))
  (declare (xargs :measure (nfix n)))
  :returns (mv (drn-sts-new good-dr-state-list-p :hyp (good-dr-state-list-p drn-sts))
               (coord-st-new coord-state-p :hyp (coord-state-p coord-st)))
  :guard-hints (("Goal" :in-theory (disable run-coordinator-1)))
  (if (zp n)
      (mv drn-sts coord-st)
    (if (null (set-difference-equal (dgraph->nodes (coord-state->dgraph coord-st))
                                    (coord-state->visited-nodes coord-st)))
        (mv drn-sts coord-st)
      (prog2$ (cw "~%")
              (mv-let (drn-sts-new coord-st-new)
                  (run-coordinator-1 drn-sts coord-st)
                (run-coordinator-until-done drn-sts-new coord-st-new (- n 1)))))))

(define run-drone-system ((dr-ids drone-id-list-p) (g wf-dgraph-p))
  :guard (and (consp dr-ids)
              (no-duplicatesp-equal dr-ids)
              (consp (dgraph->nodes g)))
  (if (mbt (and (drone-id-list-p dr-ids)
                (wf-dgraph-p g)))
      (let ((ign (cw "~%")))
        (declare (ignore ign))
        (mv-let (drn-sts coord-st)
            (initial-assign dr-ids g)
          (mv-let (final-drn-sts final-coord-st)
              (run-coordinator-until-done drn-sts coord-st (len (dgraph->nodes g)))
            (declare (ignore final-coord-st))
            (let ((result-map (dr-state-path-map final-drn-sts)))
              (prog2$ (print-plan-stats result-map)
                      result-map)))))
    nil))
