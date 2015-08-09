(in-package "ACL2")

#|

  stutter1-match.lisp
  ~~~~~~~~~~~~~~~~~~~

In this book we prove two of the basic theorems for bisimulation of the two
systems, viz., the implementation system, and the spec.

The theorems tell us that the next state of the implementation either matches
with the next state of the spec, or with the the current state of the spec,
under the invariants. For simplification of our reasoning, we use the
simplified condition suff rather than the full-blown condition inv, and later
prove in a separate book that inv implies suff.

|#

(include-book "programs")
(include-book "properties")

;; BEGIN Proof of >>-stutter1


(local
(defthm map-status-update-reduction
  (implies (uniquep keys)
           (equal (map-status keys (-> r a v))
                  (if (memberp a keys)
                      (-> (map-status keys r) a
                          (-> () :status (status v)))
                    (map-status keys r)))))
)


(local
(defthm map-status-access-reduction
  (implies (uniquep keys)
           (equal (<- (map-status keys r) a)
                  (if (memberp a keys)
                      (-> () :status (status (<- r a)))
                    nil))))
)


(DEFTHM >>-stutter1-b-c
  (implies (and (suff-b-c st in)
                (not (commit-b-c st in)))
           (equal (rep-b-c (bake+ st in))
                  (rep-b-c st)))
  :rule-classes nil)

(DEFTHM >>-fair-stutter1-b-c
  (implies (and (fair-suff-b-c st X)
                (not (commit-b-c st (fair-select (env st) X))))
           (equal (rep-b-c (fair-bake+ st X))
                  (rep-b-c st)))
  :rule-classes nil)


(DEFTHM >>-stutter1-c-s
  (implies (and (suff-c-s st in)
                (not (commit-c-s st in)))
              (equal (rep-c-s (cent st in))
                  (rep-c-s st)))
  :rule-classes nil)


;; BEGIN Proof of >>-match

(local
(defthm map-status-update-covers
  (equal (-> (map-status (insert a keys) r) a v)
         (-> (map-status keys r) a v))
  :hints (("Subgoal *1/2.2'"
           :use ((:instance s-diff-s
                            (b a)
                            (y v)
                            (a (car keys))
                            (x (s :status (g :status (g (car keys) r)) nil))
                            (r (map-status (insert a (cdr keys)) r)))
                 (:instance s-diff-s
                            (b a)
                            (y v)
                            (a (car keys))
                            (x (s :status (g :status (g (car keys) r)) nil))
                            (r (map-status (cdr keys) r))))
           :in-theory (disable s-diff-s))))
)

(DEFTHM >>-match-b-c
  (implies (and (suff-b-c st in)
                (commit-b-c st in))
           (equal (rep-b-c (bake+ st in))
                  (cent (rep-b-c st) (pick-b-c st in))))
  :rule-classes nil)

(DEFTHM >>-fair-match-b-c
  (implies (and (fair-suff-b-c st X)
                (commit-b-c st (fair-select (env st) X)))
           (equal (rep-b-c (fair-bake+ st X))
                  (cent (rep-b-c st)
                        (fair-pick-b-c st X))))
  :rule-classes nil)

(DEFTHM match-c-s
  (implies (and (suff-c-s st in)
                (legal st in)
                (commit-c-s st in))
           (equal (rep-c-s (cent st in))
                  (spec (rep-c-s st) in)))
  :rule-classes nil)
