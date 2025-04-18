; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book provides a generic way to do proof by epsilon-induction (hence, by
; induction over the ordinals), in a manner that can be instantiated for
; specific purposes.  We introduce a predicate that is intended to hold on a
; set whenever it holds at all members of that set, and we prove from that
; assumption that this predicate holds on all sets.

(in-package "ZF")

(include-book "tc")

(defstub in-pred (x) t)

(defun-sk in-pred-holds-below (s)
  (forall x
    (implies (in x s)
             (in-pred x))))

(defun-sk in-pred-is-inductive ()
  (forall s
    (implies (in-pred-holds-below s)
             (in-pred s))))

(in-theory (disable in-pred-is-inductive))

; Start proof of in-pred-holds-when-inductive.

; {x \in s: ~p(x)} where p is in-pred
(zsub in-pred-complement (s)
      x                 ; x
      s                 ; s (see comment above)
      (not (in-pred x)) ; u
      )

(defthmz in-pred-holds-when-inductive-1-1-1
  (implies (and (in-pred-is-inductive)
                (not (in-pred s)))
           (in s
               (in-pred-complement (tc (singleton s)))))
  :rule-classes nil
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive-1-1
  (implies (and (in-pred-is-inductive)
                (not (in-pred s)))
           (not (equal (in-pred-complement (tc (singleton s)))
                       0)))
  :hints (("Goal" :use in-pred-holds-when-inductive-1-1-1))
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive-1
  (implies (and (in-pred-is-inductive)
                (not (in-pred s)))
           (in (min-in (in-pred-complement (tc (singleton s))))
               (in-pred-complement (tc (singleton s)))))
  :hints (("Goal" :in-theory '(min-in-1 in-pred-holds-when-inductive-1-1)))
  :rule-classes nil
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive-2
  (implies (and (in-pred-is-inductive)
                (not (in-pred s)))
           (not (in-pred (min-in (in-pred-complement (tc (singleton s)))))))
  :hints (("Goal" :use in-pred-holds-when-inductive-1))
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive-3-1
  (implies (in x (min-in (in-pred-complement (tc (singleton s)))))
           (not (in x (in-pred-complement (tc (singleton s))))))
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive-3-2-1
  (implies (and (in-pred-is-inductive)
                (not (in-pred s))
                (in x (min-in (in-pred-complement (tc (singleton s))))))
           (in x (tc (singleton s))))
  :rule-classes nil
  :hints (("Goal" :use (in-pred-holds-when-inductive-1)))
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive-3-2
  (implies (and (in-pred-is-inductive)
                (not (in-pred s))
                (in x (min-in (in-pred-complement (tc (singleton s))))))
           (in-pred x))
  :hints (("Goal" :use in-pred-holds-when-inductive-3-2-1))
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive-3-3
  (implies (and (in-pred-is-inductive)
                (not (in-pred s)))
           (in-pred-holds-below
            (min-in (in-pred-complement (tc (singleton s))))))
  :rule-classes nil
  :hints (("Goal" :restrict ((in-pred-holds-when-inductive-3-2 ((s s))))))
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive-3
  (implies (and (in-pred-is-inductive)
                (not (in-pred s)))
           (in-pred (min-in (in-pred-complement (tc (singleton s))))))
  :hints (("Goal"
           :in-theory (disable in-pred-holds-below
                               in-pred-is-inductive-necc)
           :use (in-pred-holds-when-inductive-3-3
                 (:instance
                  in-pred-is-inductive-necc
                  (s (min-in (in-pred-complement (tc (singleton s)))))))))
  :rule-classes nil
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))

(defthmz in-pred-holds-when-inductive

; Proof. Abbreviate (in-pred-is-inductive) as Ind and (in-pred x) as I(x).
; Assume Ind and ~I(s).  Let [c] = (in-pred-complement (tc {s})) and let [min]
; = (min-in [c]).  [C] is non-empty since s \in [c]; so [min] \in [c] and thus
; ~I([min]).  By definition of min-in, then for all x \in [min], x \notin [c];
; yet x \in (tc {s}), hence I(x).  Then I([min]) by Ind, a contradiction.

  (implies (in-pred-is-inductive)
           (in-pred s))
  :hints (("Goal" :use (in-pred-holds-when-inductive-2
                        in-pred-holds-when-inductive-3)))
  :props (zfc in-pred-complement$prop inverse$prop prod2$prop domain$prop
              tc-fn$prop))
