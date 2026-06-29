; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")
(include-book "set-algebra") ; for diff

(defun-sk in-all (x s)
  (forall (y)
    (implies (in y s)
             (in x y)))
  :rewrite :direct)

(in-theory (disable in-all))

(defthmz in-all-implies-in-in
  (implies (and (not (equal s 0))
                (in-all x s))
           (in-in x s))
  :hints (("Goal" :restrict ((in-in-suff ((y (min-in s))))))))

(zsub intersection (s) ; name, args
      x                ; x
      (union s)        ; s
      (in-all x s)
      )

(defthmz intersection$comprehension-improved
  (equal (in x (intersection s))
         (and (not (equal s 0))
              (in-all x s)))
  :props (zfc intersection$prop))

; Degenerate case:

(encapsulate
  ()

  (local (defthmz subset-intersection-0-0
           (subset (intersection 0) 0)
           :hints (("Goal" :in-theory (e/d (subset) (subset-x-0))))
           :props (zfc intersection$prop)))

  (defthmz intersection-0
    (equal (intersection 0) 0)
    :hints (("Goal" :in-theory (enable extensionality)))
    :props (zfc intersection$prop)))

(in-theory (disable intersection$comprehension))

; Let's take on deMorgan's laws for intersection and union.

; Our first goal is the theorem diff-intersection, which states that the
; complement of the intersection is the union of the complements.  We start by
; definitin the set of the complements -- with respect to a universal set, u --
; as {x \in powerset(u): u\x \in s}.  This definition is suitable only if s
; \subset powerset(u).

(zsub diff-all (u ss) ; name, args
      s               ; x
      (powerset u)    ; s
      (in (diff u s) ss)
      )

(encapsulate
  ()

  (local (defthmz diff-intersection-1-1-1
           (implies (force (subset s1 s2))
                    (equal (diff s2 (diff s2 s1))
                           s1))
           :hints (("Goal"
                    :expand ((subset s1 (diff s2 (diff s2 s1))))
                    :in-theory (enable extensionality-rewrite)))
           :props (zfc diff$prop)))

  (defthmz diff-intersection-1-1
    (implies (and (subset ss (powerset u))
                  (not (equal ss 0))
                  (in x (diff u (intersection ss))))
             (in-in x (diff-all u ss)))
    :hints (("Goal"
             :in-theory (disable in-in-suff)
; Doesn't work:
;          :restrict ((in-in-suff ((y (diff u (in-all-witness x ss))))))
; So instead:
             :use ((:instance in-in-suff
                              (a x)
                              (x (diff-all u ss))
                              (y (diff u (in-all-witness x ss)))))
             :expand ((in-all x ss))))
    :props (zfc intersection$prop diff$prop diff-all$prop)))

(defthmz diff-intersection-1
  (implies (and (subset ss (powerset u))
                (not (equal ss 0)))
           (subset (diff u (intersection ss))
                   (union (diff-all u ss))))
  :hints (("Goal" :expand ((subset (diff u (intersection ss))
                                   (union (diff-all u ss))))))
  :props (zfc intersection$prop diff$prop diff-all$prop))

(defthmz diff-intersection-2-1-1
  (implies (and (subset ss (powerset u))
                (not (equal ss 0))
                (in s wit)
                (subset wit u)
                (in (diff u wit) ss))
           (not (in-all s ss)))
  :hints (("Goal"
           :in-theory (disable in-all-necc)
           :use ((:instance in-all-necc
                            (x s)
                            (s ss)
                            (y (diff u wit))))))
  :props (zfc intersection$prop diff$prop diff-all$prop))

(defthmz diff-intersection-2
  (implies (and (subset ss (powerset u))
                (not (equal ss 0)))
           (subset (union (diff-all u ss))
                   (diff u (intersection ss))))
  :hints (("Goal"
           :in-theory (enable in-in)
           :expand ((subset (union (diff-all u ss))
                            (diff u (intersection ss))))))
  :props (zfc intersection$prop diff$prop diff-all$prop))

(defthmz diff-intersection
  (implies (and (subset ss (powerset u))
                (not (equal ss 0)))
           (equal (diff u (intersection ss))
                  (union (diff-all u ss))))
  :hints (("Goal" :in-theory (enable extensionality)))
  :props (zfc intersection$prop diff$prop diff-all$prop))
