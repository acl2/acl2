; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "dedekind")

(local (in-theory (enable drp)))

(defun-sk dr-sum-p (r dr1 dr2)
  (exists (r1 r2)
    (and (in r1 dr1)
         (in r2 dr2)
         (equal r (+ r1 r2)))))

; Best to disable defun-sk functions:
(in-theory (disable dr-sum-p))

(zsub dr+ (dr1 dr2)
      r
      (rationals)
      (dr-sum-p r dr1 dr2))

(extend-zfc-table dr-sum-prop
                  dr-prop0 dr+$prop)

(defthmz drp-dr+-1
  (implies (and (rational-setp dr1)
                (rational-setp dr2))
           (rational-setp (dr+ dr1 dr2)))
  :hints (("Goal" :expand ((rational-setp (dr+ dr1 dr2)))))
  :props (dr-sum-prop))

(defthm rational-setp-forward
  (implies (and (in r dr)
                (rational-setp dr))
           (rationalp r))
  :rule-classes :forward-chaining)

(defthm dr-sum-p-closed-downward-1
  (implies (and (rational-setp dr1)
                (dr-closed-downward dr2)
                (and (in r21 dr1)
                     (in r22 dr2)
                     (equal r2 (+ r21 r22)))
                (rationalp r1)
                (< r1 r2))
           (let ((r11 r21)
                 (r12 (- r22 (- r2 r1))))
             (and (in r11 dr1)
                  (in r12 dr2)
                  (equal r1 (+ r11 r12)))))
  :hints (("Goal" :restrict ((dr-closed-downward-necc ((y r22))))))
  :rule-classes nil)

(defthm dr-sum-p-closed-downward
  (implies (and (rational-setp dr1)
                (dr-closed-downward dr2)
                (dr-sum-p r2 dr1 dr2)
                (rationalp r1)
                (< r1 r2))
           (dr-sum-p r1 dr1 dr2))
  :hints (("Goal"
           :expand ((dr-sum-p r2 dr1 dr2))
           :use ((:instance dr-sum-p-closed-downward-1
                            (r1 r1)
                            (r2 r2)
                            (r21 (car (dr-sum-p-witness r2 dr1 dr2)))
                            (r22 (mv-nth 1 (dr-sum-p-witness r2 dr1 dr2))))))))

(defthmz drp-dr+-2
  (implies (and (rational-setp dr1)
                (dr-closed-downward dr2))
           (dr-closed-downward (dr+ dr1 dr2)))
  :hints (("Goal" :expand ((dr-closed-downward (dr+ dr1 dr2)))))
  :props (dr-sum-prop))

(defthmz dr-boundp-+-dr+-1-1
  (implies (and (rational-setp dr2)
                (dr-boundp b1 dr1)
                (dr-boundp b2 dr2)
                (equal r (+ r1 r2))
                (in r1 dr1)
                (in r2 dr2))
           (<= r (+ b1 b2)))
  :hints (("Goal"
           :in-theory (disable dr-boundp-necc)
           :use ((:instance dr-boundp-necc
                            (b b1)
                            (s dr1)
                            (y r1))
                 (:instance dr-boundp-necc
                            (b b2)
                            (s dr2)
                            (y r2)))))
  :props (dr-sum-prop))

(defthmz dr-boundp-+-dr+-1
  (implies (and (dr-sum-p r dr1 dr2)
                (rational-setp dr2)
                (dr-boundp b1 dr1)
                (dr-boundp b2 dr2))
           (<= r (+ b1 b2)))
  :hints (("Goal" :expand ((dr-sum-p r dr1 dr2))))
  :props (dr-sum-prop))

(defthmz dr-boundp-+-dr+
  (implies (and (rational-setp dr2)
                (dr-boundp b1 dr1)
                (dr-boundp b2 dr2))
           (dr-boundp (+ b1 b2) (dr+ dr1 dr2)))
  :hints (("Goal" :expand ((dr-boundp (+ b1 b2) (dr+ dr1 dr2)))))
  :props (dr-sum-prop))

(defthmz dr-bounded-above-dr+
  (implies (and (rational-setp dr2)
                (dr-bounded-above dr1)
                (dr-bounded-above dr2))
           (dr-bounded-above (dr+ dr1 dr2)))
  :hints (("Goal"
           :expand ((dr-bounded-above dr1)
                    (dr-bounded-above dr2))
           :use ((:instance dr-bounded-above-suff
                            (b (+ (dr-bound dr1)
                                  (dr-bound dr2)))
                            (s (dr+ dr1 dr2))))
           :in-theory (disable dr-bounded-above-suff)))
  :props (dr-sum-prop))

(encapsulate
  ()

  (local (defthm dr-sum-p-commutes-1
           (implies (dr-sum-p x dr2 dr1)
                    (dr-sum-p x dr1 dr2))
           :hints (("Goal" :expand ((dr-sum-p x dr2 dr1))))))

  (defthm dr-sum-p-commutes
    (equal (dr-sum-p x dr2 dr1)
           (dr-sum-p x dr1 dr2))
    :hints (("Goal" :cases ((dr-sum-p x dr2 dr1))))))

(defthmz dr-bound-p-dr+-1
  (implies (and (dr-boundp (+ b1 b2) (dr+ dr1 dr2))
                (rational-setp dr1)
                (rational-setp dr2)
                (in b2 dr2))
           (dr-boundp b1 dr1))
  :hints (("Goal"
           :expand ((dr-boundp b1 dr1))
           :use ((:instance dr-boundp-necc
                            (b (+ b1 b2))
                            (y (+ (dr-boundp-witness b1 dr1)
                                  b2))
                            (s (dr+ dr1 dr2))))
           :in-theory (disable dr-boundp-necc)))
  :props (dr-sum-prop))

(defthmz dr-bound-p-dr+
  (implies (and (dr-boundp b (dr+ dr1 dr2))
                (rational-setp dr1)
                (rational-setp dr2)
                (dr-sum-p b dr1 dr2))
           (dr-max-p dr1))
  :instructions ((:bash ("Goal" :expand ((dr-sum-p b dr1 dr2))))
                 (:rewrite dr-max-p-suff nil t)
                 (:generalize ((car (dr-sum-p-witness b dr1 dr2)) b1)
                              ((mv-nth 1 (dr-sum-p-witness b dr1 dr2))
                               b2))
                 :prove)
  :props (dr-sum-prop))

(defthmz dr-max-p-dr+
  (implies (and (rational-setp dr1)
                (rational-setp dr2)
                (dr-max-p (dr+ dr1 dr2)))
           (dr-max-p dr1))
  :hints (("Goal" :expand ((dr-max-p (dr+ dr1 dr2)))))
  :props (dr-sum-prop))

(defthmz dr+-non-empty-1
  (implies (and (not (equal dr1 0))
                (rational-setp dr1)
                (not (equal dr2 0))
                (rational-setp dr2))
           (in (+ (min-in dr1) (min-in dr2))
               (dr+ dr1 dr2)))
  :hints (("Goal" :restrict ((dr-sum-p-suff
                              ((r1 (min-in dr1))
                               (r2 (min-in dr2)))))))
  :props (dr-sum-prop)
  :rule-classes nil)

(defthmz dr+-non-empty
  (implies (and (not (equal dr1 0))
                (rational-setp dr1)
                (not (equal dr2 0))
                (rational-setp dr2))
           (not (equal (dr+ dr1 dr2) 0)))
  :hints (("Goal" :use dr+-non-empty-1))
  :props (dr-sum-prop))

(defthmz drp-dr+
  (implies (and (drp dr1)
                (drp dr2))
           (drp (dr+ dr1 dr2)))
  :hints (("Goal" :in-theory (enable drp)))
  :props (dr-sum-prop))

(defthme dr+-commutativity
  (equal (dr+ dr2 dr1)
         (dr+ dr1 dr2))
  :props (dr-sum-prop))

(defthmz dr+-associativity-1-1-1
  (implies (and (rational-setp dr1)
                (rational-setp dr2)
                (rational-setp dr3)
                (in r1 dr1)
                (in r2 dr2)
                (in r3 dr3)
                (equal r23 (+ r2 r3)))
           (dr-sum-p (+ r1 r23) dr3 (dr+ dr1 dr2)))
  :hints (("Goal"
           :use ((:instance dr-sum-p-suff
                            (r1 r3)
                            (r2 (+ r1 r2))
                            (r (+ r1 r23))
                            (dr1 dr3)
                            (dr2 (dr+ dr1 dr2))))))
  :props (dr-sum-prop))

(defthmz dr+-associativity-1-1
  (implies (and (rational-setp dr1)
                (rational-setp dr2)
                (rational-setp dr3)
                (rationalp elt)
                (in r1 dr1)
                (dr-sum-p r23 dr2 dr3)
                (equal elt (+ r1 r23)))
           (dr-sum-p elt dr3 (dr+ dr1 dr2)))
  :hints (("Goal" :expand ((dr-sum-p r23 dr2 dr3))))
  :props (dr-sum-prop))

(defthmz dr+-associativity-1
  (implies (and (rational-setp dr1)
                (rational-setp dr2)
                (rational-setp dr3)
                (rationalp elt)
                (dr-sum-p elt dr1 (dr+ dr2 dr3)))
           (dr-sum-p elt dr3 (dr+ dr1 dr2)))
  :hints (("Goal" :expand ((dr-sum-p elt dr1 (dr+ dr2 dr3)))))
  :props (dr-sum-prop))

(defthmz dr+-associativity-2-1-1
  (implies (and (rational-setp dr2)
                (rational-setp dr3)
                (in r3 dr3)
                (in r1 dr1)
                (in r2 dr2)
                (equal r12 (+ r1 r2)))
           (dr-sum-p (+ r12 r3) dr1 (dr+ dr2 dr3)))
  :hints (("Goal"
           :use ((:instance dr-sum-p-suff
                            (r1 r1)
                            (r2 (+ r2 r3))
                            (r (+ r12 r3))
                            (dr1 dr1)
                            (dr2 (dr+ dr2 dr3))))))
  :props (dr-sum-prop))

(defthmz dr+-associativity-2-1
  (implies (and (rational-setp dr2)
                (rational-setp dr3)
                (in r3 dr3)
                (rationalp r12)
                (in r12 (dr+ dr1 dr2))
                (equal elt (+ r3 r12)))
           (dr-sum-p elt dr1 (dr+ dr2 dr3)))
  :hints (("Goal" :expand ((dr-sum-p r12 dr1 dr2))))
  :props (dr-sum-prop))

(defthmz dr+-associativity-2
  (implies (and (rational-setp dr2)
                (rational-setp dr3)
                (rationalp elt)
                (dr-sum-p elt dr3 (dr+ dr1 dr2)))
           (dr-sum-p elt dr1 (dr+ dr2 dr3)))
  :hints (("Goal" :expand ((dr-sum-p elt dr3 (dr+ dr1 dr2)))))
  :props (dr-sum-prop))

(defthme dr+-associativity
  (implies (and (rational-setp dr1)
                (rational-setp dr2)
                (rational-setp dr3))
           (equal (dr+ (dr+ dr1 dr2) dr3)
                  (dr+ dr1 (dr+ dr2 dr3))))
  :props (dr-sum-prop))
