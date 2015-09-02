(in-package "ACL2")

(include-book "de4")

(defconst
  *counter-netlist*
  '((four-bit-counter
     (incr reset-)
     (out0 out1 out2 out3)
     (h0 h1 h2 h3)
     ((h0 (out0 carry0) one-bit-counter (incr   reset-))
      (h1 (out1 carry1) one-bit-counter (carry0 reset-))
      (h2 (out2 carry2) one-bit-counter (carry1 reset-))
      (h3 (out3 carry3) one-bit-counter (carry2 reset-))))

    (one-bit-counter
     (carry-in reset-)
     (out carry)
     (r0)
     ((r0 (out)          ff         (sum-reset))
      (r1 (sum carry)    half-adder (carry-in out))
      (r2 (sum-reset)    and        (sum reset-))))

    (three-bit-adder
     (c a0 a1 a2 b0 b1 b2)
     (sum0 sum1 sum2 carry)
     ()
     ((m0 (sum0 carry1) full-adder (a0 b0 c))
      (m1 (sum1 carry2) full-adder (a1 b1 carry1))
      (m1 (sum2 carry)  full-adder (a2 b2 carry2))))

    (full-adder
     (c a b)
     (sum carry)
     ()
     ((t0 (sum1 carry1) half-adder (a b))
      (t1 (sum  carry2) half-adder (sum1 c))
      (t2 (carry)       or         (carry1 carry2))))

    (half-adder
     (a b)
     (sum carry)
     ()
     ((g0 (sum)   xor (a b))
      (g1 (carry) and (a b))))
    ))


(defthm half-adder-ok
  (implies (and (equal (assoc-eq 'half-adder netlist)
                       '(half-adder (a b)
                                    (sum carry)
                                    ()
                                    ((g0 (sum)   xor (a b))
                                     (g1 (carry) and (a b)))))
                (booleanp a)
                (booleanp b))
           (equal (se 'half-adder (list a b) nil netlist)
                  (list (xor a b)
                        (and a b))))
    :hints (("Goal" :in-theory (enable md-accessors-defuns
                                       occ-accessors-defuns
                                       se-open
                                       se-occ-open
                                       ))))

;;;  The proof below makes use of the lemma above.

(defthm full-adder-ok
  (implies (and (equal (assoc-eq 'half-adder
                                 (delete-eq-module 'full-adder netlist))
                       '(half-adder (a b)
                                    (sum carry)
                                    ()
                                    ((g0 (sum)   xor (a b))
                                     (g1 (carry) and (a b)))))
                (equal (assoc-eq 'full-adder netlist)
                       '(full-adder
                         (c a b)
                         (sum carry)
                         ()
                         ((t0 (sum1 carry1) half-adder (a b))
                          (t1 (sum  carry2) half-adder (sum1 c))
                          (t2 (carry)       or         (carry1 carry2)))))
                (booleanp a)
                (booleanp b)
                (booleanp c)
;                (equal netlist *counter-netlist*)
                )
           (equal (se 'full-adder (list c a b) nil netlist)
                  (list (xor c (xor a b))
                        (if c (or a b) (and a b)))))
    :hints (("Goal" :in-theory (enable md-accessors-defuns
                                       occ-accessors-defuns
                                       se-open
                                       se-occ-open
                                       ))))

(defun v-adder (c a-vec b-vec)
  (declare (xargs :guard (and (booleanp c)
                              (boolean-listp a-vec)
                              (boolean-listp b-vec)
                              (= (len a-vec) (len b-vec)))))
  (if (atom a-vec)
      (list (b-fix c))
    (let ((a (car a-vec))
          (b (car b-vec)))
      (cons (xor c (xor a b))
            (v-adder (if c (or a b) (and a b))
                     (cdr a-vec)
                     (cdr b-vec))))))

(defthm v-adder-open
  (and (implies (atom a-vec)
                (equal (v-adder c a-vec b-vec)
                       (list (b-fix c))))
       (implies (consp a-vec)
                (equal (v-adder c a-vec b-vec)
                       (let ((a (car a-vec))
                             (b (car b-vec)))
                         (cons (xor c (xor a b))
                               (v-adder (if c (or a b) (and a b))
                                        (cdr a-vec)
                                        (cdr b-vec))))))))

(defthm three-bit-adder-ok
  (implies (and (equal netlist *counter-netlist*)
                (booleanp c)
                (boolean-listp (list a0 a1 a2))
                (boolean-listp (list b0 b1 b2)))
           (equal (se 'three-bit-adder (list c a0 a1 a2 b0 b1 b2) nil netlist)
                  (v-adder c (list a0 a1 a2) (list b0 b1 b2))))
  :hints (("Goal" :in-theory (enable md-accessors-defuns
                                       occ-accessors-defuns
                                       se-open
                                       se-occ-open
                                       ))))
