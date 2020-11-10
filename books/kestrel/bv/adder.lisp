(in-package "ACL2")

(include-book "rules")

(defun full-adder-sum (bit1 bit2 carryin)
  (bitxor bit1 (bitxor bit2 carryin)))

(defun full-adder-carry (bit1 bit2 carryin)
  (bitor (bitand bit1 bit2)
         (bitand carryin (bitxor bit1 bit2))))

;returns n+1 bits, one bit of carry followed by n bits of sum
(defund ripple-carry-adder (n
                           x y        ;these are n-bit values
                           carry-in   ;a single bit
                           )
  (if (zp n)
      carry-in ;(used to add the 1 when subtracting since A-B=A+inv(b)+1)
    (let* ((shorter-sum (ripple-carry-adder (+ -1 n) (bvchop (+ -1 n) x) (bvchop (+ -1 n) y) carry-in))
           (carryin (getbit (+ -1 n) shorter-sum)))
      (bvcat2 1 (full-adder-carry (getbit (+ -1 n) x)
                                  (getbit (+ -1 n) y)
                                  carryin)
              1 (full-adder-sum (getbit (+ -1 n) x)
                                (getbit (+ -1 n) y)
                                carryin)
              (+ -1 n) (bvchop (+ -1 n) shorter-sum)))))

(defthm ripple-carry-adder-of-zeros
  (equal (ripple-carry-adder n 0 0 0)
         0)
  :hints (("Goal" :in-theory (enable ripple-carry-adder))))

(defthm ripple-carry-adder-base
  (equal (ripple-carry-adder 0 x y carry-in)
         carry-in)
  :hints (("Goal" :in-theory (enable ripple-carry-adder))))

(defthm ripple-carry-adder-recursive
  (implies (not (zp n))
           (equal (ripple-carry-adder n x y carry-in)
                  (let* ((shorter-sum (ripple-carry-adder (+ -1 n) (bvchop (+ -1 n) x) (bvchop (+ -1 n) y) carry-in))
                         (carryin (getbit (+ -1 n) shorter-sum))
                         (sumin (bvchop (+ -1 n) shorter-sum)))
                    (bvcat2 1 (full-adder-carry (getbit (+ -1 n) x)
                                                (getbit (+ -1 n) y)
                                                carryin)
                            1 (full-adder-sum (getbit (+ -1 n) x)
                                              (getbit (+ -1 n) y)
                                              carryin)
                            (+ -1 n) sumin))))
  :hints (("Goal" :in-theory (enable ripple-carry-adder))))
