(in-package "ACL2")

(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)

(defund bv-add (x y)
  (mod (+ (nfix x) (nfix y)) 32))

(defun bv-add-lex-< (x y)
  (lexorder x y))

(defund bv-add (x y)
  (mod (+ (nfix x) (nfix y)) 32))

(defun bv-add-lex-< (x y)
  (lexorder x y))

(defthm bv-commute
  (implies
   (and (syntaxp (not (bv-add-lex-< x y))))
   (equal (bv-add x y)
          (bv-add y x)))
  :hints (("Goal" :in-theory (enable bv-add))))

(defthm bv-commute-2
  (implies
   (syntaxp (not (bv-add-lex-< x y)))
   (equal (bv-add x (bv-add y z))
          (bv-add y (bv-add x z))))
  :hints (("Goal" :in-theory (enable bv-add))))
