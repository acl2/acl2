(in-package "ACL2")

(include-book "land0")
(include-book "lior0")
(include-book "lxor0")
(local (include-book "lextra-proofs"))

;theorems mixing two or more of the new logical operators.

;BOZO really the -1 and -2 names below should be switched?

(deflabel lextra0-start)

(defthm lior0-land0-1
  (equal (lior0 x (land0 y z n) n)
         (land0 (lior0 x y n) (lior0 x z n) n)))

(defthm lior0-land0-2
  (equal (lior0 (land0 y z n) x n)
         (land0 (lior0 x y n) (lior0 x z n) n)))

(defthm land0-lior0-1
  (equal (land0 x (lior0 y z n) n)
         (lior0 (land0 x y n) (land0 x z n) n)))

(defthm land0-lior0-2
  (equal (land0 (lior0 y z n) x n)
         (lior0 (land0 x y n) (land0 x z n) n)))

(defthm lior0-land0-lxor0
  (equal (lior0 (land0 x y n) (lior0 (land0 x z n) (land0 y z n) n) n)
         (lior0 (land0 x y n) (land0 (lxor0 x y n) z n) n)))

(defthm lxor0-rewrite
  (equal (lxor0 x y n)
         (lior0 (land0 x (lnot y n) n)
               (land0 y (lnot x n) n)
               n)))

(defthm lnot-lxor0
  (equal (lnot (lxor0 x y n) n)
         (lxor0 (lnot x n) y n)))

(defthm lnot-lior0
  (equal (lnot (lior0 x y n) n)
         (land0 (lnot x n) (lnot y n) n)))

(defthm lnot-land0
  (equal (lnot (land0 x y n) n)
         (lior0 (lnot x n) (lnot y n) n)))

(deflabel lextra0-end)

(in-theory (current-theory 'lextra0-start))
