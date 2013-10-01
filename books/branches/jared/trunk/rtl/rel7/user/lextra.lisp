(in-package "ACL2")

(include-book "land")
(include-book "lior")
(include-book "lxor")
(local (include-book "../support/support/lextra0"))

;theorems mixing two or more of the new logical operators.

;BOZO really the -1 and -2 names below should be switched?

(defthmd lior0-land0-1
  (equal (lior0 x (land0 y z n) n)
         (land0 (lior0 x y n) (lior0 x z n) n)))

(defthmd lior0-land0-2
  (equal (lior0 (land0 y z n) x n)
         (land0 (lior0 x y n) (lior0 x z n) n)))

(defthmd land0-lior0-1
  (equal (land0 x (lior0 y z n) n)
         (lior0 (land0 x y n) (land0 x z n) n)))

(defthmd land0-lior0-2
  (equal (land0 (lior0 y z n) x n)
         (lior0 (land0 x y n) (land0 x z n) n)))

(defthmd lior0-land0-lxor0
  (equal (lior0 (land0 x y n) (lior0 (land0 x z n) (land0 y z n) n) n)
         (lior0 (land0 x y n) (land0 (lxor0 x y n) z n) n)))

(defthmd lxor0-rewrite
  (equal (lxor0 x y n)
         (lior0 (land0 x (lnot y n) n)
               (land0 y (lnot x n) n)
               n)))

(defthmd lnot-lxor0
  (equal (lnot (lxor0 x y n) n)
         (lxor0 (lnot x n) y n)))

;consider enabling?
(defthmd lnot-lior0
  (equal (lnot (lior0 x y n) n)
         (land0 (lnot x n) (lnot y n) n)))

;consider enabling?
(defthmd lnot-land0
  (equal (lnot (land0 x y n) n)
         (lior0 (lnot x n) (lnot y n) n)))

