(in-package "ACL2")

(include-book "land")
(include-book "lior")
(include-book "lxor")
(local (include-book "lextra-proofs"))

;theorems mixing two or more of the new logical operators.

;BOZO really the -1 and -2 names below should be switched?

(defthmd lior-land-1
  (equal (lior x (land y z n) n)
         (land (lior x y n) (lior x z n) n)))

(defthmd lior-land-2
  (equal (lior (land y z n) x n)
         (land (lior x y n) (lior x z n) n)))

(defthmd land-lior-1
  (equal (land x (lior y z n) n)
         (lior (land x y n) (land x z n) n)))

(defthmd land-lior-2
  (equal (land (lior y z n) x n)
         (lior (land x y n) (land x z n) n)))

(defthmd lior-land-lxor
  (equal (lior (land x y n) (lior (land x z n) (land y z n) n) n)
         (lior (land x y n) (land (lxor x y n) z n) n)))

(defthmd lxor-rewrite
  (equal (lxor x y n)
         (lior (land x (lnot y n) n)
               (land y (lnot x n) n)
               n)))

(defthmd lnot-lxor
  (equal (lnot (lxor x y n) n)
         (lxor (lnot x n) y n)))

;consider enabling?
(defthmd lnot-lior
  (equal (lnot (lior x y n) n)
         (land (lnot x n) (lnot y n) n)))

;consider enabling?
(defthmd lnot-land
  (equal (lnot (land x y n) n)
         (lior (lnot x n) (lnot y n) n)))

