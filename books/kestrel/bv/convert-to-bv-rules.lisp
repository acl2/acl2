; Trim-based rules to convert functions to BV functions
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "trim")
(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "bvplus")
(include-book "bvnot")
(include-book "bv-syntax")
(local (include-book "logxor-b"))
(local (include-book "logior-b"))

;; These rules do step 1 of the conversion by inserting calls of trim.
;; Axe will need to have its own version of the rules, since they use syntaxp.

;; TODO: Add more of these

(defthmd bvplus-convert-arg2-to-bv
  (implies (syntaxp (and (consp x)
                         (member-eq (ffn-symb x) *functions-convertible-to-bv*)))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-convert-arg3-to-bv
  (implies (syntaxp (and (consp y)
                         (member-eq (ffn-symb y) *functions-convertible-to-bv*)))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;; These rules finish the job after other rules introduce trim.

;; TODO: Add more of these

(defthmd trim-of-logand-becomes-bvand
  (equal (trim size (logand x y))
         (bvand size x y))
  :hints (("Goal" :in-theory (enable trim bvand))))

(defthmd trim-of-logior-becomes-bvor
  (equal (trim size (logior x y))
         (bvor size x y))
  :hints (("Goal" :in-theory (enable trim bvor))))

(defthmd trim-of-logxor-becomes-bvxor
  (equal (trim size (logxor x y))
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable trim bvxor))))

(defthmd trim-of-lognot-becomes-bvnot
  (equal (trim size (lognot x))
         (bvnot size x))
  :hints (("Goal" :in-theory (enable trim bvnot))))

(defthmd trim-of-+-becomes-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (trim size (+ x y))
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable trim bvplus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;todo: or use a trim-like scheme for stuff like this
(defthm bvand-of-lognot-arg2
  (equal (bvand size (lognot x) y)
         (bvand size (bvnot size x) y))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvand-of-lognot-arg3
  (equal (bvand size x (lognot y))
         (bvand size x (bvnot size y)))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvxor-of-lognot-arg2
  (equal (bvxor size (lognot x) y)
         (bvxor size (bvnot size x) y))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvxor-of-lognot-arg3
  (equal (bvxor size x (lognot y))
         (bvxor size x (bvnot size y)))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvchop-of-lognot
  (equal (bvchop size (lognot x))
         (bvnot size x))
  :hints (("Goal" :in-theory (enable bvnot))))
