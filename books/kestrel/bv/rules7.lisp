; More BV rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat")
(include-book "bitnot")
(include-book "bitxor")
(include-book "bitand")
(include-book "bvxor")
(include-book "rotate")
(local (include-book "rules"))

(defthmd bvcat-of-bitnot-and-bitnot
  (equal (bvcat 1 (bitnot x) 1 (bitnot y))
         (bvnot 2 (bvcat 1 x 1 y))))

(defthmd bvcat-of-bvnot-and-bitnot
  (implies (posp size) ;why not 0?
           (equal (bvcat size (bvnot size x) 1 (bitnot y))
                  (bvnot (+ 1 size) (bvcat size x 1 y)))))

(defthmd bvcat-of-bitnot-and-bvnot
  (implies (posp size) ;why not 0?
           (equal (bvcat 1 (bitnot x) size (bvnot size y))
                  (bvnot (+ 1 size) (bvcat 1 x size y)))))

(defthmd bvcat-of-bvnot-and-bvnot
  (implies (and (posp highsize) ;why not 0?
                (posp lowsize) ;why not 0?
                )
           (equal (bvcat highsize (bvnot highsize highval) lowsize (bvnot lowsize lowval))
                  (bvnot (+ highsize lowsize) (bvcat highsize highval lowsize lowval)))))

;gen
(defthm bvxor-of-leftrotate-trim-8-32-arg2
  (equal (bvxor 8 x (leftrotate 32 amt y))
         (bvxor 8 x (trim 8 (leftrotate 32 amt y))))
  :hints (("Goal" :in-theory (enable trim))))

;gen
(defthm bvxor-of-leftrotate-trim-8-32-arg1
  (equal (bvxor 8 (leftrotate 32 amt y) x)
         (bvxor 8 (trim 8 (leftrotate 32 amt y)) x))
  :hints (("Goal" :in-theory (enable trim))))

;gen
(defthm bvxor-of-leftrotate32-trim-8-arg2
  (equal (bvxor 8 x (leftrotate32 amt y))
         (bvxor 8 x (trim 8 (leftrotate32 amt y))))
  :hints (("Goal" :in-theory (enable trim))))

;gen
(defthm bvxor-of-leftrotate32-trim-8-arg1
  (equal (bvxor 8 (leftrotate32 amt y) x)
         (bvxor 8 (trim 8 (leftrotate32 amt y)) x))
  :hints (("Goal" :in-theory (enable trim))))

(defthm leftrotate-32-of-bvxor-32-when-constant
  (implies (syntaxp (quotep x))
           (equal (leftrotate 32 amt (bvxor 32 x y))
                  (bvxor 32
                         (leftrotate 32 amt x)
                         (leftrotate 32 amt y))))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm leftrotate32-of-bvxor-32-when-constant
  (implies (syntaxp (quotep x))
           (equal (leftrotate32 amt (bvxor 32 x y))
                  (bvxor 32
                         (leftrotate32 amt x)
                         (leftrotate32 amt y))))
  :hints (("Goal" :in-theory (enable leftrotate32 natp))))

(defthm bvchop-of-1-when-bitp
  (implies (bitp x)
           (equal (bvchop 1 x)
                  x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;;
;; Generalize these to handle x equal to any syntactically-bitp term?
;;

(defthmd bitp-when-equal-of-getbit-1
  (implies (equal x (getbit free-n free-y))
           (bitp x)))

(defthmd bitp-when-equal-of-getbit-2
  (implies (equal (getbit free-n free-y) x)
           (bitp x)))

(defthmd bitp-when-equal-of-bitxor-1
  (implies (equal x (bitxor free-y free-z))
           (bitp x)))

(defthmd bitp-when-equal-of-bitxor-2
  (implies (equal (bitxor free-y free-z) x)
           (bitp x)))

(defthmd bitp-when-equal-of-bitand-1
  (implies (equal x (bitand free-y free-z))
           (bitp x)))

(defthmd bitp-when-equal-of-bitand-2
  (implies (equal (bitand free-y free-z) x)
           (bitp x)))

;; This can let you prove X satisfies bitp without waiting for substitution to
;; happen.
(defthmd bitp-when-equal-1
  (implies (and (equal x free)
                (bitp free))
           (bitp x)))

;; Only needed for Axe
(defthmd bitp-when-equal-2
  (implies (and (equal free x)
                (bitp free))
           (bitp x)))

;; Try these rules late, since they require searching through hyps:
(table axe-rule-priorities-table 'bitp-when-equal-of-getbit-1 1)
(table axe-rule-priorities-table 'bitp-when-equal-of-getbit-2 1)
(table axe-rule-priorities-table 'bitp-when-equal-of-bitxor-1 1)
(table axe-rule-priorities-table 'bitp-when-equal-of-bitxor-2 1)
(table axe-rule-priorities-table 'bitp-when-equal-1 1)
(table axe-rule-priorities-table 'bitp-when-equal-2 1)
