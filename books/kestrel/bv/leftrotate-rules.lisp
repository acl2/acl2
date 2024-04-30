(in-package "ACL2")

(include-book "leftrotate")
(include-book "leftrotate32")
(include-book "bvxor")
(include-book "bitxor")
(include-book "bitand")
(include-book "bitor")
(include-book "trim")
(local (include-book "bvcat-rules"))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

(defthm leftrotate-of-bvxor
  (equal (leftrotate size amt (bvxor size x y))
         (bvxor size (leftrotate size amt x)
                (leftrotate size amt y)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable leftrotate natp))))

(defthm leftrotate32-of-bvxor-32
  (equal (leftrotate32 amt (bvxor 32 x y))
         (bvxor 32 (leftrotate32 amt x)
                (leftrotate32 amt y)))
  :hints (("Goal" :in-theory (enable leftrotate32))))

;; do we need these?
(defthm bitand-of-leftrotate-arg1-trim
  (implies (syntaxp (and (quotep amt) ; so we know what bit we'll get
                         (quotep width)))
           (equal (bitand (leftrotate width amt x) y)
                  (bitand (trim 1 (leftrotate width amt x)) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bitand-of-leftrotate-arg2-trim
  (implies (syntaxp (and (quotep amt) ; so we know what bit we'll get
                         (quotep width)))
           (equal (bitand x (leftrotate width amt y))
                  (bitand x (trim 1 (leftrotate width amt y)))))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bitor-of-leftrotate-arg1-trim
  (implies (syntaxp (and (quotep amt) ; so we know what bit we'll get
                         (quotep width)))
           (equal (bitor (leftrotate width amt x) y)
                  (bitor (trim 1 (leftrotate width amt x)) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bitor-of-leftrotate-arg2-trim
  (implies (syntaxp (and (quotep amt) ; so we know what bit we'll get
                         (quotep width)))
           (equal (bitor x (leftrotate width amt y))
                  (bitor x (trim 1 (leftrotate width amt y)))))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bitxor-of-leftrotate-arg1-trim
  (implies (syntaxp (and (quotep amt) ; so we know what bit we'll get
                         (quotep width)))
           (equal (bitxor (leftrotate width amt x) y)
                  (bitxor (trim 1 (leftrotate width amt x)) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bitxor-of-leftrotate-arg2-trim
  (implies (syntaxp (and (quotep amt) ; so we know what bit we'll get
                         (quotep width)))
           (equal (bitxor x (leftrotate width amt y))
                  (bitxor x (trim 1 (leftrotate width amt y)))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: only trim leftrotate is the amt is constant?

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
