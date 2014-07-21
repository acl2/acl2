(in-package "ACL2")

(defund logior1 (x)
  (declare (xargs :guard t))
  (if (equal x 0) 0 1))

(defthm logior1-logior1
  (equal (logior1 (logior1 x))
         (logior1 x))
  :hints (("Goal" :in-theory (enable logior1))))

(defthm logior1-equal-0
  (equal (equal (logior1 x) 0)
         (equal x 0))
  :hints (("goal" :in-theory (enable logior1))))

(defthm logior1-equal-1
  (equal (equal (logior1 x)
                1)
         (not (equal x 0)))
  :hints (("goal" :in-theory (enable logior1))))