(in-package "ACL2")

;Perhaps we want to keep LOGIOR1 enabled, but if not here are some rules about it...  More are in logs.lisp
;(more those here?).

(local (include-book "../support/support/logior1"))

(defund logior1 (x)
  (declare (xargs :guard t))
  (if (equal x 0) 0 1))

(defthm logior1-logior1
  (equal (logior1 (logior1 x))
         (logior1 x)))

(defthm logior1-equal-0
  (equal (equal (logior1 x) 0)
         (equal x 0)))

(defthm logior1-equal-1
  (equal (equal (logior1 x) 1)
         (not (equal x 0))))