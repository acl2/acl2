
(in-package "ACL2")


(defun u32-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (unsigned-byte-p 32 (car x))
         (u32-listp (cdr x)))))

(defthmd nth-in-u32-listp-natp
  (implies (and (u32-listp gates)
                (< (nfix idx) (len gates)))
           (natp (nth idx gates)))
  :hints(("Goal" :in-theory (enable nth))))

(defthmd nth-in-u32-listp-u32p
  (implies (and (u32-listp gates)
                (< (nfix idx) (len gates)))
           (unsigned-byte-p 32 (nth idx gates)))
  :hints(("Goal" :in-theory (enable nth))))

(defthmd nth-in-u32-listp-integerp
  (implies (and (u32-listp gates)
                (< (nfix idx) (len gates)))
           (integerp (nth idx gates)))
  :hints(("Goal" :in-theory (enable nth))))

(defthmd nth-in-u32-listp-gte-0
  (implies (and (u32-listp gates)
                (< (nfix idx) (len gates)))
           (<= 0 (nth idx gates)))
  :hints(("Goal" :in-theory (enable nth)))
  :rule-classes :linear)

(defthmd nth-in-u32-listp-upper-bound
  (implies (and (u32-listp gates)
                (< (nfix idx) (len gates)))
           (< (nth idx gates) (expt 2 32)))
  :hints(("Goal" :in-theory (enable nth)))
  :rule-classes :linear)
