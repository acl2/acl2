(in-package "ACL2")

(include-book "defexec/other-apps/records/records" :dir :system)
(defmacro g (a r) `(mget ,a ,r))
(defmacro s (a v r) `(mset ,a ,v ,r))

(encapsulate
 ((step-generic (in) t)
  (prop-generic (n in) t))

 (local (defun step-generic (in)
          in))

 (local (defun prop-generic (n in)
          (declare (ignore n in))
          t))

 (defthm prop-generic-step
   (implies (and (natp n)
                 (natp (g :lc in))
                 (< (g :lc in) n)
                 (prop-generic n in))
            (prop-generic n (s :lc (1+ (g :lc in))
                               (step-generic in))))))

(defun loop-generic (n in)
  (declare (xargs :measure (nfix (- n (g :lc in)))))
  (cond ((or (not (natp n))
             (not (natp (g :lc in)))
             (>= (g :lc in) n))
         in)
        (t (loop-generic n
                         (s :lc (1+ (g :lc in))
                            (step-generic in))))))

(local
 (defthm prop-generic-step-better
   (implies (and (natp n)
                 (natp (g :lc in))
                 (< (g :lc in) n)
                 (prop-generic n in)
                 (equal x (1+ (g :lc in))))
            (prop-generic n (s :lc x
                               (step-generic in))))))

(defthm loop-generic-thm
  (implies (and (natp n)
                (natp (g :lc in))
                (prop-generic n in))
           (prop-generic n (loop-generic n in)))
  :hints (("Goal" :induct t)))

(defthm loop-generic-lc
  (implies (and (natp n)
                (natp (g :lc in))
                (<= (g :lc in) n))
           (equal (g :lc (loop-generic n in))
                  n)))
