(in-package "ACL2")

;  stobj-find-n-free-clusters.lisp                      Mihir Mehta

(include-book "update-data-region")

(defund-nx
  effective-fat (fat32$c)
  (declare
   (xargs :stobjs fat32$c
          :guard (lofat-fs-p fat32$c)
          :guard-hints
          (("goal" :in-theory (enable fat32$c-p)))))
  (take (+ (count-of-clusters fat32$c)
           *ms-first-data-cluster*)
        (nth *fati* fat32$c)))

(defthm len-of-effective-fat
  (equal (len (effective-fat fat32$c))
         (nfix (+ (count-of-clusters fat32$c)
                  *ms-first-data-cluster*)))
  :hints (("goal" :in-theory (enable effective-fat))))

(defthm
  fat32-entry-list-p-of-effective-fat
  (implies (and (fat32$c-p fat32$c)
                (<= (+ (count-of-clusters fat32$c)
                       *ms-first-data-cluster*)
                    (fat-length fat32$c)))
           (fat32-entry-list-p (effective-fat fat32$c)))
  :hints
  (("goal" :in-theory (enable effective-fat
                              fat-length fat32$c-p)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (lofat-fs-p fat32$c)
             (fat32-entry-list-p (effective-fat fat32$c))))))

(defthm
  nth-of-effective-fat
  (equal (nth n (effective-fat fat32$c))
         (if (< (nfix n)
                (nfix (+ (count-of-clusters fat32$c)
                         *ms-first-data-cluster*)))
             (fati n fat32$c)
           nil))
  :hints (("goal" :in-theory (enable fati effective-fat nth))))

(defthm
  effective-fat-of-update-data-regioni
  (equal
   (effective-fat (update-data-regioni i v fat32$c))
   (effective-fat fat32$c))
  :hints (("goal" :in-theory (enable effective-fat))))

(defthm
  effective-fat-of-update-fati
  (equal (effective-fat (update-fati i v fat32$c))
         (if (< (nfix i)
                (+ (count-of-clusters fat32$c)
                   *ms-first-data-cluster*))
             (update-nth i v (effective-fat fat32$c))
           (effective-fat fat32$c)))
  :hints (("goal" :in-theory (enable effective-fat update-fati))))

(defund
  stobj-find-n-free-clusters-helper
  (fat32$c n start)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32$c)
                (natp n)
                (natp start))
    :stobjs fat32$c
    :measure (nfix (- (+ (count-of-clusters fat32$c)
                         *ms-first-data-cluster*)
                      start))))
  (if
      (or (zp n)
          (mbe :logic (zp (- (+ (count-of-clusters fat32$c)
                                *ms-first-data-cluster*)
                             start))
               :exec (>= start
                         (+ (count-of-clusters fat32$c)
                            *ms-first-data-cluster*))))
      nil
    (if
        (not (equal (fat32-entry-mask (fati start fat32$c))
                    0))
        (stobj-find-n-free-clusters-helper
         fat32$c n (+ start 1))
      (cons
       (mbe :exec start :logic (nfix start))
       (stobj-find-n-free-clusters-helper fat32$c (- n 1)
                                          (+ start 1))))))

(defthm
  nat-listp-of-stobj-find-n-free-clusters-helper
  (nat-listp
   (stobj-find-n-free-clusters-helper fat32$c n start))
  :hints
  (("goal"
    :in-theory (enable stobj-find-n-free-clusters-helper)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (stobj-find-n-free-clusters-helper
                               fat32$c n start)))))

(defthm
  stobj-find-n-free-clusters-helper-correctness-1
  (implies
   (and (natp start)
        (lofat-fs-p fat32$c))
   (equal
    (stobj-find-n-free-clusters-helper fat32$c n start)
    (find-n-free-clusters-helper
     (nthcdr start (effective-fat fat32$c))
     n start)))
  :hints
  (("goal" :in-theory (enable stobj-find-n-free-clusters-helper
                              find-n-free-clusters-helper)
    :induct (stobj-find-n-free-clusters-helper
             fat32$c n start))))

(defund
  stobj-find-n-free-clusters
  (fat32$c n)
  (declare
   (xargs :guard (and (lofat-fs-p fat32$c)
                      (natp n))
          :stobjs fat32$c))
  (stobj-find-n-free-clusters-helper
   fat32$c n *ms-first-data-cluster*))

(defthm
  nat-listp-of-stobj-find-n-free-clusters
  (nat-listp (stobj-find-n-free-clusters fat32$c n))
  :hints
  (("goal" :in-theory (enable stobj-find-n-free-clusters)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (stobj-find-n-free-clusters-helper
                               fat32$c n start)))))

(defthm
  stobj-find-n-free-clusters-correctness-1
  (implies
   (lofat-fs-p fat32$c)
   (equal (stobj-find-n-free-clusters fat32$c n)
          (find-n-free-clusters (effective-fat fat32$c)
                                n)))
  :hints (("goal" :in-theory (enable stobj-find-n-free-clusters
                                     find-n-free-clusters)))
  :rule-classes :definition)
