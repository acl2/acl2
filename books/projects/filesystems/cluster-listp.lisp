(in-package "ACL2")

;  cluster-listp.lisp                                Mihir Mehta

; Here we define some utility functions and related lemmas for a string
; representation of FAT32 clusters.

(local (include-book "file-system-lemmas"))
(include-book "kestrel/utilities/strings/top" :dir :system)
(local (in-theory (disable make-list-ac-removal)))

;; These books were suggested by proof-by-arith.
(local (include-book "arithmetic-5/top" :dir :system))
(set-default-hints '((nonlinearp-default-hint++
                      id
                      stable-under-simplificationp hist nil)))

(defund cluster-p (cluster cluster-size)
  (declare (xargs :guard t))
  (and (stringp cluster)
       (equal (length cluster) cluster-size)))

(defthm cluster-p-of-implode
  (iff (cluster-p (implode x) cluster-size)
       (equal (len x) cluster-size))
  :hints (("goal" :in-theory (enable cluster-p))))

(defthm
  cluster-p-correctness-1
  (implies (not (stringp v))
           (not (cluster-p v cluster-size)))
  :hints (("goal" :in-theory (enable cluster-p))))

(defun cluster-listp (l cluster-size)
  (declare (xargs :guard t))
  (if
      (atom l)
      (equal l nil)
    (and (cluster-p (car l) cluster-size)
         (cluster-listp (cdr l) cluster-size))))

(defthm
  cluster-listp-of-update-nth
  (implies (cluster-listp l cluster-size)
           (equal (cluster-listp (update-nth key val l)
                                 cluster-size)
                  (and (<= (nfix key) (len l))
                       (cluster-p val cluster-size))))
  :hints (("goal" :induct (mv (update-nth key val l)
                              (cluster-listp l cluster-size))
           :in-theory (enable cluster-p update-nth))))

(defthm cluster-p-of-nth
  (implies (cluster-listp l cluster-size)
           (iff (cluster-p (nth n l) cluster-size)
                (< (nfix n) (len l))))
  :hints (("goal" :induct (nth n l)
           :in-theory (enable cluster-p nth))))

(defthm cluster-listp-of-append
  (equal (cluster-listp (append x y)
                        cluster-size)
         (and (cluster-listp (true-list-fix x)
                             cluster-size)
              (cluster-listp y cluster-size))))

(defund
  make-clusters (text cluster-size)
  (declare
   (xargs :guard (and (stringp text) (natp cluster-size))
          :measure (length text)))
  (if
      (or (zp (length text))
          (zp cluster-size))
      nil
    (list*
     (concatenate
      'string
      (subseq text 0 (min cluster-size (length text)))
      (coerce (make-list (nfix (- cluster-size (length text)))
                         :initial-element (code-char 0))
              'string))
     (make-clusters
      (subseq text (min cluster-size (length text))
              nil)
      cluster-size))))

(defthmd
  make-clusters-correctness-1
  (iff (consp (make-clusters text cluster-size))
       (and (not (zp (length text)))
            (not (zp cluster-size))))
  :hints (("goal" :in-theory (enable make-clusters)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (iff (equal (len (make-clusters text cluster-size))
                0)
         (or (zp (length text)) (zp cluster-size)))
    :hints
    (("goal"
      :expand (len (make-clusters text cluster-size)))))))

(in-theory (enable (:rewrite make-clusters-correctness-1 . 2)))

(defthm
  cluster-listp-of-make-clusters
  (implies (stringp text)
           (cluster-listp (make-clusters text cluster-size)
                          cluster-size))
  :hints
  (("goal"
    :in-theory (enable cluster-listp
                       make-clusters make-list-ac-removal)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (stringp text)
     (let ((l (make-clusters text cluster-size)))
          (implies (consp l)
                   (and (cluster-p (car l) cluster-size)
                        (cluster-listp (cdr l)
                                       cluster-size))))))))

(defthm
  make-clusters-correctness-2
  (implies (not (zp cluster-size))
           (and (>= (* cluster-size
                       (len (make-clusters text cluster-size)))
                    (length text))
                (< (* cluster-size
                      (len (make-clusters text cluster-size)))
                   (+ cluster-size (length text)))))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable make-clusters))))

(defthmd
  len-of-make-clusters
  (implies (not (zp cluster-size))
           (equal (len (make-clusters text cluster-size))
                  (ceiling (length text) cluster-size)))
  :hints (("goal" :in-theory (enable make-clusters))))

(defthm
  make-clusters-correctness-3
  (implies (and (stringp text)
                (not (zp cluster-size))
                (<= (length text) max-length)
                (equal (mod max-length cluster-size) 0))
           (<= (* cluster-size
                  (len (make-clusters text cluster-size)))
               max-length))
  :rule-classes :linear
  :hints (("goal" :in-theory (disable make-clusters-correctness-2)
           :use len-of-make-clusters)))

(defthm
  cluster-listp-of-resize-list
  (implies (and (cluster-listp lst cluster-size)
                (<= (nfix n) (len lst)))
           (cluster-listp (resize-list lst n default-value)
                          cluster-size)))
