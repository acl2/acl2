(in-package "ACL2")

;  generate-index-list.lisp                            Mihir Mehta

;; If one's going to append some blocks at the end of the disk, one needs to
;; generate the indices for those blocks - that's what this function does.
(defun
  generate-index-list
  (disk-length block-list-length)
  (declare (xargs :guard (and (natp disk-length)
                              (natp block-list-length))))
  (if (zp block-list-length)
      nil
      (cons (nfix disk-length)
            (generate-index-list (1+ disk-length)
                                 (1- block-list-length)))))

(defthm
  generate-index-list-correctness-1
  (nat-listp
   (generate-index-list disk-length block-list-length)))

(defthm
  generate-index-list-correctness-2
  (equal
   (len (generate-index-list disk-length block-list-length))
   (nfix block-list-length)))

(defthm
  member-of-generate-index-list
  (iff (member-equal
        x
        (generate-index-list disk-length block-list-length))
       (or (and (equal x 0)
                (zp disk-length)
                (not (zp block-list-length)))
           (and (integerp x)
                (>= x (nfix disk-length))
                (< x
                   (nfix (+ disk-length
                            (nfix block-list-length))))))))

(defthm remove-when-absent
  (implies (not (member-equal x l))
           (equal (remove-equal x l)
                  (true-list-fix l))))

(defthm len-of-true-list-fix
  (equal (len (true-list-fix x)) (len x)))

(defthm
  generate-index-list-correctness-4
  (implies
   (and (integerp x)
        (natp disk-length)
        (>= x disk-length)
        (< x
           (+ disk-length (nfix block-list-length))))
   (equal
    (len
     (remove-equal
      x
      (generate-index-list disk-length block-list-length)))
    (- (nfix block-list-length) 1))))
