

;; Naive quartet method for distance-based tree reconstruction.
;; Input is the distance matrix (a list of n lists of n naturals).
;; The output is a rooted tree.  See the toy examples at bottom.

(in-package "ACL2")


(defun quartet-p (x)
  (declare (xargs :guard t))
  (case-match x
    (((a b) (c d))
     (and (natp a) (natp b) (natp c) (natp d)))))

(defun pair-p (x)
  (declare (xargs :guard t))
  (case-match x
    ((a b)
     (and (natp a) (natp b)))))

(defun quartet-list-p (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (quartet-p (car x))
         (quartet-list-p (cdr x)))))

; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
; definition.
(defun nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))

(defthm nat-listp-true-listp
  (implies (nat-listp x)
           (true-listp x))
  :rule-classes (:rewrite :compound-recognizer))

(defun dist-matrix-helper (M n)
  (declare (xargs :guard (natp n)))
  (if (atom M)
      (equal M nil)
    (and (nat-listp (car M))
         (= (len (car M)) n)
         (dist-matrix-helper (cdr M) n))))

(defun dist-matrix-p (M)
  (declare (xargs :guard t))
  (dist-matrix-helper M (len M)))

(defun indexp (n max)
  (declare (xargs :guard (natp max)))
  (and (natp n)
       (< n max)))

(defthm indexp-bounds
  (implies (indexp n max)
           (and (<= 0 n)
                (< n max)))
  :rule-classes (:rewrite :forward-chaining))

(defthm indexp-type
  (implies (indexp x max)
           (and (integerp x)
                (<= 0 x)))
  :rule-classes (:rewrite :forward-chaining))


(defthm nat-list-p-nth-dist
  (implies (and (dist-matrix-helper M n)
                (indexp j (len M)))
           (nat-listp (nth j M))))

(defthm len-nth-dist
  (implies (and (dist-matrix-helper M n)
                (indexp j (len M)))
           (= (len (nth j M)) n)))

(defthm natp-nth-nat-list
  (implies (and (nat-listp x)
                (indexp j (len x)))
           (natp (nth j x))))

(defthm indexp-incr
  (implies (and (indexp i m)
                (natp n)
                (< i (- m n)))
           (indexp (+ n i) m)))

(in-theory (disable indexp))

(defun get-distance (M i j)
  (declare (xargs :guard (and (dist-matrix-p M)
                              (indexp i (len M))
                              (indexp j (len M)))))
  (nth j (nth i M)))

(defthm get-distance-natp
  (implies (and (dist-matrix-p M)
                (indexp i (len M))
                (indexp j (len M)))
           (natp (get-distance M i j)))
  :rule-classes (:rewrite :type-prescription))


(in-theory (disable get-distance))

(defun quartet-guard (M i j k l)
  (declare (xargs :guard t))
  (and (dist-matrix-p M)
       (let ((n (len M)))
         (and (indexp i n)
              (indexp j n)
              (indexp k n)
              (indexp l n)
              (no-duplicatesp (list i j k l))))))

(defun get-quartet (M i j k l)
  (declare (xargs :guard (quartet-guard M i j k l)))
  (let ((sum1 (+ (get-distance M i j)
                 (get-distance M k l)))
        (sum2 (+ (get-distance M i k)
                 (get-distance M j l)))
        (sum3 (+ (get-distance M i l)
                 (get-distance M j k))))
    (if (< sum1 sum2)
        (if (< sum1 sum3)
            `((,i ,j) (,k ,l))
          `((,i ,l) (,j ,k)))
      (if (< sum2 sum3)
          `((,i ,k) (,j ,l))
        `((,i ,l) (,j ,k))))))

(defthm quartet-p-get-quartet
  (implies (quartet-guard M i j k l)
           (quartet-p (get-quartet M i j k l))))

(defun get-quartets (M i j k l)
  (declare (xargs :guard (and (quartet-guard M i j k l)
                              (< i j)
                              (< j k)
                              (< k l))

            :measure (if (quartet-guard M i j k l)
                               (let ((n (len M)))
                                 (make-ord
                                  4 (- n i)
                                  (make-ord
                                   3 (- n j)
                                   (make-ord
                                    2 (- n k)
                                    (make-ord
                                     1 (- n l)
                                     0)))))
                             0)))
        (let ((maxidx (1- (len M)))
              (q (get-quartet M i j k l)))
          (if (mbt (quartet-guard M i j k l))

              (cond ((< l maxidx)
                     (cons q (get-quartets M i j k (1+ l))))
                    ((< k (1- l))
                     (cons q (get-quartets M i j (1+ k) (+ 2 k))))
                    ((< j (1- k))
                     (cons q (get-quartets M i (1+ j) (+ 2 j) (+ 3 j))))
                    ((< i (1- j))
                     (cons q (get-quartets M (1+ i) (+ 2 i) (+ 3 i) (+ 4 i))))
                    (t (list q)))
            nil)))

(defthm quartet-listp-get-quartets
  (implies (and (quartet-guard M i j k l)
                (< i j) (< j k) (< k l))
           (quartet-list-p (get-quartets M i j k l))))

(defun quartet-member (i quartet)
  (declare (xargs :guard (quartet-p quartet)))
  (or (member i (car quartet))
      (member i (cadr quartet))))

(defun quartets-member (i quartets)
  (declare (xargs :guard (quartet-list-p quartets)))
  (if (atom quartets)
      nil
    (or (quartet-member i (car quartets))
        (quartets-member i (cdr quartets)))))

(defun check-sibling (pair quartet)
  (declare (xargs :guard (and (pair-p pair)
                              (quartet-p quartet))))
  (let ((i (car pair))
        (j (cadr pair)))
    (and (not (and (member i (car quartet))
                   (member j (cadr quartet))))
         (not (and (member i (cadr quartet))
                   (member j (car quartet)))))))

(defun check-siblings (pair quartets)
  (declare (xargs :guard (and (pair-p pair)
                              (quartet-list-p quartets))))
  (if (atom quartets)
      t
    (and (check-sibling pair (car quartets))
         (check-siblings pair (cdr quartets)))))

(defun maybe-pair-and-quartet-listp (x)
  (declare (xargs :guard t))
  (or (equal x nil)
      (and (consp x)
           (or (quartet-p (car x))
               (let ((carx (car x)))
                 (case-match carx
                   (((a b))
                    (and (natp a) (natp b))))))
           (quartet-list-p (cdr x)))))

(defthm mpql-quartet-listp
  (implies (quartet-list-p x)
           (maybe-pair-and-quartet-listp x)))

(defun find-siblings (quartets rest)
  (declare (xargs :measure (make-ord
                            2 (1+ (len rest))
                            (make-ord
                             1 (1+ (len (car rest)))
                             0))
                  :guard (and (quartet-list-p quartets)
                              (maybe-pair-and-quartet-listp rest))))
  (if (consp rest)
      (let ((pair (caar rest)))
        (if (check-siblings pair quartets)
            pair
          (if (<= (len (car rest)) 1)
              (find-siblings quartets (cdr rest))
            (find-siblings quartets (cons (cdar rest) (cdr rest))))))
    nil))

(defthm find-siblings-quartets-member
  (implies (and (find-siblings quartets rest-of-quartets)
                (quartet-list-p quartets)
                (maybe-pair-and-quartet-listp rest-of-quartets))
           (and (quartets-member (car (find-siblings quartets
                                                     rest-of-quartets))
                                 rest-of-quartets)
                (quartets-member (cadr (find-siblings quartets
                                                     rest-of-quartets))
                                 rest-of-quartets)))
  :rule-classes (:rewrite :forward-chaining))

(defthm find-siblings-consp
  (implies (and (quartet-list-p quartets)
                (maybe-pair-and-quartet-listp rest)
                (find-siblings quartets rest))
           (and (consp (find-siblings quartets rest))
                (consp (cdr (find-siblings quartets rest))))))

(defthm find-siblings-eqlablep
  (implies (and (quartet-list-p quartets)
                (maybe-pair-and-quartet-listp rest)
                (find-siblings quartets rest))
           (and (eqlablep (car (find-siblings quartets rest)))
                (eqlablep (cadr (find-siblings quartets rest))))))

(defun remove-from-quartets (i quartets)
  (declare (xargs :guard (quartet-list-p quartets)))
  (if (atom quartets)
      nil
    (if (quartet-member i (car quartets))
        (remove-from-quartets i (cdr quartets))
      (cons (car quartets)
            (remove-from-quartets i (cdr quartets))))))

(defthm remove-from-quartets-measure
  (implies (quartets-member i quartets)
           (< (len (remove-from-quartets i quartets))
              (len quartets)))
  :hints (("Goal" :induct (remove-from-quartets i quartets)))
  :rule-classes (:linear :rewrite))

(defthm remove-from-quartets-quartet-list
  (implies (quartet-list-p quartets)
           (quartet-list-p (remove-from-quartets i quartets))))

(defun add-sibling (curr new tree flg)
  (declare (xargs :measure
                  (if flg
                      (+ 1 (* 2 (acl2-count tree)))
                    (* 2 (acl2-count tree)))
                  :guard (eqlablep curr)))
  (if flg
      (if (atom tree)
          (if (eql tree curr)
              (list curr new)
            tree)
        (add-sibling curr new tree nil))
    (if (atom tree)
        nil
      (cons (add-sibling curr new (car tree) t)
            (add-sibling curr new (cdr tree) nil)))))

(defun naive-quartet-recursion (taxa quartets)
  (declare (xargs :measure (len quartets)
                  :guard (and (quartet-list-p quartets)
                              (true-listp taxa))))
  (if (atom quartets)
      taxa
    (if (mbt (quartet-list-p quartets))
        (let* ((siblings (find-siblings quartets quartets)))
          (if siblings
              (let* ((quartets (remove-from-quartets (car siblings) quartets))
                     (taxa (remove (car siblings) taxa))
                 (tree (naive-quartet-recursion taxa quartets)))
                (add-sibling (cadr siblings) (car siblings) tree t))
            taxa))
      nil)))



(defun list-up-to-n-helper (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons (1- n) (list-up-to-n-helper (1- n)))))

(defun list-up-to-n (n)
  (declare (xargs :guard (natp n)))
  (reverse (list-up-to-n-helper n)))

(defthm true-listp-revappend
  (implies (true-listp end)
           (true-listp (revappend beg end))))

(defun naive-quartet-method (M)
  (declare (xargs :guard (and (dist-matrix-p M)
                              (<= 4 (len M)))
                  :guard-hints (("Goal" :in-theory (enable indexp)))))
  (let* ((n (len M))
         (taxa (list-up-to-n n))
         (quartets (get-quartets M 0 1 2 3)))
    (naive-quartet-recursion taxa quartets)))


;; 0             2
;;  \3         1/
;;   \  2   3  /
;;    x---+---x
;;   /    |    \
;;  /2   1|    3\
;; 1      4      3

(defthm nqm-test
 (equal (let ((M
               '(( 0  5 9 11 6)
                 ( 5  0 8 10 5)
                 ( 9  8 0  4 5)
                 (11 10 4  0 7)
                 ( 6  5 5  7 0))))
          (naive-quartet-method  M))
        '(2 3 (4 (1 0)))))

;;            x
;;           /|\
;;          / | \
;;         2  3  x
;;               |\
;;               | \
;;               4  x
;;                  |\
;;                  | \
;;                  1  0


;; 0      5          2
;;  \3    |3       1/
;;   \  2 | 4   3  /
;;    x---+---+---x
;;   /        |    \
;;  /2       1|    3\
;; 1          4      3


(defthm nqm-test2
 (equal (let ((M
               '(( 0  5 13 15 10  8)
                 ( 5  0 12 14  9  7)
                 (13 12  0  4  5 11)
                 (15 14  4  0  7 13)
                 (10  9  5  7  0  8)
                 ( 8  7 11 13  8  0))))
          (naive-quartet-method  M))
        '((3 2) 4 (5 (1 0)))))


;;              x
;;             /|\
;;            / | \
;;           x  4  x
;;          / \   / \
;;         3   2 5   x
;;                  / \
;;                 1   0
