

(in-package "ACL2")

(include-book "test-help" :ttags (sat sat-cl))

(defun member-n (n a x)
  (cond
   ((zp n)
    nil)
   ((equal a (car x))
    t)
   (t
    (member-n (1- n) a (cdr x)))))

(defun duplicatesp (row-n x)
  (cond
   ((zp row-n)
    nil)
   ((member-n (1- row-n) (car x) (cdr x))
    t)
   (t
    (duplicatesp (1- row-n) (cdr x)))))

(defun good-rowsp (row-num x)
  (cond
   ((zp row-num)
    t)
   ((duplicatesp 9 (car x))
    nil)
   (t
    (good-rowsp (1- row-num) (cdr x)))))

(defun make-column (col-num n x)
  (cond
   ((zp n)
    nil)
   (t
    (cons (nth col-num (car x))
          (make-column col-num (1- n) (cdr x))))))

(defun good-columnsp (col-num x)
  (cond
   ((zp col-num)
    t)
   ((duplicatesp 9 (make-column (1- col-num) 9 x))
    nil)
   (t
    (good-columnsp (1- col-num) x))))

(defun make-cell (cell-num element-num x)
  (cond
   ((zp element-num)
    nil)
   (t
    (cons (nth (+ (mod (1- element-num) 3)
                  (* 3 (mod cell-num 3)))
               (nth (+ (floor (1- element-num) 3)
                       (* 3 (floor cell-num 3)))
                    x))
          (make-cell cell-num (1- element-num) x)))))

(defun good-cellsp (cell-num x)
  (cond
   ((zp cell-num)
    t)
   ((duplicatesp 9 (make-cell (1- cell-num) 9 x))
    nil)
   (t
    (good-cellsp (1- cell-num) x))))

(defun valid-numbers-rowp (n x)
  (cond
   ((zp n)
    t)
   ((not (or (equal (car x) 1)
             (equal (car x) 2)
             (equal (car x) 3)
             (equal (car x) 4)
             (equal (car x) 5)
             (equal (car x) 6)
             (equal (car x) 7)
             (equal (car x) 8)
             (equal (car x) 9)))
    nil)
   (t
    (valid-numbers-rowp (1- n) (cdr x)))))

(defun valid-numbersp (row-n x)
  (cond
   ((zp row-n)
    t)
   ((not (valid-numbers-rowp 9 (car x)))
    nil)
   (t
    (valid-numbersp (1- row-n) (cdr x)))))

(defconst *test-struct*
  '(( 1  2  3  4  5  6  7  8  9)
    (11 12 13 14 15 16 17 18 19)
    (21 22 23 24 25 26 27 28 29)
    (31 32 33 34 35 36 37 38 39)
    (41 42 43 44 45 46 47 48 49)
    (51 52 53 54 55 56 57 58 59)
    (61 62 63 64 65 66 67 68 69)
    (71 72 73 74 75 76 77 78 79)
    (81 82 83 84 85 86 87 88 89)
    (91 92 93 94 95 96 97 98 99)))

(defun good-solutionp (x)
  (and (valid-numbersp 9 x)
       (good-rowsp 9 x)
       (good-columnsp 9 x)
       (good-cellsp 9 x)))

(defun satisfies-constraints-rowp (constraints x)
  (cond
   ((endp constraints)
    t)
   ((eq (car constraints) 'X)
    (satisfies-constraints-rowp (cdr constraints) (cdr x)))
   ((not (eq (car constraints) (car x)))
    nil)
   (t
    (satisfies-constraints-rowp (cdr constraints) (cdr x)))))

(defun satisfies-constraintsp (constraints x)
  (cond
   ((endp constraints)
    t)
   ((not (satisfies-constraints-rowp (car constraints) (car x)))
    nil)
   (t
    (satisfies-constraintsp (cdr constraints) (cdr x)))))

(defconst *puzzle-X*
  '((X X X X X X X X X)
    (X X X X X X X X X)
    (X X X X X X X X X)
    (X X X X X X X X X)
    (X X X X X X X X X)
    (X X X X X X X X X)
    (X X X X X X X X X)
    (X X X X X X X X X)
    (X X X X X X X X X)))

(defconst *puzzle-1*
  '((X 7 X X 2 X X X X)
    (2 3 X X X 5 6 X X)
    (1 8 5 4 6 X 2 9 X)
    (X X 3 7 X X X X X)
    (4 2 X X 3 X X 8 6)
    (X X X X X 6 1 X X)
    (X 5 8 X 7 4 9 6 2)
    (X X 6 3 X X X 4 5)
    (X X X X 5 X X 1 X)))

(defconst *puzzle-hard*
  '((X X 6 4 X X 7 X X)
    (9 8 X X X X 3 X X)
    (X X X 8 2 X X X X)
    (X X X 6 X 2 5 X X)
    (3 X X X 5 X X X 6)
    (X X 1 7 X 8 X X X)
    (X X X X 1 5 X X X)
    (X X 2 X X X X 4 8)
    (X X 3 X X 4 1 X X)))

;; Note: thm-sat-invalid is a simple make-event macro defined
;; in test-help, which allows the book to certify as long as
;; the conjecture is NOT a theorem when given to the
;; sat solver.
(thm-sat-invalid
 (implies (satisfies-constraintsp *puzzle-X* x)
          (not (good-solutionp x))))

(thm-sat-invalid
 (implies (satisfies-constraintsp *puzzle-1* x)
          (not (good-solutionp x))))

(thm-sat-invalid
 (implies (satisfies-constraintsp *puzzle-hard* x)
          (not (good-solutionp x))))
