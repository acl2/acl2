
;  sra-matrix-defuns.lisp                               Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; (ld "sra-matrix-defuns.lisp" :ld-pre-eval-print t)
; (certify-book "sra-matrix-defuns" ?)

(in-package "ACL2")

(include-book "num")
(include-book "vw-eval")

; Sparse-Representation-Alist (SRA) format for sparse-matrix rows

(defun sra-rowp (a)
  (declare (xargs :guard t))
  (if (atom a)
      (null a)
    (if (atom (cdr a))
        (and (consp (car a))
             (natp (caar a))
             (null (cdr a)))
      (and (consp (car a))
           (consp (cadr a))
           (let ((key1 (caar a))
                 (key2 (caar (cdr a))))
             (and (natp key1)
                  (natp key2)
                  (< key1 key2)
                  (sra-rowp (cdr a))))))))

(defun sra-rational-row-elements-p (a)
  "Recognizes one row of a SRA (sparse) matrix."
  (declare (xargs :guard (sra-rowp a)))
  (if (atom a)
      (null a)
    (let ((pair (car a))) ;; last pair
      (and (nump (cdr pair))
           (sra-rational-row-elements-p (cdr a))))))

(defun sra-rational-rowp (a)
  (declare (xargs :guard t))
  (and (sra-rowp a)
       (sra-rational-row-elements-p a)))

(defthm sra-rational-rowp-forward-to-sra-rowp
  (implies (sra-rational-rowp row)
           (sra-rowp row))
  :rule-classes :forward-chaining)

(defun sra-nat-row-elements-p (a)
  "Recognizes one row of a SRA (sparse) matrix with natural number
   entries."
  (declare (xargs :guard (sra-rowp a)))
  (if (atom a)
      (null a)
    (let ((pair (car a))) ;; last pair
      (and (natp (cdr pair))
           (sra-nat-row-elements-p (cdr a))))))

(defun sra-nat-rowp (a)
  (declare (xargs :guard t))
  (and (sra-rowp a)
       (sra-nat-row-elements-p a)))

(defthm sra-nat-rowp-forward-to-sra-rowp
  (implies (sra-nat-rowp row)
           (sra-rowp row))
  :rule-classes :forward-chaining)

(defthm forward-sra-rowp
  (implies (sra-rowp a)
           (and (alistp a)
                (true-listp a)))
  :rule-classes :forward-chaining)

(defun list-of-sra-rational-rowp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (null l)
    (and (sra-rational-rowp (car l))
         (list-of-sra-rational-rowp (cdr l)))))

(defun-inline sra-rget (pos row default)
  (declare (xargs :guard (and (natp pos)
                              (sra-rowp row))))
  (let ((pair (assoc pos row)))
    (if pair (cdr pair) default)))

(defthm sra-rget-sra-rational-rowp
  (implies (and (sra-rational-rowp row)
                (rationalp default))
           (rationalp (sra-rget pos row default))))

(defun sra-rput (pos row val)
  (declare (xargs :guard (and (natp pos)
                              (sra-rowp row))))
  (if (atom row)
      (list (cons pos val))
    (let* ((pair (car row))
           (rest (cdr row))
           (key (car pair)))
       (if (< pos key)
          (cons (cons pos val)
                row)
        (if (= pos key)
            (cons (cons pos val)
                  rest)
          (cons pair
                (sra-rput pos rest val)))))))

(defthm sra-rowp-sra-rput
  (implies (and (natp pos)
                (sra-rowp row))
           (sra-rowp (sra-rput pos row val))))

(defthm sra-rational-rowp-sra-rput
  (implies (and (natp j)
                (rationalp entry)
                (sra-rational-rowp row))
           (sra-rational-rowp (sra-rput j row entry))))

; SRA row evaluation

(defun sra-vw-eval-term-row-elements-p (row)
  (declare (xargs :guard (sra-rowp row)))
  (if (atom row)
      (null row)
    (let ((pair (car row)))
      (and (vw-eval-termp (cdr pair))
           (sra-vw-eval-term-row-elements-p (cdr row))))))

(defun sra-term-rowp (row)
  (declare (xargs :guard t))
  (and (sra-rowp row)
       (sra-vw-eval-term-row-elements-p row)))

(defthm sra-term-rowp-forward-to-sra-rowp
  (implies (sra-term-rowp row)
           (sra-rowp row))
  :rule-classes :forward-chaining)

(defun list-of-sra-term-rowp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (null l)
    (and (sra-term-rowp (car l))
         (list-of-sra-term-rowp (cdr l)))))

(defthm vw-eval-termp-sra-rget
  (implies (and (sra-vw-eval-term-row-elements-p row)
                (natp i)
                (vw-eval-termp default))
           (vw-eval-termp (sra-rget row i default)))
  :hints
  (("Goal" :in-theory (enable sra-rget))))

(defthm sra-term-rowp-sra-rget-is-vw-eval-termp
  (implies (and (vw-eval-termp default)
                (sra-term-rowp r))
           (vw-eval-termp (sra-rget j r default))))

(defthm sra-vw-eval-term-listp-sra-rput
  (implies (and (sra-vw-eval-term-row-elements-p row)
                (natp i)
                (vw-eval-termp expr))
           (sra-vw-eval-term-row-elements-p (sra-rput row i expr)))
  :hints
  (("Goal" :in-theory (enable sra-rput))))

(defthm sra-term-rowp-sra-rput
  (implies (and (natp j)
                (vw-eval-termp entry)
                (sra-term-rowp row))
           (sra-term-rowp (sra-rput j row entry))))

(defun list-of-sra-nat-rowp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (null l)
    (and (sra-nat-rowp (car l))
         (list-of-sra-nat-rowp (cdr l)))))

(defun sra-vw-eval-row (row a)
  (declare (xargs :guard (and (sra-term-rowp row)
                              (symbol-rational-list-alistp a)
                              (alist-entry-consp a))))
  (if (atom row)
      nil
    (let* ((pair (car row))
           (key (car pair))
           (val (cdr pair))
           (res (vw-eval val a)))
      (if (= res 0)
          (sra-vw-eval-row (cdr row) a)
        (cons (cons key res)
              (sra-vw-eval-row (cdr row) a))))))

(encapsulate
  ()
  (local (defthm sra-vw-eval-row-maintains-order
           (implies (and (sra-rowp row)
                         (consp (sra-vw-eval-row (cdr row) a)))
                    (< (car (car row))
                       (car (car (sra-vw-eval-row (cdr row) a)))))))

  (defthm sra-rowp-sra-vw-eval-row
    (implies (sra-rowp row)
             (sra-rowp (sra-vw-eval-row row a)))))

(defthm sra-rational-rowp-sra-vw-eval-row
  (implies (sra-term-rowp row)
           (sra-rational-rowp (sra-vw-eval-row row a))))

(in-theory (disable sra-rational-rowp sra-term-rowp sra-rget sra-rput))

(defun sra-vw-eval-fold-row (row a)
  (declare (xargs :guard (and (sra-term-rowp row)
                              (symbol-rational-list-alistp a)
                              (alist-entry-consp a))
                  :guard-hints
                  (("Goal" :in-theory (enable sra-term-rowp)))))
  (if (atom row)
      nil
    (let* ((pair (car row))
           (key (car pair))
           (val (cdr pair))
           (res (vw-eval-fold val a)))
      (if (equal res ''0)
          (sra-vw-eval-fold-row (cdr row) a)
        (cons (cons key res)
              (sra-vw-eval-fold-row (cdr row) a))))))

(encapsulate
  ()
  (local
   (defthm sra-vw-eval-fold-row-maintains-order
     (implies (and (sra-rowp row)
                   (consp (sra-vw-eval-fold-row (cdr row) a)))
              (< (car (car row))
                 (car (car (sra-vw-eval-fold-row (cdr row) a)))))))

  (defthm sra-rowp-sra-vw-eval-fold-row
    (implies (sra-rowp row)
             (sra-rowp (sra-vw-eval-fold-row row a)))))

(defthm sra-term-rowp-sra-vw-eval-row
  (implies (sra-term-rowp row)
           (sra-term-rowp (sra-vw-eval-fold-row row a)))
  :hints
  (("Goal" :in-theory (enable sra-term-rowp))))
