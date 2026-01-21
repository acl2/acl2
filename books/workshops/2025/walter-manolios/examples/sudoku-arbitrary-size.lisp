;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-sudoku-arbitrary-size
  (:use :cl :z3))

(in-package :z3-sudoku-arbitrary-size)

(defun cell-idx (n row col)
  (+ col (* row n n)))

(defun idx-to-cell-var (idx)
  (intern (concatenate 'string "C" (write-to-string idx))))

;; We represent cell values as elements of an enumerated type
(defun val-to-cell-value (val)
  `(enumval :cell ,val))

(defun cell-vars (n)
  (loop for idx below (* n n n n)
        append (list (idx-to-cell-var idx) :cell)))

;; The values in each row must be distinct
(defun row-distinct-constraints (n)
  (loop for row below (* n n)
        collect (cons 'distinct
                      (loop for col below (* n n)
                            collect (idx-to-cell-var (cell-idx n row col))))))

;; The values in each column must be distinct
(defun col-distinct-constraints (n)
  (loop for col below (* n n)
        collect (cons 'distinct
                      (loop for row below (* n n)
                            collect (idx-to-cell-var (cell-idx n row col))))))

(defun box-cell-offsets (n)
  (loop for col below n
        append (loop for row below n
                     collect (cell-idx n row col))))

(defun box-starts (n)
  (mapcar (lambda (offset) (* n offset)) (box-cell-offsets n)))
              
;; The values in each 3x3 box must be distinct
(defun box-distinct-constraints (n)
  ;; These numbers are the indices of the top-left square of each box
  (loop for box-start in (box-starts n)
        collect (cons 'distinct
                      ;; These numbers are the offsets of each square in a box from the index of the box's top-left square
                      (loop for box-offset in (box-cell-offsets n)
                            collect (idx-to-cell-var (+ box-start box-offset))))))

(defun input-grid-constraints (n grid)
  (assert (eq (length grid) (* n n n n)))
  (loop for entry in grid
        for idx below (* n n n n)
        when (not (equal entry '_))
        collect `(= ,(idx-to-cell-var idx) ,(val-to-cell-value entry))))

(defun solve-grid (n input-grid)
  ;; We need to do solver-init here because we want to wipe out the old sort definition for :cell
  (solver-init)
  (z3::register-enum-sort-fn :cell (loop for i below (* n n) collect (1+ i)) z3::*default-context*) 
  (z3-assert-fn (cell-vars n) (cons 'and (row-distinct-constraints n)))
  (z3-assert-fn (cell-vars n) (cons 'and (col-distinct-constraints n)))
  (z3-assert-fn (cell-vars n) (cons 'and (box-distinct-constraints n)))
  (let ((input-constraints (input-grid-constraints n input-grid)))
    (when input-constraints (z3-assert-fn (cell-vars n) (cons 'and input-constraints))))
  (let ((res (check-sat)))
    (if (equal res :sat)
        (get-model-as-assignment)
      res)))

(defun get-square-value (soln idx)
  (let ((v (assoc (idx-to-cell-var idx) soln :test #'equal)))
    (if v (second v) nil)))

(defun pretty-print-sudoku-solution (n soln)
  ;; n-spaces is how many decimal digits it will take to display the
  ;; maximum cell value
  (let* ((n-spaces (ceiling (log (* n n) 10)))
         (value-format-spec (concatenate 'string "~" (write-to-string n-spaces) "d")))
    (loop for row below (* n n)
          do (progn (terpri)
                    (loop for col below (* n n)
                          do (progn (format t "~@? " value-format-spec (get-square-value soln (cell-idx n row col)))
                                    (when (equal (mod col n) (1- n)) (format t "  "))))
                  (when (equal (mod row n) (1- n)) (terpri))))))

(defun blank-grid (n)
  (loop for i below (* n n n n)
        collect '_))

;; Formatted for readability.
(defconstant a-hard-sudoku-grid
  '(6 _ _   3 _ 1   _ 8 4
    _ _ _   _ 6 9   _ _ 7
    _ _ _   _ _ 7   _ 1 3

    4 _ _   6 9 _   _ _ 8
    _ _ _   _ 1 5   _ _ _
    _ _ 8   _ _ _   _ 6 _

    _ _ _   _ _ _   _ _ _
    _ _ _   1 _ _   7 _ _
    2 _ 4   _ _ 3   1 _ _))

(pretty-print-sudoku-solution 3 (time (solve-grid 3 a-hard-sudoku-grid)))

(defun pretty-print-board (n board)
  (assert (equal (length board) (* n n n n)))
  (terpri)
  (let* ((n-spaces (ceiling (log (* n n) 10)))
         (value-format-spec (concatenate 'string "~" (write-to-string n-spaces) "a")))
    (loop for val in board
          for i below (* n n n n)
          do (progn
               ;; This avoids adding extra spaces after the value when not needed
               (if (equal (mod i (* n n)) (1- (* n n)))
                   (format t "~a" val)
                 (format t "~@?" value-format-spec val))
               (cond ((equal (mod i (* n n n)) (1- (* n n n))) (terpri) (terpri))
                     ((equal (mod i (* n n)) (1- (* n n))) (terpri))
                     ;; this format string just prints a variable number of spaces
                     ((equal (mod i n) (1- n)) (format t "~v{~a~:*~}" (1+ n-spaces) '(#\ )))
                     (t (format t " ")))))))

(defconstant hexadoku-grid
  '(1  _  2  _    _  _  10 6    8  _  _  5    4  11 _  _
    13 _  _  10   _  8  16 _    11 _  9  _    _  7  _  _
    _  11 _  _    _  _  _  _    _  2  7  _    _  14 _  9
    _  _  9  _    _  7  _  _    _  _  16 _    13 8  5  10
    
    _  16 _  15   1  _  _  2    10 4  _  6    _  _  _  8
    _  3  _  _    _  _  _  9    _  _  _  _    _  _  _  _
    10 9  4  2    _  5  _  13   _  _  12 _    3  _  _  _
    _  _  _  _    _  _  8  15   3  9  2  _    _  4  _  _
    
    _  _  1  _    _  16 14 3    9  6  _  _    _  _  _  _
    _  _  _  6    _  9  _  _    15 _  11 _    2  10 4  13
    _  _  _  _    _  _  _  _    2  _  _  _    _  _  1  _
    2  _  _  _    15 _  13 8    1  _  _  12   11 _  6  _
    
    5  4  14 1    _  13 _  _    _  _  6  _    _  15 _  _
    6  _  15 _    _  2  5  _    _  _  _  _    _  _  11 _
    _  _  11 _    _  15 _  16   _  7  1  _    12 _  _  4
    _  _  16 13   14 _  _  10   4  3  _  _    _  5  _  1))

;; Should take on the order of 10s
(pretty-print-sudoku-solution 4 (time (solve-grid 4 hexadoku-grid)))

(defconstant hexadoku-grid2
  '(1  2  3  4    5  6  7  8    9  10 11 12   13 14 15 16
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _
    _  _  _  _    _  _  _  _    _  _  _  _    _  _  _  _))

;; very slow... (~260s)
;;(time (solve-grid 4 hexadoku-grid2))
