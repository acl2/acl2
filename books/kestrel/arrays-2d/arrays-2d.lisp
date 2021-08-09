; A formalization of 2-dimensional arrays as lists of rows
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book is about 2 dimensional arrays represented as lists of lists.
;; These definitions have nothing to do with acl2 arrays (aref1, aset1, etc.).

(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;; Applies true-list-fix to every element of LST.
(defund true-list-fix-list (lst)
  (if (endp lst)
      nil
    (cons (true-list-fix (car lst))
          (true-list-fix-list (cdr lst)))))

(defthm items-have-len-of-true-list-fix-list
  (equal (items-have-len n (true-list-fix-list lst))
         (items-have-len n lst))
  :hints (("Goal" :in-theory (enable items-have-len true-list-fix-list))))

;move
(defthm len-of-car-when-items-have-len-strong
  (implies (items-have-len n lst) ;n is a free var
           (equal (len (car lst))
                  (if (consp lst)
                      n
                    0))))

;; Recognize a 2D array (of values of an unspecified type) represented as a
;; list of rows. We allow nil (the list of no rows) because it will be the base
;; case of recursions.  Such an array has an ambiguous width.
(defund 2d-arrayp (val)
  (declare (xargs :guard t))
  (and (true-list-listp val)
       (or (null val)
           (let* ((first-row (car val))
                  (width (len first-row)))
             (items-have-len width (rest val))))))

(defthm 2d-arrayp-forward-to-true-listp
  (implies (2d-arrayp val)
           (true-listp val))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable 2d-arrayp))))

;; The number of rows in the array
(defund 2d-array-height (val)
  (declare (xargs :guard (2d-arrayp val)))
  (len val))

;; The number of columns in the array
(defund 2d-array-width (val)
  (declare (xargs :guard (and (2d-arrayp val)
                              (posp (2d-array-height val))))) ;otherwise, the width is ambiguous
  (len (first val)))

(defthm equal-of-2d-array-height-and-0
  (implies (2d-arrayp array)
           (equal (equal (2d-array-height array) 0)
                  (equal array nil)))
  :hints (("Goal" :in-theory (enable 2d-array-height))))

;ARRAY is a list of rows
;man, this is awkward to add a guard for:
(defund get-column (n array)
  (declare (xargs :guard (and (2d-arrayp array)
                              (natp n)
                              (or (eql 0 (2d-array-height array))
                                  (< n (2d-array-width array))))
                  :guard-hints (("Goal" :in-theory (enable 2d-arrayp 2d-array-width)))))
  (if (endp array)
      nil
    (cons (nth n (car array))
          (get-column n (cdr array)))))

;; returns a list of the columns of ARRAY from column NUM down to 0
(defund get-columns (num array)
  (declare (xargs :guard (and (2d-arrayp array)
                              (integerp num)
                              (<= -1 num)
                              (or (eql 0 (2d-array-height array))
                                  (< num (2d-array-width array))))
                  :guard-hints (("Goal" :in-theory (enable 2d-arrayp 2d-array-width)))))
  (declare (xargs :measure (nfix (+ 1 num))))
  (if (not (natp num)) ;stop at -1
      nil
    (cons (get-column num array)
          (get-columns (+ -1 num) array))))

(defun transpose-2d-array (array)
  (declare (xargs :guard (2d-arrayp array)
                  :guard-hints (("Goal" :in-theory (enable 2d-arrayp 2d-array-width)))))
  (if (eq nil array)
      nil
    (reverse-list (get-columns (+ -1 (2d-array-width array)) array))))

;(transpose-2d-array '((1 2 3) (4 5 6)))

;todo: deprecate this stuff?
;this is just get-column?
(defund cols-to-row (rownum cols)
  (if (endp cols)
      nil
    (cons (nth rownum (car cols))
          (cols-to-row rownum (cdr cols)))))

;this is just get-columns?
;cols is a list of lists, one list for each column of the array
(defund cols-to-array-aux (rownum cols)
    (declare (xargs :measure (nfix (+ 1 rownum))))
  (if (or (not (integerp rownum))
          (< rownum 0))
      nil
    (cons (cols-to-row rownum cols)
          (cols-to-array-aux (+ -1 rownum) cols))))

;similar to transpose-2d-array
;takes a list of columns and makes them into an array of the given size (do i need both size params?)
(defund cols-to-array (numrows cols)
  (reverse-list (cols-to-array-aux (+ -1 numrows) cols)))

(defthm cols-to-row-of-cons2
  (equal (cols-to-row rownum (cons col cols))
         (if (endp cols)
             (list (nth rownum col))
           (cons (nth rownum col)
                 (cols-to-row rownum cols))))
  :hints (("Goal" :in-theory (enable cols-to-row))))

(defthm cols-to-row-of-nil
  (equal (cols-to-row rownum nil)
         nil)
  :hints (("Goal" :in-theory (enable cols-to-row))))


;contents is a list of lists
(defund array-elem-2d (row col contents)
  (declare (xargs :guard (and (natp row)
                              (natp col)
                              (TRUE-LISTP CONTENTS)
                              (all-true-listp contents))))
  (nth col (nth row contents)))

(defthm array-elem-2d-of-cons
  (implies (and (natp row)
                (natp col))
           (equal (array-elem-2d row col (cons a b))
                  (if (equal 0 row)
                      (nth col a)
                    (array-elem-2d (+ -1 row) col b))))
  :hints (("Goal" :in-theory (e/d (array-elem-2d) ()))))


(defthm len-of-COLS-TO-ARRAY-AUX
  (implies (natp rownum)
           (equal (len (COLS-TO-ARRAY-AUX ROWNUM COLS))
                  (+ 1 rownum)))
  :hints (("Goal" :expand (COLS-TO-ARRAY-AUX 0 COLS)
           :in-theory (enable COLS-TO-ARRAY-aux))))

(defthm len-of-cols-to-array
  (implies (and (integerp n)
                (< 0 n))
           (equal (LEN (COLS-TO-ARRAY n cols))
                  n))
  :hints (("Goal" :in-theory (enable COLS-TO-ARRAY))))

(defthm true-listp-of-cols-to-array
  (true-listp (cols-to-array numrows cols))
  :hints (("Goal" :in-theory (enable cols-to-array))))

(defun indhhh (n rownum)
  (declare (xargs :measure (nfix (+ 1 rownum))))
  (if (OR (NOT (INTEGERP ROWNUM))
          (< ROWNUM 0))
      (list n rownum)
    (indhhh (+ -1 n) (+ -1 rownum))))

(defthm nth-of-COLS-TO-ARRAY-aux
  (implies (and (<= n rownum)
                (natp n)
                (natp rownum)
                )
           (equal (NTH n (COLS-TO-ARRAY-aux rownum cols))
                  (cols-to-row (- rownum n) cols)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (indhhh n rownum)
           :in-theory (enable COLS-TO-ARRAY-aux))))

(defthm nth-of-COLS-TO-ARRAY
  (implies (and (< n m)
                (natp n)
                (natp m)
                )
           (equal (NTH n (COLS-TO-ARRAY m cols))
                  (cols-to-row n cols)))
  :hints (("Goal" :in-theory (enable COLS-TO-ARRAY cols-to-row))))

(defthm len-of-cols-to-row
  (equal (LEN (COLS-TO-ROW rownum cols))
         (len cols))
  :hints (("Goal" :in-theory (enable COLS-TO-ROW))))

(defthm cols-to-row-of-cons
  (equal (COLS-TO-ROW rownum (cons col cols))
         (cons (nth rownum col)
               (COLS-TO-ROW rownum cols)))
  :hints (("Goal" :in-theory (enable COLS-TO-ROW))))

(defthm len-of-get-column
  (equal (len (get-column n rows))
         (len rows))
  :hints (("Goal" :in-theory (enable get-column))))

(defthm get-column-of-append
  (equal (get-column n (append rows1 rows2))
         (append  (get-column n rows1)
                  (get-column n rows2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable get-column reverse-list))))

(defthm get-column-of-reverse
  (equal (get-column n (reverse-list rows))
         (reverse-list (get-column n rows)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable get-column reverse-list))))

(defthm get-column-of-cons
  (equal (GET-COLUMN N (CONS row rows))
         (cons (nth n row)  (GET-COLUMN N rows)))
  :hints (("Goal" :in-theory (enable GET-COLUMN))))

(defthm helper-th
  (IMPLIES (AND (NATP ROWNUM) (CONSP COLS))
           (EQUAL (NTH 0 (COLS-TO-ROW ROWNUM COLS))
                  (NTH ROWNUM (NTH 0 COLS))))
  :hints (("Goal" :expand ((COLS-TO-ROW ROWNUM COLS)))))

(defthm nth-of-COLS-TO-ROW
  (implies (and (natp n)
                (natp rownum))
           (equal (NTH N (COLS-TO-ROW rownum COLS))
                  (nth rownum (nth n cols))))
  :hints (("Goal" :induct t
           :in-theory (e/d (COLS-TO-ROW nth) (nth-of-cdr)))))

(defthm get-column-of-nil
  (equal (GET-COLUMN N NIL)
         nil)
  :hints (("Goal" :in-theory (enable GET-COLUMN))))

(defthmd reverse-take-one-more
  (implies (and (<= (+ 1 n) (len lst))
                (natp n))
           (equal (REVERSE-LIST (TAKE (+ 1 n) lst))
                  (cons (nth n lst) (REVERSE-LIST (TAKE n lst)))))
  :hints (("Goal" :in-theory (enable take)))
  )

(defthm GET-COLUMN-of-COLS-TO-ARRAY-AUX
  (implies (and (natp n)
                (natp rownum)
                (< rownum (len (nth n cols))) ;yuck?
                ;; (consp cols)
                )
           (equal (GET-COLUMN N (COLS-TO-ARRAY-AUX rownum COLS))
                  (reverse-list (take (+ 1 rownum) (nth n cols)))))
  :hints (("Subgoal *1/4''" :in-theory (e/d (REVERSE-TAKE-ONE-MORE) (;CONS-NTH-REVERSE-TAKE
                                                                         )))
          ("Goal"
           :do-not '(generalize eliminate-destructors)
           :expand ( ;(REVERSE-LIST (TAKE ROWNUM (NTH N COLS)))
                    (COLS-TO-ARRAY-AUX 0 COLS))
     ;:induct (indhhh n rownum)
           :in-theory (e/d ( ;REVERSE-TAKE-ONE-MORE
                            COLS-TO-ARRAY-AUX) (;CONS-NTH-REVERSE-TAKE
                                                )))))

(defthm GET-COLUMN-of-COLS-TO-ARRAY
  (implies (and (<= M (LEN (NTH N COLS)))
                (< n m)
                ;; (< n (len cols))
                (natp n)
                (natp m))
           (equal (GET-COLUMN n (COLS-TO-ARRAY m cols))
                  (take m (nth n cols))))
  :hints (("Goal"
           :in-theory (enable COLS-TO-ARRAY))))

;move
(defthm ARRAY-ELEM-2D-of-cols-to-array
  (implies (and (< i numrows)
                (integerp numrows)
                ;; (< 0 numrows)
                (natp i)
                (< j (len cols))
                (natp j))
           (equal (ARRAY-ELEM-2D i j (cols-to-array numrows cols))
                  (ARRAY-ELEM-2D j i cols))
           )
  :hints (("Goal" :in-theory (e/d (cols-to-array ARRAY-ELEM-2D) (;NTH-OF-ARRAY-ROW ARRAY-ELEM-2D-RECOLLAPSE
                                                                 )))))

(defun take-list (n lst)
  (if (endp lst)
      nil
    (cons (take n (car lst)) (take-list n (cdr lst)))))

;use a defmap..
(defthm len-of-take-list
  (equal (len (take-list n lst))
         (len lst))
  :hints (("Goal" :in-theory (enable take-list))))

(defthm take-list-when-right-length
  (implies (and (items-have-len n lst) ;slow?
                (natp n))
           (equal (take-list n lst)
                  (true-list-fix-list lst)))
  :hints (("Goal" :in-theory (enable true-list-fix-list))))

(defthm true-list-fix-list-does-nothing
  (implies (all-true-listp lst)
           (equal (true-list-fix-list lst)
                  (true-list-fix lst)))
  :hints (("Goal" :in-theory (enable true-list-fix-list))))

(defthm consp-nth-from-items-have-len
  (implies (and (items-have-len n a)
                ;; (natp n)
                (natp m)
                (< 0 n)
                (< m (len a)))
           (consp (nth m a)))
  :hints (("Goal" :in-theory (e/d (items-have-len nth) (nth-of-cdr)))))

(defthm len-nth-from-items-have-len
  (implies (and (items-have-len n a) ;n is a free variable
                (< m (len a))
                ;; (natp n)
                (natp m)
;               (< 0 n)
                )
           (equal (len (nth m a))
                  n))
  :hints (("Goal" :in-theory (e/d (items-have-len nth) (nth-of-cdr)))))

(defthm true-list-fix-list-of-true-list-fix-list
  (equal (true-list-fix-list (true-list-fix-list lst))
         (true-list-fix-list lst))
  :hints (("Goal" :in-theory (enable true-list-fix-list))))



(defthm len-of-true-list-fix-list
  (equal (len (true-list-fix-list lst))
         (len lst))
 :hints (("Goal" :in-theory (enable true-list-fix-list))))


(defthm ALL-TRUE-LISTP-of-TRUE-LIST-FIX-LIST
  (ALL-TRUE-LISTP (TRUE-LIST-FIX-LIST lst))
  :hints (("Goal" :in-theory (enable TRUE-LIST-FIX-LIST))))

;disable these?
(defun row (n x)
  (nth n x))

(defun set-row (n value x)
  (update-nth n value x))

(defthmd cols-to-row-opener
  (implies (consp cols)
           (equal (cols-to-row rownum cols)
                  (cons (nth rownum (car cols))
                        (cols-to-row rownum (cdr cols)))))
  :hints (("Goal" :in-theory (enable cols-to-row))))


(defthm len-of-get-columns
  (implies (natp n)
           (equal (len (get-columns n COLS))
                  (+ 1 n)))
  :hints (("Goal" :expand (get-columns 0 COLS)
           :in-theory (enable get-columns))))

(defthm nth-of-get-columns
  (implies (and (<= n colnum)
                (natp n)
                (natp colnum)
                )
           (equal (NTH n (get-columns colnum cols))
                  (get-column (- colnum n) cols)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (indhhh n colnum)
           :in-theory (enable get-columns))))

(defthm nth-of-transpose-2d-array
  (implies (and (2d-arrayp array)
                (< n (2d-array-width array))
                (natp n)
                )
           (equal (nth n (transpose-2d-array array))
                  (get-column n array)))
  :hints (("Goal" :in-theory (enable cols-to-array cols-to-row))))

(defthm nth-of-get-column-orig
  (implies (natp n)
           (equal (nth n (get-column colnum cols))
                  (nth colnum (nth n cols))))
  :hints (("Goal" :induct t
           :in-theory (e/d (get-column nth) (nth-of-cdr)))))

(local
 (defun ind77 (j rows)
   (if (endp rows)
       (list j rows)
     (ind77 (+ -1 j) (cdr rows)))))

(defthm nth-of-get-column
  (implies (natp j)
           (equal (NTH j (GET-COLUMN i rows))
                  (ARRAY-ELEM-2D j i rows))
           )
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :induct (ind77 j rows)
           :in-theory (e/d (GET-COLUMN cols-to-array ARRAY-ELEM-2D nth-of-0)
                           ( )))))

(defthmd array-elem-2d-constant-opener
  (implies (and (syntaxp (quotep val))
                (natp row)
                (natp col))
           (equal (array-elem-2d row col val)
                  (if (equal 0 row)
                      (nth col (car val))
                      (array-elem-2d (+ -1 row) col (cdr val)))))
  :hints (("Goal" :in-theory (e/d (array-elem-2d)
                                  (;array-elem-2d-recollapse NTH-OF-ARRAY-ROW
                                   )))))

;bbbozo hack but we have to open the 2d-array stuff
;hack for triple des
(defthmd array-elem-2d-constant-opener-4-rows
  (implies (and (syntaxp (quotep val))
                (equal 4 (len val))
                (unsigned-byte-p 2 row)
                ;; (natp row)
                (natp col))
           (equal (array-elem-2d row col val)
                  (if (equal 0 row)
                      (NTH COL (NTH 0 VAL))
                    (if (equal 1 row)
                        (NTH COL (NTH 1 VAL))
                      (if (equal 2 row)
                          (NTH COL (NTH 2 VAL))
                        (NTH COL (NTH 3 VAL)))))))
  :hints (("Goal" :in-theory (e/d (ARRAY-ELEM-2D) (;NTH-OF-ARRAY-ROW ARRAY-ELEM-2D-RECOLLAPSE
                                                   )))))

(defthm 2d-arrayp-of-cons
  (equal (2d-arrayp (cons row rows))
         (and (items-have-len (len row) rows)
              (true-listp row)
              (2d-arrayp rows)))
  :hints (("Goal" :in-theory (enable 2d-arrayp))))
