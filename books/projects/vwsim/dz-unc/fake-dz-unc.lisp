
; Copyright (C) 2021-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' in top-level directory for additional
; information.

; FAKE! - FAKE! - FAKE! - FAKE! - FAKE! - FAKE! - FAKE! - FAKE! - FAKE!
; (certify-book "fake-dz-unc" 0 t :skip-proofs-okp t)
; (include-book "fake-dz-unc" :skip-proofs-okp t)

; THIS CODE CANNOT BE RUN BUT DOES HAVE REALISTIC GUARDS ON THE STOBJ
; PRIMITIVES AND DZ-UNC-DECOMP AND DZ-UNC-SOLVE
; -----------------------------------------------------------------

; The Unconventional Gaussian Elimination Solver
; J Strother Moore
; August, 2021

; Abstract: This file provides a system for solving Ax = b, given an nxn matrix
; A and a vector b of length n.  Two core functions here, dz-unc-decomp and
; dz-unc-solve, together they provide functionality akin to that of an LU
; solver but use a Gaussian elimination algorithm specialized for sparse
; matrices.

; The basic use case for solving Ax = b for a given A and various vectors b is:

; (1) load A into the stobj dz (see load-SR-matrix-into-DZ-a defined in
;     dz-unc.lisp as an example of how to move data from the user's environment
;     into the A array of the dz stobj and initialize certain other fields)

; (2) call DZ-UNC-DECOMP to put the A array of dz into triangular form and to
;     generate a ``program'' for solving Ax = b for any given b,

; (3) load a b vector into dz (as with load-LL-vector-into-DZ-b defined in
;     dz-unc.lisp as an example of how to move data from the the user's
;     environment into the b array of dz),

; (4) call DZ-UNC-SOLVE to write the solution to Ax = b into the x array of dz,

; (5) extract the solution from dz (see extract-soln-as-a-list in dz-unc.lisp
;     as an example of how to move data from dz into the user's environment),
;     and

; (6) repeat from (3) for the same A but other b vectors.

; See the README file for details, setup instructions, how to use the system,
; and some performance comparisons.

; Coincidentally, this file also contains a conventional Gaussian elimination
; procedure, dz-solve.  That function is equivalent to the dz-solve function
; described in ~/Sync/sf/Moore/dz-13-july-2021/dz.lisp.  However, because that
; function is much slower than the system described here we do not recommend
; its use.  Eventually, we will excise the older system from this one.

(in-package "ACL2")

; (program)

(defmacro meaningless-placeholder (result)
  `(prog2$
    (cw "You can't run dz-solve except in raw mode!~%")
    ,result))

(defmacro the-data (x)
  `(the #-raw rational #+raw double-float ,x))

(defmacro the-small-int (x)
  `(the (signed-byte 60) ,x))

(defmacro i+ (&rest args)
  (cond ((endp args) 0)
        ((endp (cdr args)) `(the-small-int ,(car args)))
        (t `(the-small-int (+ (the-small-int ,(car args))
                              (i+ ,@(cdr args)))))))

(defmacro i* (&rest args)
  (cond ((endp args) 1)
        ((endp (cdr args)) `(the-small-int ,(car args)))
        (t `(the-small-int (* (the-small-int ,(car args))
                              (i* ,@(cdr args)))))))

(defmacro i- (x &optional (y 'nil binary-p))
  (if binary-p
      `(the-small-int (- (the-small-int ,x) (the-small-int ,y)))
      `(the-small-int (- (the-small-int ,x)))))

(defmacro i= (x y)
  `(= (the-small-int ,x) (the-small-int ,y)))

(defmacro i< (x y)
  `(< (the-small-int ,x) (the-small-int ,y)))

(defmacro i<= (x y)
  `(<= (the-small-int ,x) (the-small-int ,y)))

(defmacro i> (x y)
  `(> (the-small-int ,x) (the-small-int ,y)))

(defmacro i>= (x y)
  `(>= (the-small-int ,x) (the-small-int ,y)))

(defmacro d0 ()
  #-raw 0
  #+raw 0.0D0)

(defmacro d1 ()
  #-raw 1
  #+raw 1.0D0)

(defmacro d+ (&rest args)
  (cond ((endp args) (d0))
        ((endp (cdr args)) `(the-data ,(car args)))
        (t `(the-data (+ (the-data ,(car args))
                         (d+ ,@(cdr args)))))))

(defmacro d* (&rest args)
  (cond ((endp args) (d1))
        ((endp (cdr args)) `(the-data ,(car args)))
        (t `(the-data (* (the-data ,(car args))
                         (d* ,@(cdr args)))))))

(defmacro d- (x &optional (y 'nil binary-p))
  (if binary-p
      `(the-data (- (the-data ,x) (the-data ,y)))
      `(the-data (- (the-data ,x)))))

(defmacro d/ (x &optional (y 'nil binary-p))
  (if binary-p
      `(the-data (/ (the-data ,x) (the-data ,y)))
      `(the-data (/ (the-data ,x)))))

(defmacro d= (x y)
  `(= (the-data ,x) (the-data ,y)))

; We don't define d< because it is defined in ordinals/lexicographic-book.lisp.
; But we don't use that comparison anyway.

(defmacro d<= (x y)
  `(<= (the-data ,x) (the-data ,y)))

(defmacro d> (x y)
  `(> (the-data ,x) (the-data ,y)))

(defmacro d>= (x y)
  `(>= (the-data ,x) (the-data ,y)))

(defmacro index->address (index dz)
  `(the-small-int
    (* (the-small-int ,index)
       (the-small-int (dim ,dz)))))

(defmacro address->index (addr dz)
  `(the-small-int
    (/ (the-small-int ,addr)
       (the-small-int (dim ,dz)))))

(defmacro zcnt-of-address (addr dz)
  `(the-small-int
    (let ((addr ,addr))
      (if (d= (ai addr ,dz) (d0))
          (zi addr ,dz)
          0))))

(defmacro lead-coef-of-address (addr dz)
  `(the-data
    (let* ((addr ,addr)
           (e (ai addr ,dz)))
      (if (d= e (d0))
          (ai (i+ (zi addr ,dz) addr) ,dz)
          e))))

; The dz stobj

(defstobj dz
  (dim :type integer
       :initially 0)
  (dim*dim :type integer
           :initially 0)
  (a :type (array #-raw rational #+raw double-float
                  (1))
     :initially #-raw 0 #+raw 0.0D0
     :resizable t)
  (z :type (array (signed-byte 60) ; integer
                  (1))
     :initially 0
     :resizable t)
  (b :type (array #-raw rational #+raw double-float
                  (1))
     :initially #-raw 0 #+raw 0.0D0
     :resizable t)
  (x :type (array #-raw rational #+raw double-float
                  (1))
     :initially #-raw 0 #+raw 0.0D0
     :resizable t)
  (b-program :type t :initially :conventional-gaussian-elim)
  (print-msgp :type t :initially nil)
  (top-row :type (signed-byte 60) :initially -1)
  (nx-row :type (array (signed-byte 60) (1))
          :initially -1
          :resizable t)
  (nx-blk :type (array (signed-byte 60) (1))
          :initially -1
          :resizable t)
  :renaming ((zp dz-zp))
  :inline t)

(skip-proofs
(defun clear-dz-a (i max dz)
  (declare (xargs :stobjs (dz)))
  (cond
   ((i>= i max) dz)
   (t (let ((dz (update-ai i (d0) dz)))
        (clear-dz-a (i+ i 1) max dz))))))

(skip-proofs
(defun clear-dz-b (i max dz)
  (declare (xargs :stobjs (dz)))
  (cond
   ((i>= i max) dz)
   (t (let ((dz (update-bi i (d0) dz)))
        (clear-dz-b (i+ i 1) max dz))))))

(skip-proofs
(defun clear-dz (dz)
  (declare (xargs :stobjs (dz)))
  (let* ((dz (clear-dz-a 0 (a-length dz) dz))
         (dz (clear-dz-b 0 (b-length dz) dz)))
    dz)))

; Here starts the real code for solving...

(skip-proofs
(defun insert-row-into-blk
    (row-index row-zcnt row-coef prev-blk-index blk-index dz)
; Initially, prev-blk-index is current-blk.  row-coef is actually the absolute
; value of that coefficient.
  (declare (xargs :stobjs (dz))
           (type (signed-byte 60) row-index row-zcnt prev-blk-index blk-index)
           (type #+raw double-float #-raw rational
                 row-coef)
           (ignore row-index row-zcnt row-coef prev-blk-index blk-index))
  #+raw
  (loop do
        (cond
         ((equal blk-index -1)
          (let* ((dz (if (equal prev-blk-index -1)
                         (update-top-row row-index dz)
                         (update-nx-blki prev-blk-index row-index dz)))
                 (dz (update-nx-blki row-index -1 dz))
                 (dz (update-nx-rowi row-index -1 dz)))
            (return dz)))
         (t (let ((blk-index-zcnt
                   (zcnt-of-address (index->address blk-index dz) dz)))
              (cond
               ((< row-zcnt blk-index-zcnt)
                (let* ((dz (if (equal prev-blk-index -1)
                               (update-top-row row-index dz)
                               (update-nx-blki prev-blk-index row-index dz)))
                       (dz (update-nx-blki row-index blk-index dz))
                       (dz (update-nx-rowi row-index -1 dz)))
                  (return dz)))
               ((equal row-zcnt blk-index-zcnt)
                (let ((blk-index-coef (the-data
                                       (abs (lead-coef-of-address
                                             (index->address blk-index dz)
                                             dz)))))
                  (cond
                   ((d<= row-coef blk-index-coef)
                    (let* ((temp (nx-rowi blk-index dz))
                           (dz (update-nx-rowi blk-index row-index dz))
                           (dz (update-nx-rowi row-index temp dz)))
                      (return dz)))
                   (t (let* ((dz (if (equal prev-blk-index -1)
                                     (update-top-row row-index dz)
                                     (update-nx-blki prev-blk-index row-index dz)))
                             (dz (update-nx-blki row-index (nx-blki blk-index dz) dz))
                             (dz (update-nx-rowi row-index blk-index dz)))
                        (return dz))))))
               (t (setq prev-blk-index blk-index)
                  (setq blk-index (nx-blki blk-index dz))))))))
  #-raw
  (meaningless-placeholder dz)))

(skip-proofs
(defun initialize-blocks (row-index dim dz)
  (declare (xargs :stobjs (dz)))
  (cond
   ((i>= row-index dim) dz)
   (t (let* ((row-addr (index->address row-index dz))
             (dz (insert-row-into-blk row-index
                                      (zcnt-of-address row-addr dz)
                                      (abs (lead-coef-of-address row-addr dz))
                                      -1
                                      (top-row dz)
                                      dz)))
        (initialize-blocks (i+ 1 row-index) dim dz))))))

(skip-proofs
(defun configure-dz-z (addr next-row-addr zcnt-addr zcnt dim max dz)

; zcnt-addr is either an address or nil!  If it is an address, it's the address
; of where we should write the zcnt when we eventually encounter a non-zero.
; It is nil if we just started row addr0 or if we just saw a non-zero.

  (declare (xargs :stobjs (dz))
           (type (signed-byte 60)
                 addr next-row-addr zcnt dim max)
           (type (or null (signed-byte 60)) zcnt-addr)
           (ignore addr next-row-addr zcnt-addr zcnt dim max))
  #+raw
  (loop do
        (cond
         ((i>= addr next-row-addr)
          (let ((dz (if zcnt-addr
                        (if (>= zcnt dim)
			    (prog2$ (er hard 'configure-dz-z
                                        "Row ~x0 is empty!"
                                        (floor (- next-row-addr dim) dim))
                                    dz)
			    (update-zi zcnt-addr zcnt dz))
                        dz)))
            (cond
             ((i>= next-row-addr max)
              (return dz))
             (t
              (setq addr next-row-addr)
              (setq next-row-addr (i+ next-row-addr dim))
              (setq zcnt-addr nil)
              (setq zcnt 0)))))
         ((d= (ai addr dz) (d0))
          (setq zcnt-addr
                (if zcnt-addr
                    zcnt-addr
                    addr))
          (setq addr (i+ addr 1))
          (setq zcnt (i+ 1 zcnt)))
         (t (let ((dz (if zcnt-addr
                          (update-zi zcnt-addr zcnt dz)
                          dz)))
              (setq addr (i+ addr 1))
              (setq zcnt-addr nil)
              (setq zcnt 0))))
        finally
        (return
         (let ((dz (if zcnt-addr
                       (update-zi zcnt-addr zcnt dz)
                       dz)))
           dz)))
  #-raw
  (meaningless-placeholder dz)))

(skip-proofs
(defun configure-dz (dz)

; We assume the user has written his A and b into the A and b arrays of dz.
; But no other fields have been set and none of the dz invariants necessarily
; hold.  We might have to resize the hidden array fields, z, x, nx-row and
; nx-blk, and initialize the z array so that it accurately reports the lengths
; of the zero gaps in the user's A and we have to organize the rows in A and b
; into blocks chained together by the nx-row and nx-blk arrays.

  (declare (xargs :stobjs (dz)))
  (let* ((dim (b-length dz))
         (dim*dim (i* dim dim)))
    (cond
     ((not (i= dim*dim (a-length dz)))
      (prog2$
       (er hard 'configure-dz
           "The A and b components of dz are not sized appropriately.  ~
            (A-length dz) must be the square of (b-length dz) but (a-length ~
            dz) = ~x0 and (b-length dz) = ~x1."
           (a-length dz)
           (b-length dz))
       dz))
     (t (let* ((dz (update-dim dim dz))
               (dz (update-dim*dim dim*dim dz))
               (dz (if (i= dim*dim (z-length dz))
                       dz
                       (resize-z dim*dim dz)))
               (dz (if (i= dim (x-length dz))
                       dz
                       (resize-x dim dz)))
               (dz (if (i= dim (nx-row-length dz))
                       dz
                       (resize-nx-row dim dz)))
               (dz (if (i= dim (nx-blk-length dz))
                       dz
                       (resize-nx-blk dim dz)))
               (dz (configure-dz-z 0 dim nil 0 dim dim*dim dz))
               (dz (update-top-row -1 dz))
               (dz (initialize-blocks 0 dim dz)))
          dz))))))

; In the following row1 and row2 are the (absolute) addresses of the beginning
; of two rows.

; The following three functions are the basic steppers through the a array of
; dz.  The first one is for use when we've just read non-zeros from both row1
; and row2, the second is for when we read a non-zero from row1 but a zero from
; row2, and the third is for when we read a zero from row1 and a non-zero from
; row2.

(skip-proofs
(defun next-non-zero0 (j row1 row2 dz dim)

; Dim is available from dz but we pass it in to save time since this function
; is used often.

; row1[j] and row2[j] are non-zero (but we know nothing about their scaled
; sum).  We return (mv j' z1' z2' e1' e2') where j' is the index of
; next non-zero entry in either row1 or row2 (or else j' is dim), e1' and e2'
; are those corresponding entries, and z1' and z2' are the number of zeros to
; the right of j' (counting the element at j') in the other row.  Constraints:

; * If e1' and e2' are both non-zero, then z1' and z2' are both 0.

; * If e1' is non-zero, then e2' is zero, z1' is 0, and z2' is the number of
;   zeros (counting e2') between j' and the next non-zero in row2.

; * If e1' is zero, then e2' is non-zero, z1' is the number of zeros (counting
;   e1') between j' and the next non-zero in row1, and z2' is 0.

; * Else, there were no further non-zeros in either row and j' is dim.

; Because row1[j] and row2[j] are non-zero each may be followed by zeros.

  (declare (xargs :stobjs (dz)))
  (let ((j1 (i+ j 1)))
    (cond
     ((i= j1 dim)
      (mv dim 0 0 (d0) (d0)))
     (t (let ((e1 (ai (i+ j1 row1) dz))
              (e2 (ai (i+ j1 row2) dz)))
          (cond
           ((d= e1 (d0))
            (cond
             ((d= e2 (d0))
              (let ((z1 (zi (i+ j1 row1) dz)) ; number of zeros to next non-zero in row1
                    (z2 (zi (i+ j1 row2) dz)) ; number of zeros to next non-zero in row2
                    )
                (cond
                 ((i= z1 z2)
                  (let ((j2 (i+ j1 z1)))
                    (cond
                     ((i= j2 dim)
                      (mv dim 0 0 (d0) (d0)))
                     (t (mv j2 0 0 (ai (i+ j2 row1) dz) (ai (i+ j2 row2) dz))))))
                 ((i< z1 z2) ; See note below
                  (let ((j2 (i+ j1 z1)))
                    (mv j2 0 (i- z2 z1) (ai (i+ j2 row1) dz) (d0))))
                 (t
                  (let ((j2 (i+ j1 z2)))
                    (mv j2 (i- z1 z2) 0 (d0) (ai (i+ j2 row2) dz)))))))
             (t (mv j1 (zi (i+ j1 row1) dz) 0 (d0) e2))))
           ((d= e2 (d0))
            (mv j1 0 (zi (i+ j1 row2) dz) e1 (d0)))
           (t (mv j1 0 0 e1 e2)))))))))

; Note: If e1 and e2 are both zero and not equal, then j plus the smaller of z1
; and z2 is a legal index in the corresponding row.  The reason is that the
; largest possible zi value at index j is the distance to the next row and all
; smaller z are legal offsets in the current row.

(skip-proofs
(defun next-non-zero1 (j z2 row1 row2 dz dim)

; Like next-non-zero0, except now we know that row1[j] is non-zero but row2[j]
; is zero and we know that the next non-zero in row2 is at (i+ j z2).
; Furthermore, we know that z2 is non-0 because if it were then both rows would
; have had non-zeros at j.  That also means that j+1 is a legal index.

  (declare (xargs :stobjs (dz)))

  (let ((j1 (i+ j 1)))
    (cond
     ((i= j1 dim)
      (mv j1 0 0 (d0) (d0)))
     (t (let ((e1 (ai (i+ j1 row1) dz))
              (e2 (if (i= z2 1) (ai (i+ j1 row2) dz) (d0))))
          (cond
           ((d= e1 (d0))
            (cond
             ((d= e2 (d0))
; Number of zeros from j1 to next non-zero in each row
              (let ((z1 (zi (i+ j1 row1) dz))
                    (z2 (i- z2 1)))
                (cond
                 ((i= z1 z2)
                  (let ((j2 (i+ j1 z1)))
                    (mv j2 0 0 (ai (i+ j2 row1) dz) (ai (i+ j2 row2) dz))))
                 ((i< z1 z2)
                  (let ((j2 (i+ j1 z1)))
                    (mv j2 0 (i- z2 z1) (ai (i+ j2 row1) dz) (d0))))
                 (t
                  (let ((j2 (i+ j1 z2)))
                    (mv j2 (i- z1 z2) 0 (d0) (ai (i+ j2 row2) dz)))))))
             (t (mv j1 (zi (i+ j1 row1) dz) 0 (d0) e2))))
           ((d= e2 (d0))
            (mv j1 0 (i- z2 1) e1 (d0)))
           (t (mv j1 0 0 e1 e2)))))))))

(skip-proofs
(defun next-non-zero2 (j z1 row1 row2 dz dim)

; Like next-non-zero1, except now we know that row1[j] is zero but row2[j]
; is non-zero and we know that the next non-zero in row1 is at (i+ j z1).

  (declare (xargs :stobjs (dz)))
  (let ((j1 (i+ j 1)))
    (cond
     ((i= j1 dim)
      (mv j1 0 0 (d0) (d0)))
     (t
      (let ((e1 (if (i= z1 1) (ai (i+ j1 row1) dz) (d0)))
            (e2 (ai (i+ j1 row2) dz)))
        (cond
         ((d= e1 (d0))
          (cond
           ((d= e2 (d0))
; Number of zeros from j1 to next non-zero in each row
            (let ((z1 (i- z1 1))
                  (z2 (zi (i+ j1 row2) dz)))
              (cond
               ((i= z1 z2)
                (let ((j2 (i+ j1 z1)))
                  (mv j2 0 0 (ai (i+ j2 row1) dz) (ai (i+ j2 row2) dz))))
               ((i< z1 z2)
                (let ((j2 (i+ j1 z1)))
                  (mv j2 0 (i- z2 z1) (ai (i+ j2 row1) dz) (d0))))
               (t
                (let ((j2 (i+ j1 z2)))
                  (mv j2 (i- z1 z2) 0 (d0) (ai (i+ j2 row2) dz)))))))
           (t (mv j1 (i- z1 1) 0 (d0) e2))))
         ((d= e2 (d0))
          (mv j1 0 (zi (i+ j1 row2) dz) e1 (d0)))
         (t (mv j1 0 0 e1 e2)))))))))

(skip-proofs
(defun first-non-zero (row1 row2 dz)

; We return (mv j z1 z2 e1 e2), where j is the index of the first non-zero
; element in either row, e1 and e2 are those elements (both of which cannot be
; zero but one of which might be zero), and if e1 is non-zero, then z1 is 0 and
; z2 is the number of zeros from j to the first non-zero in row2, and if e2 is
; non-zero, then z2 is 0 and z1 is the number of zeros from j to the first
; non-zero in row1.

  (declare (xargs :stobjs (dz)))
  (let ((e1 (ai row1 dz))
        (e2 (ai row2 dz)))
    (cond
     ((d= e1 (d0))
      (cond
       ((d= e2 (d0))
        (let ((z1 (zi row1 dz))
              (z2 (zi row2 dz)))
          (cond
           ((i= z1 z2)
            (mv z1 0 0 (ai (i+ z1 row1) dz) (ai (i+ z2 row2) dz)))
           ((i< z1 z2)
            (mv z1 0 (i- z2 z1) (ai (i+ z1 row1) dz) (d0)))
           (t (mv z2 (i- z1 z2) 0 (d0) (ai (i+ z2 row2) dz))))))
       (t (mv 0 (zi row1 dz) 0 (d0) e2))))
     ((d= e2 (d0))
      (mv 0 0 (zi row2 dz) e1 (d0)))
     (t (mv 0 0 0 e1 e2))))))

; Let gap be the number of uninterupted zeros below j in row2.  If you write a
; zero, gap grows by 1.  If you skip over k zeros, gap grows by k.  When you
; write a non-zero write gap into the z of j-gap.

(skip-proofs
(defun dz-add-row1 (scalar j z1 z2 e1 e2 gap row1 row2 dim firstp dz)

; Unless j is dim, at least one of row1[j] and row2[j] is non-zero.

  (declare (type (signed-byte 60) j z1 z2 gap row1 row2 dim)
           (type #-raw rational #+raw double-float scalar e1 e2)
           (xargs :stobjs (dz))
           (ignore scalar j z1 z2 e1 e2 gap row1 row2 dim firstp))
  #+raw
  (loop do
        (cond
         ((i= j dim)
          (let* ((dz (if (i= gap 0) dz (update-ai (i+ (i- j gap) row2) (d0) dz)))
                 (dz (if (i= gap 0) dz (update-zi (i+ (i- j gap) row2) gap dz))))
            (return dz)))
         ((d= e1 (d0))

; We ``write'' a non-zero (by leaving e2 untouched).  So we must update the
; ruling z.

          (let* ((dz (if (i= gap 0) dz (update-ai (i+ (i- j gap) row2) (d0) dz)))
                 (dz (if (i= gap 0) dz (update-zi (i+ (i- j gap) row2) gap dz))))
            (mv-let (new-j new-z1 new-z2 new-e1 new-e2)
              (next-non-zero2 j z1 row1 row2 dz dim)
              (progn
                (setq gap (i+ (i- new-j j) -1))
                (setq j new-j)
                (setq z1 new-z1)
                (setq z2 new-z2)
                (setq e1 new-e1)
                (setq e2 new-e2)
                (setq firstp nil)))))
         ((d= e2 (d0))
          (let ((temp (the-data (d* scalar e1))))
            (mv-let (new-j new-z1 new-z2 new-e1 new-e2)
              (next-non-zero1 j z2 row1 row2 dz dim)
              (cond
               ((d= temp (d0))

; The ``zero'' at (ai (i+ j row2) dz) may be an uninitialized slot that is implicitly
; zero in the sparse representation.  But we might use this slot as a ruling
; zero down the line.  So we make it explicit.  The gap has grown by 1.  The
; expression (i+ gap (i- j1 j)), below, could be replaced by the less efficient
; but equivalent (i+ gap (i- j1 j) -1 +1) to make this growth by 1 more
; obvious!

                (let ((dz (update-ai (i+ j row2) (d0) dz)))
                  (progn
                    (setq gap (i+ gap (i- new-j j)))
                    (setq j new-j)
                    (setq z1 new-z1)
                    (setq z2 new-z2)
                    (setq e1 new-e1)
                    (setq e2 new-e2)
                    (setq firstp nil))))
               (t (let* ((dz (update-ai (i+ j row2) temp dz))
                         (dz (if (i= gap 0) dz (update-ai (i+ (i- j gap) row2) (d0) dz)))
                         (dz (if (i= gap 0) dz (update-zi (i+ (i- j gap) row2) gap dz))))
                    (progn
                      (setq gap (i+ (i- new-j j) -1))
                      (setq j new-j)
                      (setq z1 new-z1)
                      (setq z2 new-z2)
                      (setq e1 new-e1)
                      (setq e2 new-e2)
                      (setq firstp nil))))))))
         (t (let* ((temp0 (d+ (d* scalar e1) e2))
                   (temp (if firstp
                             (if (and (not (d= temp0 (d0)))
                                      (print-msgp dz))
                                 (prog2$
                                  (cw "Note: ~x0 coerced to zero.~%" temp0)
                                  (d0))
                                 (d0))
                             temp0)))
              (mv-let (new-j new-z1 new-z2 new-e1 new-e2)
                (next-non-zero0 j row1 row2 dz dim)
                (cond
                 ((d= temp (d0))
                  (let ((dz (update-ai (i+ j row2) (d0) dz)))
                    (progn
                      (setq gap (i+ gap (i- new-j j)))
                      (setq j new-j)
                      (setq z1 new-z1)
                      (setq z2 new-z2)
                      (setq e1 new-e1)
                      (setq e2 new-e2)
                      (setq firstp nil))))
                 (t (let* ((dz (update-ai (i+ j row2) temp dz))
                           (dz (if (i= gap 0) dz (update-ai (i+ (i- j gap) row2) (d0) dz)))
                           (dz (if (i= gap 0) dz (update-zi (i+ (i- j gap) row2) gap dz))))
                      (progn
                        (setq gap (i+ (i- new-j j) -1))
                        (setq j new-j)
                        (setq z1 new-z1)
                        (setq z2 new-z2)
                        (setq e1 new-e1)
                        (setq e2 new-e2)
                        (setq firstp nil))))))))))
  #-raw
  (meaningless-placeholder dz)))

(skip-proofs
(defun dz-add-row (scalar row1 row2 dim dz)
  (declare (xargs :stobjs (dz)))
  (mv-let (j1 z1 z2 e1 e2)
    (first-non-zero row1 row2 dz)
    (dz-add-row1 scalar j1 z1 z2 e1 e2 j1 row1 row2 dim t dz))))

(skip-proofs
(defun empty-rowp (row dim dz)
  (declare (xargs :stobjs (dz)))
  (and (d= (ai row dz) (d0))
       (i= (zi row dz) dim))))

(skip-proofs
(defun cancel-block1 (blk-index pivot-addr pivot-coef pivot-rhs
                                target-index dim dz)

; Blk-index is the index of the block we're working on.  The address of its
; pivot row is pivot-addr (which is in fact the address of the block, i.e.,
; pivot-addr is (index->address blk-index dz).  Pivot-coef and pivot-rhs are the
; leading non-zero coefficient and the right-hand side of the pivot equation.
; Target-index is the index of a row in this block and thus has the same number
; of leading zeros as the pivot.  We'll add a scalar multiple of the pivot to
; the target row to cancel the leading non-zero in the target and then put the
; modified row in the appropriate block.  That will destroy the nx-row pointer
; of the target, so we'll have to grab it before we insert the canceled target
; into a new block.  (This also means the structure of this block is
; destroyed.)  But we will clean it up -- setting nx-row of this blk to -1 --
; when we've canceled all the equations in it.

  (declare (xargs :stobjs (dz))
           (type (signed-byte 60) blk-index pivot-addr target-index dim)
           (type #+raw double-float #-raw rational
                  pivot-coef pivot-rhs)
           (ignore blk-index pivot-addr pivot-coef pivot-rhs
                   target-index dim))
  #+raw
  (loop do
        (cond
         ((i= target-index -1)
; We have exhausted this block.  Clean up.
          (let* ((dz (update-nx-rowi blk-index -1 dz)))
            (return (mv nil dz))))
         (t (let* ((target-addr (index->address target-index dz))
                   (d (lead-coef-of-address target-addr dz))
                   (scalar (the-data (d- (d/ d pivot-coef))))
                   (dz (dz-add-row scalar pivot-addr target-addr dim dz))
                   (b-prog (b-program dz))

; If (b-program dz), aka b-prog, is :conventional-gaussian-elim then we just
; modify the righthand side of the target equation by adding the product of the
; scalar and the pivot's rhs.  But if b-program is different it means we are
; just collecting the operations to perform on b later -- so we can perform
; them on multiple righthand sides.  The triple we create below, (cons
; target-index (cons scalar blk-index)) means: modify the bi of target-index by
; adding to it the product of scalar and (bi blk-index dz).  By the way,
; pivot-rhs, used in the conventional operation, is (bi blk-index dz) because
; blk-index is also the index of the pivot row.

                   (dz (if (eq b-prog :conventional-gaussian-elim)
                           (update-bi target-index
                                      (d+ (bi target-index dz) (d* scalar pivot-rhs))
                                      dz)
                           (update-b-program
                            (cons (cons target-index (cons scalar blk-index))
                                  b-prog)
                            dz)))
                   )

              (cond
               ((empty-rowp target-addr dim dz)
                (return (mv :unsolvable dz)))
               (t

; The equation at target-addr has been modified and no longer belongs in this
; block.  We insert it into the appropriate block.  But first we have to grab
; the next row in this block because insertion of target-addr will smash that
; value.  The insertion below will update the nx-blki field of this block if
; necessary.  But it leaves the nx-rowi field of the block untouched and thus
; the block is no longer coherent.  We don't care.  When we have canceled every
; equation in the block against the pivot, we set the nx-row of the block to
; -1.

                (let* ((next-target-index (nx-rowi target-index dz))
                       (dz (insert-row-into-blk target-index
                                                (zcnt-of-address target-addr dz)
; Note that the lead-coef-of-address for target-addr is no longer d!
                                                (abs
                                                 (lead-coef-of-address target-addr
                                                                       dz))
                                                blk-index
                                                (nx-blki blk-index dz)
                                                dz)))
                  (setq target-index next-target-index))))))))
  #-raw
  (meaningless-placeholder (mv nil dz))))

(skip-proofs
(defun cancel-block (blk-index dim dz)
  (declare (xargs :stobjs (dz)))
  (let* ((pivot-addr (index->address blk-index dz))
         (pivot-coef (lead-coef-of-address pivot-addr dz))
         (pivot-rhs (bi blk-index dz)) ; blk-index = pivot-index
         (nx-row-index (nx-rowi blk-index dz)))
    (cancel-block1 blk-index pivot-addr pivot-coef pivot-rhs
                   nx-row-index dim dz))))

(skip-proofs
(defun dz-phase1 (blk-index zcnt dim dz)

; Initially, blk-index is the index of the top-most block in A, which is found
; in (top-row dz).  Zcnt is initially 0 and is incremented as we cancel blocks.
; We check that the zcnt of the successive blocks is always the successive
; zcnts.  We cancel all of the equations in blk-index, distributing the
; resulting equations into lower blocks, and then recur to the nx-blk after
; blk-index.  We return (mv flg dz), where flg is :unsolvable or :error (the
; latter indicating a programming error).  If flg is nil, then the data
; structures of dz represent the unreduced row echelong form: starting at
; top-row, each successive block in the nx-blk chain is a singleton block
; containing equations with successively more leading zeros.

  (declare (xargs :stobjs (dz)))
  (cond
   ((i= blk-index -1)
    (if (i= (dim dz) zcnt)
        (mv nil dz)
        (mv (prog2$
             (er hard 'dz-phase1
                 "The nx-blk chain was is corrupted: we reached its end before ~
              all equations have been canceled.  Zcnt = ~x0."
                 zcnt)
             :error)
            dz)))
   ((not (i= zcnt (zcnt-of-address (index->address blk-index dz) dz)))
    (mv (prog2$
         (er hard 'dz-phase1
             "There is no tier with zcnt = ~x0!  Current block index is ~x0 ~
              (address ~x1) with zcnt ~x2 while we were expecting a zcnt of ~
              ~x3."
             blk-index
             (index->address blk-index dz)
             (zcnt-of-address (index->address blk-index dz) dz)
             zcnt)
         :error)
        dz))
   (t (mv-let (flg dz)
        (cancel-block blk-index dim dz)
        (cond
         ((eq flg :unsolvable)
          (mv :unsolvable dz))
         (t (dz-phase1 (nx-blki blk-index dz)
                       (i+ 1 zcnt)
                       dim
                       dz))))))))

; -----------------------------------------------------------------
; Phase 2

(skip-proofs
(defun reverse-nx-blk-chain (prev-blk-index blk-index dz)

; Starting with prev-blk-index = -1 and blk-index = (top-row dz) we reverse the
; nx-blk chain and return the last block index in the original chain and the
; modified dz.

  (declare (xargs :stobjs (dz)))
  (cond
   ((i= blk-index -1) (mv prev-blk-index dz))
   (t (let* ((nx-blk-index (nx-blki blk-index dz))
             (dz (update-nx-blki blk-index prev-blk-index dz)))
        (reverse-nx-blk-chain blk-index nx-blk-index dz))))))

(skip-proofs
(defun dz-sum-of-products-into-x (i j row-addr dim dz)

; We sum the products of successive coefficients (starting with index j of
; the row with address row-addr) with the values of successive variables
; starting with index j.  These values have already been stored in the x
; array of dz.  We accumulate the sum-of-products into (xi i dz).

  (declare (xargs :stobjs (dz)))
  (cond
   ((i>= j dim) dz)
   (t (let ((j-addr (i+ j row-addr)))
        (cond
         ((d= (ai j-addr dz) (d0))
          (dz-sum-of-products-into-x i
                                     (i+ j (zi j-addr dz))
                                     row-addr dim dz))
         (t (let ((dz (update-xi i
                                 (d+ (xi i dz)
                                     (d* (ai j-addr dz)
                                         (xi j dz)))
                                 dz)))
              (dz-sum-of-products-into-x i
                                         (i+ j 1)
                                         row-addr
                                         dim dz)))))))))

(skip-proofs
(defun dz-solve-for-leading-variable (i row-addr dim dz)

; The row starting at row-addr has i leading zeros.  The solutions to the
; higher variables (i.e., those to the right of i) are stored in the x array of
; dz.  Let d be the first non-zero coefficient in row.  Let temp be the sum of
; the products of subsequent coefficients with the corresponding solutions of
; higher variables.  Let b be the rhs of the row.  Then the solution, soln, to
; the leading variable of row, x_i, is (d/ (d- b temp) d).  We set (xi i dz) to
; soln and return dz.

  (declare (xargs :stobjs (dz)))
  (let* ((row-index (address->index row-addr dz))
         (e0 (ai row-addr dz))
         (d (the-data (if (d= e0 (d0))
                          (ai (i+ i row-addr) dz)
                          e0)))
         (dz (update-xi i (d0) dz))
         (dz (dz-sum-of-products-into-x
              i
              (i+ 1 i)
              row-addr dim dz))
         (b (the-data (bi row-index dz)))
         (dz (update-xi i (d/ (d- b (xi i dz)) d) dz)))
    dz)))

(skip-proofs
(defun dz-phase21 (i blk-index dim dz)

; Note: this function is the driver for dz-phase2.  Before it is called, the
; nx-blk chain in dz is reversed so that following it up from blk-index to the
; terminal marker -1 visits the blocks in the triangular form -- all of which
; contain exactly one equation.

; Initially i is dim-1, the index of the last column, aka, the index of the
; last variable for which we're solving.  The first (and only) equation in the
; block at blk-index has i leading zeros.  The first equation in the next block
; has i-1, etc.  The values of all the variabls x_j, j>i, are already in the x
; array of dz.  We compute the resulting solution and store it in x.  We start
; with the last variable and work backwards.  We just substitute previously
; computed values into each equation, solve for its leading variable, put that
; into (xi dz) and recur.

  (declare (xargs :stobjs (dz)))
  (cond
   ((i= blk-index -1) dz)
   (t (let ((dz
             (dz-solve-for-leading-variable i
                                            (index->address blk-index dz)
                                            dim dz)))
        (dz-phase21
         (i- i 1)
         (nx-blki blk-index dz)
         dim dz))))))

(skip-proofs
(defun dz-phase2 (dim dz)
  (declare (xargs :stobjs (dz)))
  (mv-let (btm-blk-index dz)
    (reverse-nx-blk-chain -1 (top-row dz) dz)
    (dz-phase21 (- dim 1) btm-blk-index dim dz))))

; -----------------------------------------------------------------
; The Conventional Gaussian Elimination Solver

(skip-proofs
(defun DZ-solve (dz)
  (declare (xargs :stobjs (dz)))
  (let* ((dz (update-b-program :conventional-gaussian-elim dz))
         (dz (configure-dz dz))
         (dim (dim dz)))
    (mv-let (flg dz)
      (dz-phase1 (top-row dz) 0 dim dz)
      (cond
       (flg

; If flg is non-nil it is either :unsolvable or :error.  The latter indicates a
; programming bug.

        (mv flg dz))
       (t (let ((dz (dz-phase2 dim dz)))
            (mv nil dz))))))))

; =================================================================
; Example of how to load the input and extract the solution.

; Warren and Vivek:

; If you intend to use the conventional Gaussian elimination solver, dz-solve,
; you should read all the comments in this section.  But remember two things.
; First, I don't recommend dz-solve; the unconventional solver is better.
; Second, the code for loading and unloading dz isn't run by either solver.
; You will write a versions of this code to load your data and extract the
; solution so that you avoid unnecessarily creating list-based matrices and
; vectors.

; At the very bottom of this section is the code for dz-solve-wrapped-up, which
; puts it all together: load data, call dz-solve, and extract the solution.
; You won't use dz-solve-wrapped-up; you'll write your own driver that calls
; dz-solve and your loaders and unloaders.

; In this code I assume the matrix A is in SR format.  But don't worry.  That's
; just a convenient way to show how I load data (that comes from somewhere)
; into dz.  I assume your data won't come from an SR array but will be
; generated from a symbolic form of your matrix, by evaluating each symbolic
; expression, squashing the result, and writing into its proper place in the A
; array of dz.

; A is a 1D matrix that represents a 2D matrix in row major form.  E.g.,

; 2D matrix            ==>  1D 
; (a b c                    (a b c d e f g h i)
;  d e f
;  g h i)

; To understand my example loader you need to understand my SR format just so
; you can see how I adjust the address I'm writing to.  In SR format a row like
; (0 0 x 0 y z 0 0 0) is written as ((2) x (1) y z) The loader below assumes A
; has been cleared (all zeros) and then just writes x, y, z into the proper
; locations.

; Remember that you need to write both the zeros and non-zeros, i.e., don't
; assume the dz arrays are initially all zero!  However, the functions
; clear-dz-a and clear-dz-b will fill A and b with zeros if you want just focus
; on the non-zeros.

; Squashing: dz-solve does not squash!  However, I recommend that you squash
; your input data.  Matrix solving by all methods tends to be unstable in the
; presence of very small (in absolute value) non-zero coefficients.  Below I
; use I use (<= (abs x) 1.0D-8) as the test for ``very small.''  I squash very
; very small numbers to 0.0D0 before the solver starts.  Thereafter, the
; computation is as mathematically accurate as double precision produces.

; When I tested dz-solve on the 2,199 matrices solved in the circuit simulation
; you sent, I used 1.0D-8 to squash the input (both in A and in b).  Then I
; computed the worst-case discrepancy (between the desired b and Ax, for each
; computed x).  The worst-case discrepancy was less than 1.2D-9.

; Below you see code for loading A and b (from lists of numbers) into dz.

(skip-proofs
(defun load-SR-row-into-DZ-a (sr-row addr dz)

; We load an SR row into absolute address addr of component A in dz.  We assume
; A has been cleared, as with the clear-dz-a function.  So we only write the
; non-zero entries in the places they belong and skip over all the zeros.

  (declare (type (signed-byte 60) addr)
           (type (satisfies true-listp) sr-row)
           (xargs :stobjs (dz))
           (ignore sr-row addr))
  #+raw
  (loop for x in sr-row
        do
        (cond ((consp x)
               (setq addr (i+ addr (car x))))
              (t (let* ((dz (update-ai addr
                                       (if (<= (abs x) 1.0D-8) ; squashing
                                           0.0D0
                                           x)
                                       dz)))
                   (setq addr (i+ addr 1)))))
        finally
        (return dz))
  #-raw
  (meaningless-placeholder dz)))

(skip-proofs
(defun right-size-dz (dim dz)

; We assume (dim dz) is accurately set for the other fields of dz, i.e., if
; (dim dz) is 7 then (a-length dz) and (z-length dz) are both 49, (b-length dz)
; is 7, etc.  So if the given dim is equal to (dim dz), everything is
; right-sized.  Otherwise, we resize everything.

  (declare (xargs :stobjs (dz)))
  (cond
   ((i= dim (dim dz))
    dz)
   (t (let* ((dim*dim (i* dim dim))
             (dz (update-dim dim dz))
             (dz (update-dim*dim dim*dim dz))
             (dz (resize-a dim*dim dz))
             (dz (resize-z dim*dim dz))
             (dz (resize-b dim dz))
             (dz (resize-x dim dz))
             (dz (resize-nx-row dim dz))
             (dz (resize-nx-blk dim dz)))
        dz)))))

(skip-proofs
(defun load-SR-matrix-into-DZ-a (A dz)

; A is an SR matrix.  We load it into component A of dz.  You'll do something
; similar over your symbolic version of the matrix, evaluating each expression
; as you go and putting its squashed value into dz.  Note that even the zeros
; in A need to be written into dz.  We do that below by clearing the A array
; and then loading the SR matrix row by row (which skips writing zeros).

  (declare (type (satisfies true-listp) A)
           (xargs :stobjs (dz))
           (ignore A))
  #+raw
  (let* ((dim (length A))
         (dz (right-size-dz dim dz))
         (dz (clear-dz-a 0 (i* dim dim) dz)))
    (declare (type (signed-byte 60) dim))
    (loop for sr-row in A
          with addr of-type (signed-byte 60) = 0
          do
          (let ((dz (load-SR-row-into-DZ-a sr-row addr dz)))
            (setq addr (i+ addr dim)))
          finally
          (return dz)))
  #-raw
  (meaningless-placeholder dz)))

(skip-proofs
(defun unc-configure-dz (dz)

; This is the ``unconventional'' configuration of dz.  See dz-unc-decomp below.
; We assume that dz has been right-sized and that A has been loaded into it, as
; with load-SR-matrix-into-DZ-a.  We finish configuring dz (without touching b,
; which may or may not have been loaded).

  (declare (xargs :stobjs (dz)))
  (let* ((dim (dim dz))
         (dz (configure-dz-z 0 dim nil 0 dim (i* dim dim) dz))
         (dz (update-top-row -1 dz))
         (dz (initialize-blocks 0 dim dz))
         (dz (update-b-program nil dz)))

; By setting b-program to nil we authorize the assembly of the reversed
; b-program by dz-phase1.

    dz)))

(skip-proofs
(defun load-LL-vector-into-DZ-b (b dz)

; We assume dz has been right-sized, that A has been loaded into it and
; unc-configured (and that, perhaps, dz-unc-decomp has already been performed).
; We load successive elements of the list b into the b array of dz.

  (declare (xargs :stobjs (dz))
           (ignore b))
  #+raw
  (loop for x in b
        with addr of-type (signed-byte 60) = 0
        do
        (let ((dz (update-bi addr
                             (if (<= (abs x) 1.0D-8) ; squashing
                                 0.0D0
                                 x)
                             dz)))
          (setq addr (i+ addr 1)))
        finally
        (return dz))
  #-raw
  (meaningless-placeholder dz)))

(skip-proofs
(defun load-A-and-b-into-dz (A b dz)

; We assume A is an nxn matrix in SR format and b is a list of numbers of
; length n.  We clear the A field of dz, then we load A and b from these lists
; into the arrays of dz.  We don't have to clear b first because we write every
; value in b.  We do not update any other fields of dz.  It is your job to make
; sure that the A and b fields are properly sized.  This probably is only done
; once per sim run since all the matrices are of the same dimensionality once
; the circuit is defined.

  (declare (type (satisfies true-listp) A b)
           (xargs :stobjs (dz)))
  (let ((dim (length b)))
    (declare (type (signed-byte 60) dim))
    (cond
     ((not (i= dim (length a)))
      (prog2$
       (er hard 'load-a-and-b-into-dz
           "A and b do not have corresponding dimensions.  Your A has ~x0 ~
            rows but your b has length ~x1."
           (length a)
           dim)
       dz))
     (t (let* ((dz (right-size-dz dim dz))
               (dz (clear-dz-a 0 (i* dim dim) dz))
               (dz (load-sr-matrix-into-dz-a A dz))
               (dz (load-ll-vector-into-dz-b b dz)))
          dz))))))

(skip-proofs
(defun extract-soln-as-a-list (dz)

; Here is how you get the solution out of dz, assuming that dz-solve
; returned (mv nil dz).

  (declare (xargs :stobjs (dz))
           (ignore dz))
  #+raw
  (loop for addr from 0 to (i- (dim dz) 1)
        collect
        (xi addr dz))
  #-raw
  (meaningless-placeholder nil)))

; The average times noted below are for the 2,199 problems generated by
; the example sim run.  I'll keep working to speed up dz-solve.  You
; might work on speeding up getting the data into dz.

(skip-proofs
(defun dz-solve-wrapped-up (A b dz)
  (declare (xargs :stobjs (dz)))
  (let ((dz (load-A-and-b-into-dz A b dz)))        ; avg time: 0.003 seconds
    (mv-let (flag dz)
      (dz-solve dz)                                ; avg time: 0.005 seconds
      (cond
       (flag (mv :unsolvable dz))
       (t (mv (extract-soln-as-a-list dz) dz)))))))

; =================================================================
; The Unconventional Solver

; The unconventional solver has an interface like LU Decomposition Solvers (see
; work/jj/sparse/lup/v0/README).  A typical sequence of steps is:

; (1) load A into DZ (as with load-SR-matrix-into-DZ-a above, which right-sizes
;     dz and puts A into the A array).

; (2) call DZ-UNC-DECOMP (which will unc-configure-dz (which configures dz
;     without b and setting the b-program field to NIL to authorize assembly of
;     the b program), run dz-phase1 (to put A into triangular form and assemble
;     the b-program field with a ``program'' for adjusting any given b),
;     reverse the block chain putting the bottom-most row index into top-row of
;     z, and reverse the b-program.  (so that dz-unc-solve can be run
;     repeatedly).

; (3) load b into DZ (as with load-LL-vector-into-DZ-b).

; (4) call DZ-UNC-SOLVE (which will run b-program on the loaded b and then run
;     dz-phase21 -- the core of dz-phase2 -- which puts the solution into x.

; (5) repeat from (3) for the same A but different bs.

(skip-proofs
(defun dz-unc-decomp (dz)

; We assume dz has been right-sized and that A has been loaded into it.  We
; finish configuring it for an unconventional decomp.  Then we run phase1 which
; puts A into triangular form and assembles the b-program in reverse order.

  (declare (xargs :stobjs (dz)
                  :guard (let* ((dim (dim dz))
                                (dim*dim (* dim dim)))
                           (and (equal (dim*dim dz) dim*dim)
                                (equal (a-length dz) dim*dim)
                                (equal (z-length dz) dim*dim)
                                (equal (b-length dz) dim)
                                (equal (x-length dz) dim)
                                (equal (nx-row-length dz) dim)
                                (equal (nx-blk-length dz) dim)))))
  (let* ((dim (dim dz))
         (dz (unc-configure-dz dz)))
    (declare (type (signed-byte 60) dim))
    (mv-let (flg dz)
      (dz-phase1 (top-row dz) 0 dim dz)
      (cond
       (flg

; If flg is non-nil it is either :unsolvable or :error.  The latter indicates a
; programming bug.

        (mv flg dz))
       (t
        (mv-let (btm-blk-index dz)
          (reverse-nx-blk-chain -1 (top-row dz) dz)
          (declare (type (signed-byte 60) btm-blk-index))
          (let* ((dz (update-top-row btm-blk-index dz))
                 (dz (update-b-program (revappend (b-program dz) nil) dz)))
            (mv nil dz)))))))))

(skip-proofs
(defun run-b-program (prog dz)
  (declare (xargs :stobjs (dz))
           (type (satisfies true-listp) prog)
           (ignore prog))
  #+raw
  (loop for ins in prog do
        (let ((target-addr (car ins))
              (scalar (cadr ins))
              (rhs-index (cddr ins)))
          (declare (type (signed-byte 60) target-addr rhs-index)
                   (type #+raw double-float #-raw rational scalar))
          (update-bi target-addr
                     (d+ (bi target-addr dz)
                         (d* scalar (bi rhs-index dz)))
                     dz))
        finally
        (return dz))
  #-raw
  (meaningless-placeholder dz)))

(skip-proofs
(defun dz-unc-solve (dz)

; We assume dz-unc-decomp has been run successfully on an A.  We also assume
; that an appropriately sized b has been loaded into dz.  We solve Ax = b and
; leave the answer in x.

  (declare (xargs :stobjs (dz)))
  (let* ((dim (dim dz))
         (dz (run-b-program (b-program dz) dz)))
    (declare (type (signed-byte 60) dim))
    (dz-phase21 (- dim 1) (top-row dz) dim dz))))

; =================================================================
; Debugging Aids

; Warren and Vivek:

; This section contains some debugging tools.  These functions are not called
; in the solver, but I sometimes modify the source code to use them as needed.
; You should just ignore all this.

(skip-proofs
(defun show-row (index i dz)
  (declare (xargs :stobjs (dz)))
  (cond
   ((>= i (dim dz)) nil)
   ((d= (ai (+ (index->address index dz) i) dz)
        (d0))
    (append (make-list (zi (+ (index->address index dz) i) dz)
                       :initial-element (d0))
            (show-row index (+ i (zi (+ (index->address index dz) i) dz)) dz)))
   (t (cons (ai (+ (index->address index dz) i) dz)
            (show-row index (+ i 1) dz))))))

(skip-proofs
(defun show-a (index dz)
  (declare (xargs :stobjs (dz)))
  (cond
   ((>= index (dim dz)) nil)
   (t (cons (show-row index 0 dz)
            (show-a (+ index 1) dz))))))

(skip-proofs
(defun show-b1 (i dz)
  (declare (xargs :stobjs (dz)))
  (cond ((>= i (dim*dim dz)) nil)
        (t (cons (bi i dz) (show-b1 (+ 1 i) dz))))))

(skip-proofs
(defun show-b (dz)
  (declare (xargs :stobjs (dz)))
  (show-b1 0 dz)))

(skip-proofs
(defun show-z1 (i dz)
  (declare (xargs :stobjs (dz)))
  (cond ((>= i (dim*dim dz)) nil)
        (t (cons (zi i dz) (show-z1 (+ 1 i) dz))))))

(skip-proofs
(defun show-z (dz)
  (declare (xargs :stobjs (dz)))
  (show-z1 0 dz)))

(skip-proofs
(defun show-meta-data1 (i dz)
  (declare (xargs :stobjs (dz)))
  (cond
   ((>= i (dim dz))
    nil)
   (t (cons (list i
                  (show-row i 0 dz)
                  (nx-rowi i dz)
                  (nx-blki i dz))
            (show-meta-data1 (+ 1 i) dz))))))

(skip-proofs
(defun show-meta-data (dz)
  (declare (xargs :stobjs (dz)))
  (cons (list '(top-row dz) (top-row dz) )
        (cons '(i data nx-rowi nx-blki)
              (show-meta-data1 0 dz)))))

(skip-proofs
(defun show-block1 (row-index dz)
  (declare (xargs :stobjs (dz)))
  (cond
   ((equal row-index -1) nil)
   (t (cons row-index
            (show-block1 (nx-rowi row-index dz) dz))))))

(skip-proofs
(defun show-block (blk-index dz)

; We know blk-index is non-empty, i.e., is not -1.  We build the human readable
; block corresponding to blk-index.  Note that blk-index is also the naive row address
; of the first row in the block.  So in the call of show-block1 below we pass
; blk-index as a naive row address.

  (declare (xargs :stobjs (dz)))
  `(block
     (zcnt ,(zcnt-of-address (index->address blk-index dz) dz))
     (coef ,(abs (lead-coef-of-address (index->address blk-index dz) dz)))
     (rows ,@(show-block1 blk-index dz)))))

(skip-proofs
(defun show-blocks (blk-index dz)
  (declare (xargs :stobjs (dz)))
  (cond
   ((equal blk-index -1) nil)
   (t (cons (show-block blk-index dz)
            (show-blocks (nx-blki blk-index dz) dz))))))

(skip-proofs
(defun show-rows-in-blocks1 (row-index blk-index dz)
  (declare (xargs :stobjs (dz)
                  :measure (acl2-count blk-index) ; TOTALLY BOGUS!
                  ))

  (cond
   ((equal row-index -1)
    (cond ((equal (nx-blki blk-index dz) -1)
           nil)
          (t (show-rows-in-blocks1 (nx-blki blk-index dz)
                                   (nx-blki blk-index dz)
                                   dz))))
   (t (cons (show-row row-index 0 dz)
            (show-rows-in-blocks1 (nx-rowi row-index dz)
                                  blk-index dz))))))

(skip-proofs
(defun show-rows-in-blocks (dz)
  (declare (xargs :stobjs (dz)))
  (show-rows-in-blocks1 (top-row dz) (top-row dz) dz)))

; -----------------------------------------------------------------
; Now we define slow but correct list-based matrix operations for checking
; results...  This is used for computing Ax.

(skip-proofs
(defun all-nilsp (lst)
  (cond ((endp lst) t)
        (t (and (null (car lst))
                (all-nilsp (cdr lst)))))))

(skip-proofs
(defun cdr-all (A)
  (cond ((endp A) nil)
        (t (cons (cdr (car A))
                 (cdr-all (cdr A)))))))

(skip-proofs
(defun transpose (A)
  (cond
   ((all-nilsp A) nil)
   (t (cons (strip-cars A)
            (transpose (cdr-all A)))))))

(skip-proofs
(defun dot-product (u v)
  (declare (xargs :verify-guards t))
  (cond
   ((endp u) 0)
   (t (+ (* (car u) (car v))
         (dot-product (cdr u) (cdr v)))))))

(skip-proofs
(defun matrix-matrix-mult2 (u B)
  (cond ((endp B) nil)
        (t (cons (dot-product u (car B))
                 (matrix-matrix-mult2 u (cdr B)))))))

(skip-proofs
(defun matrix-matrix-mult1 (A B)
  (cond ((endp A) nil)
        (t (cons (matrix-matrix-mult2 (car A) B)
                 (matrix-matrix-mult1 (cdr A) B))))))

(skip-proofs
(defun matrix-matrix-mult (A B)
; Both args are list-of-list style matrices of appropriate dimensions, i.e., A
; is n x p and B is p x k, producing an n x k result.
  (matrix-matrix-mult1 A (transpose B))))

(skip-proofs
(defun matrix-vector-mult (A b)

; A is a list-of-list style n x p matrix and b is a vector of length p.  We
; multiply A time b and return a vector of length n.

  (declare (xargs :verify-guards t))
  (cond ((endp A) nil)
        (t (cons (dot-product (car A) b)
                 (matrix-vector-mult (cdr A) b))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; The following code supports SR format and is irrelevant as a guide.

; In the SR (``sparse representation'') format, a contiguous stretch of zeros
; of length k in a row is abbreviated by the singleton list (k).  So an SR row
; or vector consists of a true-list of singletons and/or non-zero numeric data.
; Furthermore, a row or vector ending with a stretch of zeros drops the final
; singleton.  Thus, the LL row (0 0 0 1 2 0 0 0 0) in SR format is ((3) 1 2).
; An nxn SR matrix is a list of n SR rows.

(skip-proofs
(defun SR-to-LL-row (m row zero)
; Convert an SR row to an LL row of length m.
  (cond ((endp row) (make-list m :initial-element zero))
        ((consp (car row))
         (append (make-list (car (car row)) :initial-element zero)
                 (SR-to-LL-row (- m (car (car row))) (cdr row) zero)))
        (t (cons (car row)
                 (SR-to-LL-row (- m 1) (cdr row) zero))))))

(skip-proofs
(defun SR-to-LL-matrix1 (m rows zero)
  (cond ((endp rows) nil)
        (t (cons (SR-to-LL-row m (car rows) zero)
                 (SR-to-LL-matrix1 m (cdr rows) zero))))))

(skip-proofs
(defun SR-to-LL-matrix (matrix zero)
; Convert an SR matrix to an LL matrix.  Zero should be either 0 or 0.0D0
; depending on the type of data in m.
  (SR-to-LL-matrix1 (length matrix) matrix zero)))

; End of SR stuff
; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(skip-proofs
(defun max-discrepancy (prob-no j b A*x relativep Tol max-tuple)

; We compare corresponding components of b and A*x and return a tuple
; describing the largest discrepancy.  Prob-no is some identifier, typically a
; number, indicating which A and b we're dealing with, e.g., the 5th one in a
; list of problems, and j is the number of the current component.  B is the
; tail of the right-hand side vector and A*x is tail of the product of the
; original A with the computed solution x.  Relativep is t or nil indicating
; whether we are maximizing the relative or absolute discrepancy.  When
; maximizing the relative error we ignore components of b that are at or below
; Tol.  Max-tuple is of the form (discrep prob-no j' e d), where discrep is the
; maximum discrepancy seen so far, j' is the number of component of b that is
; maximally out of whack so far, e is that component of b and d is the
; corresponding component of A*x.

  (declare (xargs :verify-guards t))
  (cond
   ((endp b) max-tuple)
   (t (let ((discrep (if relativep
                         (if (d>= (car b) Tol)
                             (abs (/ (- (car b) (car A*x)) (car b)))
                             (car max-tuple))
                         (abs (- (car b) (car A*x))))))
        (max-discrepancy prob-no
                         (i+ j 1)
                         (cdr b) (cdr A*x)
                         relativep Tol
                         (if (d> discrep (car max-tuple))
                             (list discrep prob-no j (car b) (car A*x))
                             max-tuple)))))))

(skip-proofs
(defun solve-and-test-one-A (test-flg prob-no A b-lst Tol dz max-tuple)

; We assume that an A has been loaded into dz and dz-unc-decomp has run
; successfully on it.  In this function, A and every element of b-lst are in LL
; format.  (This is weird: Our loader for A assumes the matrix is in SR format,
; to make loading faster.  But here we use an LL format to make multiplication
; easier as we check the solutions.)  We solve Ax = b for each b in b-lst and
; compute the max discrepancy (or not, if test-flg = nil).

  (declare (xargs :stobjs (dz)))
  (cond
   ((endp b-lst) (mv max-tuple dz))
   (t (let* ((dz (load-LL-vector-into-DZ-b (car b-lst) dz))
             (dz (dz-unc-solve dz)))
        (if (null test-flg)
            (solve-and-test-one-A test-flg
                                  (+ 1 prob-no)
                                  A (cdr b-lst)
                                  Tol dz
                                  max-tuple)
            (let* ((x (extract-soln-as-a-list dz))
                   (A*x (matrix-vector-mult A x))
                   (max-tuple1 (max-discrepancy prob-no 0
                                                (car b-lst)
                                                A*x
                                                (eq test-flg :relative)
                                                Tol
                                                `(,(d0) ,prob-no <j> <e> <d>))))
              (solve-and-test-one-A test-flg (+ 1 prob-no)
                                    A (cdr b-lst)
                                    Tol dz
                                    (if (d> (car max-tuple1) (car max-tuple))
                                        max-tuple1
                                        max-tuple)))))))))
