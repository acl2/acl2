; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Warning: Keep this book in sync with :DOC stobj-table.

; This book provides a stobj-table as a single field, tbl, of a stobj,
; stobj-table.  Because tbl is a single field, it is actually the entire stobj
; in raw Lisp; so there is no indirection through stobj-table to get to its tbl
; field.

; See books/system/tests/stobj-table-tests-input.lsp for tests of stobj-tables.
; Output from LDing that file may be found in that same directory, file
; stobj-table-tests-log.txt.  But some basic examples are below.

(in-package "ACL2")

(defstobj stobj-table (tbl :type (stobj-table)))

; Here are a few tests, all local, that illustrate reading and writing of
; stobj-tables.

(local (progn

(defstobj st1 fld1)

(defun update-st1-in-tbl (val stobj-table)
  (declare (xargs :stobjs stobj-table))
  (stobj-let ((st1 (tbl-get 'st1 stobj-table (create-st1)))) ; bindings
             (st1)                 ; producer variable
             (update-fld1 val st1) ; producer
             stobj-table           ; consumer
             ))
             
(defun read-st1-in-tbl1 (stobj-table)
  (declare (xargs :stobjs stobj-table))
  (stobj-let ((st1 (tbl-get 'st1 stobj-table (create-st1)))) ; bindings
             (val)      ; producer variable
             (fld1 st1) ; producer
             val        ; consumer
             ))

(assert-event
 (let ((stobj-table (update-st1-in-tbl 3 stobj-table)))
   (mv (equal (read-st1-in-tbl1 stobj-table)
              3)
       stobj-table))
 :stobjs-out '(nil stobj-table))

(defthm read-over-write-st1-in-tbl
  (implies (stobj-tablep stobj-table)
           (let ((stobj-table (update-st1-in-tbl val stobj-table)))
             (equal (read-st1-in-tbl1 stobj-table)
                    val))))

(defstobj st2 fld2)

(defun read-st2-in-tbl (stobj-table)
  (declare (xargs :stobjs stobj-table))
  (stobj-let ((st2 (tbl-get 'st2 stobj-table (create-st2)))) ; bindings
             (val)      ; producer variable
             (fld2 st2) ; producer
             val        ; consumer
             ))

(defthm read-over-write-st2-in-tbl
  (implies (stobj-tablep stobj-table)
           (let ((stobj-table-2 (update-st1-in-tbl val stobj-table)))
             (equal (read-st2-in-tbl stobj-table-2)
                    (read-st2-in-tbl stobj-table)))))
))
