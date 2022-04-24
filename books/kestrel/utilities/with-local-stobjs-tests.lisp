; Tests of with-local-stobjs
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "with-local-stobjs")

(defstobj one (x :type integer :initially 0))
(defstobj two (y :type integer :initially 0))
(defstobj three (v :type integer :initially 0))

;; Just a test of with-local-stobj itself:
(defun foo (x)
  (with-local-stobj one
    (mv-let (res one)
      (let ((one (update-x 17 one)))
        (mv (* 2 x) one))
      res ; no mention of ONE
      )))

;; Test of with-local-stobjs with a single stobj.  So, much like foo above.
(defun foo2 (x)
  (with-local-stobjs (one)
    (mv-let (res one)
      (let ((one (update-x 17 one)))
        (mv (* 2 x) one))
      res ; no mention of ONE
      )))

;; Two nested calls of with-local-stobj:
(defun bar (x)
  (with-local-stobj one
    (mv-let (res one)
      ;; Returns res and ONE:
      (with-local-stobj two
        (mv-let (res one two)
          ;; Returns red and ONE and TWO:
          (let* ((one (update-x 17 one))
                 (two (update-y 19 two)))
            (mv (* 2 x) one two))
          (mv res one) ; no mention of TWO
          ))
      res ; no mention of ONE or TWO
      )))

;; Test of with-local-stobjs with 2 stobjs.
;; Much like bar, above.
(defun bars (x)
  (with-local-stobjs
   (one two)
   (mv-let (res one two)
     ;; Returns ONE and TWO:
     (let* ((one (update-x 17 one))
            (two (update-y 19 two)))
       (mv (* 2 x) one two))
     res ; no mention of ONE or TWO:
     )))

;; Three nested calls of with-local-stobj:
(defun baz (x)
  (with-local-stobj one
    (mv-let (res one ig)
      ;; Returns res and ONE:
      (with-local-stobj two
        (mv-let (res one two ig)
          ;; Returns res and TWO
          (with-local-stobj three
            (mv-let (res one two three ig)
              ;; Returns res and ONE and TWO and THREE:
              (let* ((one (update-x 17 one))
                     (two (update-y 19 two))
                     (three (update-v 21 three)))
                (mv (* 2 x) one two three 'ignored-thing))
              ;; (declare (ignore ig)) ; could put the ignore here but that would be harder
              (mv res one two ig) ; no mention of THREE
              ))
          (mv res one ig) ; no mention of TWO
          ))
      (declare (ignore ig))
      res ; no mention of any stobjs
      )))

;; Test with 3 stobjs.
;; Much like baz, above.
(defun baz2 (x)
  (with-local-stobjs
   (one two three)
   (mv-let (res one two three ig)
     ;; Returns ONE and TWO and THREE:
     (let* ((one (update-x 17 one))
            (two (update-y 19 two))
            (three (update-v 21 three)))
       (mv (* 2 x) one two three 'ignored-thing))
     (declare (ignore ig))
     res ; no mentions of stobjs
     )))
