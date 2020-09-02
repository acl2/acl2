; This book provides "stress tests" for determining whether the parallelism
; library is working well.  The intent is that a person who modifies the ACL2
; mulit-threading interface and the parallelism library can gain moderate
; assurance that their changes did not break plet, pargs, pand, and por by
; certifying this book.  It is also useful for testing release candidates for
; CCL and SBCL.

; Code in all caps is effectively evaluated from a raw lisp prompt.

; To certify this book, you can type:
;
; (certify-book "stress-tests" 0 t :ttags :all)

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)

(defttag raw-lisp-for-parallelism-tests)

(defconst *level-of-pain* 100)

(set-compile-fns t) ; avoid a stack overflow in allegro

;;;;;;;;;;
;; plet ;;
;;;;;;;;;;

(defun plet-test (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (assert$ (equal (plet ((x 3) (y 7)) (+ x y)) 10) t)
         (plet-test (1- n)))))

(assert! (plet-test *level-of-pain*))

#+acl2-par
(progn! (set-raw-mode t)
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (ASSERT (PLET-TEST *LEVEL-OF-PAIN*))
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (SET-RAW-MODE NIL))

;;;;;;;;;;;
;; pargs ;;
;;;;;;;;;;;

(defun pargs-test (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (assert$ (equal (pargs (binary-+ 3 7)) 10) t)
         (pargs-test (1- n)))))

(assert! (pargs-test *level-of-pain*))

#+acl2-par
(progn! (set-raw-mode t)
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (ASSERT (PARGS-TEST *LEVEL-OF-PAIN*))
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (SET-RAW-MODE NIL))

;;;;;;;;;;
;; pand ;;
;;;;;;;;;;

(defun pand-true (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (assert$ (equal (pand 1 2 3 4 5 6 7 8 9 0) t)
                  t)
         (pand-true (1- n)))))

(assert! (pand-true *level-of-pain*))

#+acl2-par
(progn! (set-raw-mode t)
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (ASSERT (PAND-TRUE *LEVEL-OF-PAIN*))
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (SET-RAW-MODE NIL))


(defun pand-false-one (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (assert$ (not (pand 1 2 3 nil 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0)) t)
         (pand-false-one (1- n)))))


(assert! (pand-false-one *level-of-pain*))

#+acl2-par
(progn! (set-raw-mode t)
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (ASSERT (PAND-FALSE-ONE *LEVEL-OF-PAIN*))
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (SET-RAW-MODE NIL))


(defun pand-false-many (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (assert$ (not (pand 1 2 3 nil 5 nil nil nil 9 0 1 2 3 4 5 6 7 8 9)) t)
         (pand-false-many (1- n)))))

(assert! (pand-false-many *level-of-pain*))

#+acl2-par
(progn! (set-raw-mode t)
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (ASSERT (PAND-FALSE-MANY *LEVEL-OF-PAIN*))
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (SET-RAW-MODE NIL))

;;;;;;;;;
;; por ;;
;;;;;;;;;

(defun por-true-many (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (assert$ (por nil nil nil nil nil nil nil 5 6 nil nil nil 9 nil) t)
         (por-true-many (1- n)))))

(assert! (por-true-many *level-of-pain*))

#+acl2-par
(progn! (set-raw-mode t)
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (ASSERT (POR-TRUE-MANY *LEVEL-OF-PAIN*))
        (ASSERT (PARALLELISM-RESOURCES-AVAILABLE))
        (SET-RAW-MODE NIL))
