; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The original veresion of this book includes MUCH faster after mid-February
; 2021.  With *big-size-def* reduced to 10000, I observed the include-book time
; to be 0.4 seconds after mid-February 2021 but 10.24 seconds before then.  The
; discrepancy disappeared when the local form below was included.

; Below, "big-def" comes from the filename.

(in-package "ACL2")

;(local (defun h (x) x))

(defun f (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) nil)
        (t (hons (make-list n :initial-element n)
                 (f (1- n))))))

(make-event `(defun big-def1 ()
               (declare (xargs :guard t))
               ',(f 1000)))

(make-event `(defconst *big-def2*
               ',(f 1000)))

(defconst *big-size-def* 10000000)

(defconst *big-def1-list*
  (make-list *big-size-def* :initial-element (big-def1)))

(defun big-def1-list-fn ()
  (make-list *big-size-def* :initial-element (big-def1)))

(defconst *big-def1-list-fn*
  (big-def1-list-fn))

(defconst *big-def2-list*
  (make-list *big-size-def* :initial-element *big-def2*))

;;; In raw Lisp (CCL, and similarly in at least SBCL and GCL) we get the
;;; following results after including this book.  Presumably the compiler is
;;; doing some sharing of constants within the compiled file, while *big-def2*
;;; is getting its value from the :expansion-alist of the .cert file.

#|
? (hl-hspace-honsp-wrapper (car *big-def1-list*))
NIL
? (hl-hspace-honsp-wrapper (car (big-def1-list-fn)))
T
? (hl-hspace-honsp-wrapper (car *big-def1-list-fn*))
NIL
? (hl-hspace-honsp-wrapper (car *big-def2-list*))
T
? 
|#

;;; Because of that, only the second of the following three equalities computes
;;; in a reasonable amount of time when including this book.  (Certification is
;;; not a problem if if :on-skip-proofs t is included in all three.)

(assert-event (equal *big-def1-list* *big-def2-list*))

(assert-event (equal (big-def1-list-fn) *big-def2-list*)
              :on-skip-proofs t)

(assert-event (equal *big-def1-list-fn* *big-def2-list*))
