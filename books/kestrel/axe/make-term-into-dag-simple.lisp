; Utilities to make terms into dags
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also make-term-into-dag-simple.lisp

(include-book "make-term-into-dag-array-simple")

;;;
;;; make-term-into-dag-simple
;;;

;; Returns (mv erp dag-or-quotep).  Returns the DAG as a list but uses arrays to do the work.
(defund make-term-into-dag-simple (term)
  (declare (xargs :guard (pseudo-termp term)
                  :guard-hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-simple
                                                        (dag-array-name 'make-term-into-dag-simple-array)
                                                        (dag-parent-array-name 'make-term-into-dag-simple-parent-array))
                                 :in-theory (disable wf-dagp-of-make-term-into-dag-array-simple)))))
  (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (make-term-into-dag-array-simple term 'make-term-into-dag-simple-array 'make-term-into-dag-simple-parent-array )
    (declare (ignore dag-parent-array dag-constant-alist dag-variable-alist))
    (if erp
        (mv erp nil)
      (if (consp nodenum-or-quotep) ; check for quotep
          (mv (erp-nil) nodenum-or-quotep)
        (mv (erp-nil) (array-to-alist 'make-term-into-dag-simple-array dag-array dag-len))))))

;; (local
;;  (defthm equal-of-quote-and-car-when-dargp
;;    (implies (dargp x)
;;             (equal (equal 'quote (car x))
;;                    (consp x)))))

(defthm make-term-into-dag-simple-return-type
  (implies (and (pseudo-termp term)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-simple term))))
           (or (pseudo-dagp (mv-nth 1 (make-term-into-dag-simple term)))
               (myquotep (mv-nth 1 (make-term-into-dag-simple term)))))
  :hints (("Goal" :in-theory (e/d (make-term-into-dag-simple) (natp myquotep)))))

(defthm pseudo-dagp-of-mv-nth-1-of-make-term-into-dag-simple
  (implies (and (pseudo-termp term)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-simple term)))
                (not (myquotep (mv-nth 1 (make-term-into-dag-simple term)))))
           (pseudo-dagp (mv-nth 1 (make-term-into-dag-simple term))))
  :hints (("Goal" :use (:instance make-term-into-dag-simple-return-type)
           :in-theory (disable make-term-into-dag-simple-return-type))))

(defthm <-of-len-of-mv-nth-1-of-make-term-into-dag-simple
  (implies (and (pseudo-termp term)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-simple term)))
                (not (myquotep (mv-nth 1 (make-term-into-dag-simple term)))))
           (< (len (mv-nth 1 (make-term-into-dag-simple term)))
              2147483647))
  :hints (("Goal" :in-theory (enable make-term-into-dag-simple))))

;; Returns (mv erp dag-or-quotep).  Returns the DAG as a list but uses arrays to do the work.
;; This wrapper has no invariant risk because it has a guard of t.
(defund make-term-into-dag-simple-unguarded (term)
  (declare (xargs :guard t))
  (if (not (pseudo-termp term))
      (prog2$ (er hard? 'make-term-into-dag-simple-unguarded "Bad input.")
              (mv (erp-t) nil))
    (make-term-into-dag-simple term)))

;; Returns the dag-or-quotep.  Does not return erp.
(defund make-term-into-dag-simple! (term)
  (declare (xargs :guard (pseudo-termp term)
                  :guard-hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-simple
                                                        (dag-array-name 'make-term-into-dag-simple-array)
                                                        (dag-parent-array-name 'make-term-into-dag-simple-parent-array))
                                 :in-theory (disable wf-dagp-of-make-term-into-dag-array-simple)))))
  (mv-let (erp dag-or-quotep)
    (make-term-into-dag-simple term)
    (if erp
        (er hard? 'make-term-into-dag-simple "Error making term into dag.")
      dag-or-quotep)))
