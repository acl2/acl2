;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Trivia.lisp
; Copyright reserved by SRC
; Author  Jun Sawada, University of Texas at Austin
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;'
(in-package "ACL2")

;; Jared: changing this to an include of an identical book
(include-book "workshops/1999/pipeline/trivia" :dir :system)

;; (include-book "../../../../../../data-structures/array1")
;; (include-book "../../../../../../arithmetic/top")

;; (deflabel begin-trivia)

;; (defmacro quoted-constant-p (x)
;;   `(and (consp ,x) (equal (car ,x) 'quote)))

;; (defthm append-nil
;;     (implies (true-listp x)
;; 	      (equal (append x nil) x))
;;   :hints (("Goal" :in-theory (enable binary-append))))

;; (defun natural-induction (i)
;;     (if (zp i) t
;; 	(natural-induction (1- i))))

;; ;; in data-structures/list-defthms
;; ;; (defthm car-nthcdr
;; ;;     (equal (car (nthcdr idx lst)) (nth idx lst)))

;; (defthm cdr-nthcdr
;;     (implies (and (integerp idx) (<= 0 idx))
;; 	     (equal (cdr (nthcdr idx lst)) (nthcdr (+ 1 idx) lst))))


;; (in-theory (disable length))

;; (in-theory (disable array1p compress1 default dimensions header
;; 		    aref1 aset1 maximum-length))

;; (defthm array1p-module-type
;;   (implies
;;    (array1p name l)
;;    (and (symbolp name)
;; 	(alistp l)
;; 	(consp (header name l))
;; 	(consp (dimensions name l))
;; 	(true-listp (dimensions name l))
;; 	(integerp (car (dimensions name l)))
;; 	(<= 0 (car (dimensions name l)))
;; 	(integerp (maximum-length name l))
;; 	(<= 0 (maximum-length name l))))
;;   :hints (("Goal" :in-theory (enable array1p header default dimensions
;; 				     maximum-length)))
;;   :rule-classes
;;   ((:type-prescription :corollary
;; 	         (implies
;; 		  (array1p name l)
;; 		  (and (consp (header name l)))))
;;    (:type-prescription :corollary
;; 	         (implies
;; 		  (array1p name l)
;; 		  (and (consp (dimensions name l))
;; 		       (true-listp (dimensions name l)))))
;;    (:type-prescription :corollary
;; 	         (implies
;; 		  (array1p name l)
;; 		  (and (integerp (car (dimensions name l)))
;; 		       (<= 0 (car (dimensions name l))))))
;;    (:type-prescription :corollary
;; 	         (implies
;; 		  (array1p name l)
;; 		  (and (integerp (maximum-length name l))
;; 		       (<= 0 (maximum-length name l)))))))


;; (local
;; (defthm compress11-empty-array
;;     (implies (and (integerp n) (>= n 0))
;; 	     (equal (compress11 name (list (cons :header info)) n dim default)
;; 		    nil))
;;   :hints (("Goal" :In-theory (enable compress11)))))


;; (defthm compress1-empty-array
;;      (equal (compress1 tag (list (cons :header x)))
;; 	    (list (cons :header x)))
;;    :hints (("Goal" :in-theory (enable compress1 compress11
;; 				      header default))))

;; (defthm array1p-cons-with-dimensions
;;     (implies (and (array1p tag array)
;; 		  (integerp index)
;; 		  (>= index 0)
;; 		  (> (car (dimensions tag array)) index))
;; 	     (array1p tag (cons (cons index val) array)))
;;   :hints (("goal" :in-theory (enable dimensions header))))

