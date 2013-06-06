#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "syntaxp")
(include-book "misc/total-order" :dir :system)

(defun subterm-rec (x y)
  (declare (type t x y))
  (if (consp y)
      (let ((term (car y)))
	(or (equal x term)
	    (and (consp term)
		 (subterm-rec x (cdr term)))
	    (subterm-rec x (cdr y))))
    nil))

(defun subterm-p (x y)
  (declare (type t x y))
  (and (consp y)
       (subterm-rec x (cdr y))))

;; We rewrite larger symbols into smaller symbols and smaller (non
;; constant) terms into larger terms.

;; What about (equiv ram (goo ram)) ?  - presumably we would want to
;; eliminate (goo ram) ?  Which is to say, if one is a subterm of the
;; other, prehaps we should collapse the larger term into the smaller
;; term ?

(defun good-rewrite-order (x y)
  (declare (xargs :mode :program))
  (if (and (symbolp x)
	   (symbolp y))
      (smaller-term y x)
    (if (quotep x)
	(and (quotep y)
	     (<< (cadr y) (cadr x)))
      (or (quotep y)
	  (and (smaller-term x y)
	       (not (subterm-p x y)))
	  (subterm-p y x)))))
  
