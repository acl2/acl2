#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

#||
;; Jared added this comment to avoid having Centaur's cluster kill this book
;; for using too much memory.  See cert.pl for details.

(set-max-mem (* 6 (expt 2 30)))

;; Then Sol split this out into a separate book.
||#

(include-book "defung")

#+joe
(defmacro hide-local (&rest args)
  `(encapsulate
       ()
     (local
      (encapsulate
	  ()
	,@args))))

(defmacro hide-local (&rest args)
  `(local
    (encapsulate
	()
      ,@args)))


(hide-local
 (def::ung one-4 (n)
   (if (zp n) 1
     (let ((n (if (< n 7) (1+ n) (1- n))))
       (let ((n (one-4 n)))
	 (let ((n (if (> n 10) (1- n) (1+ n))))
	   (let ((n (if (< (if (< (one-4 n) n) (one-4 (1+ n)) (1+ (one-4 n))) n) (one-4 (1+ n)) (one-4 (1- n)))))
	     (one-4 n)))))))
 )
