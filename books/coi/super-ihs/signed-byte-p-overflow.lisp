(in-package "ACL2")

(local
 (encapsulate
     ()
     
(encapsulate
    (
     ((local-ifloor * *) => *)
     ((local-imod * *) => *)
     ((local-expt2 *) => *)
     ((local-logcar *) => *)
     ((local-loghead * *) => *)
     ((local-logtail * *) => *)
     ((local-logapp * * *) => *)
     )

  (local
   (encapsulate
       ()

     (defun local-ifloor (i j)
       (floor (ifix i) (ifix j)))
     
     (defun local-imod (i j)
       (mod (ifix i) (ifix j)))
     
     (defun local-expt2 (n)
       (expt 2 (nfix n)))
     
     (defun local-logcar (i)
       (local-imod i 2))
     
     (defun local-loghead (size i)
       (local-imod i (local-expt2 size)))
     
     (defun local-logtail (pos i)
       (local-ifloor i (local-expt2 pos)))

     (defun local-logapp (size i j) 
       (let ((j (ifix j)))
	 (+ (local-loghead size i) (* j (local-expt2 size)))))

     ))

  (defthm local-ifloor-defn
    (equal (local-ifloor i j)
	   (floor (ifix i) (ifix j))))
  
  (defthm local-imod-defn 
    (equal (local-imod i j)
	   (mod (ifix i) (ifix j))))
  
  (defthm local-expt2-defn 
    (equal (local-expt2 n)
	   (expt 2 (nfix n))))
  
  (defthm local-logcar-defn
    (equal (local-logcar i)
	   (local-imod i 2)))
  
  (defthm local-loghead-defn
    (equal (local-loghead size i)
	   (local-imod i (local-expt2 size))))
  
  (defthm local-logtail-defn
    (equal (local-logtail size i)
	   (local-ifloor i (local-expt2 size))))
  
  (defthm local-logapp-defn
    (equal (local-logapp size i j) 
	   (let ((j (ifix j)))
	     (+ (local-loghead size i) (* j (local-expt2 size))))))
  
  )

(encapsulate
    ()

  (local
   (encapsulate
       ()
     
     (include-book "arithmetic-3/bind-free/top" :dir :system)
     
     (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
     
     (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
						   HIST PSPV)))
     

     ))

  (defthm local-special-32-bit-overflow-reduction
    (implies
     (and
      (syntaxp (quotep c))
      (equal (local-loghead 16 c) 0)
      (integerp c)
      (integerp x))
     (equal (signed-byte-p 32 (+ c x))
	    (signed-byte-p 16 (+ (local-logtail 16 c) (local-logtail 16 x))))))
  
     )


))

(include-book "ihs/ihs-lemmas" :dir :system)

(defthm special-32-bit-overflow-reduction
  (implies
   (and
    (syntaxp (quotep c))
    (equal (loghead 16 c) 0)
    (integerp c)
    (integerp x))
   (equal (signed-byte-p 32 (+ c x))
	  (signed-byte-p 16 (+ (logtail 16 c) (logtail 16 x)))))
  :hints (("Goal" :in-theory `(logapp loghead logtail logcar expt2 imod ifloor)
	   :use (:functional-instance
		 local-special-32-bit-overflow-reduction
		 (local-ifloor  ifloor)
		 (local-imod    imod)
		 (local-expt2   expt2)
		 (local-logcar  logcar)
		 (local-loghead loghead)
		 (local-logtail logtail)
		 (local-logapp  logapp)))))

