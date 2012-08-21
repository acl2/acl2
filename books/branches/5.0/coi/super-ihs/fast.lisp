#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;; This book, fast.lisp, contains fast versions of some super-ihs functions
;; that are fast to execute.  I'm letting this be demand driven, adding to it
;; as needed.

(include-book "super-ihs")

(defmacro the-usb (size x) 
  `(the (unsigned-byte ,size) ,x))

(defmacro the-sb (size x) 
  `(the (signed-byte ,size) ,x))

(defund loghead-30-exec (i)
  (declare (type (unsigned-byte 31) i))
  (the-usb 31 (logand 1073741823 i)))

(defthm loghead-30-exec-rewrite
  (equal (loghead-30-exec i)
         (loghead 30 i))
  :hints (("Goal" :in-theory (enable loghead-30-exec))))
           
(defund logbitp-30-exec (j)
  (declare (type (unsigned-byte 31) j))
  (not (equal 0 (logand 1073741824 j))))

(defthm logbitp-30-exec-rewrite
  (equal (logbitp-30-exec i)
         (logbitp 30 i))
  :hints (("Goal" :cases ((integerp i))
           :in-theory (enable logbitp-30-exec))))

;bzo I think this version doesn't do the chop that logapp does.  Make a
;version that does do the chop (and that won't need the (unsigned-byte-p 31 x)
;hyp to be equal to (logext 31 x)?
;
;bzo inline the function calls here?
(defund logext-31-exec (x)
  (declare (type (unsigned-byte 31) x))
  (the-sb 31 (if (not (equal 0 (logand 1073741824 x))) ;(logbitp-30-exec x)
                 (the-sb 31 (+ -1073741824 (the-usb 30 (logand 1073741823 x) ;(loghead-30-exec x)
                                                    ))) ;(logapp 30 x -1);
               x)))

(defthm logext-31-exec-rw
  (implies (unsigned-byte-p 31 x)
           (equal (logext-31-exec x)
                  (logext 31 x)))
  :hints (("Goal" :in-theory (enable LOGEXT logext-31-exec))))
