(in-package 3bz)
#++
(let ((max (1- (expt 2 29))))
  (flet ((s (n)
           (+ (* (1+ n) 65520)
              (* (/ (* n (1+ n)) 2) 255))))
    (loop with n1 = 0
          with n = (/ max 2)
          with n2 = max
          when (>= (s n) max)
            do (psetf n (floor (+ n n1) 2)
                      n2 n)
          else do (psetf n (floor (+ n n2) 2)
                         n1 n)
          until (< (- n2 n1) 2)
          finally (return n1))))

(defun adler32/ub64 (buf end s1 s2)
  (declare (type octet-vector buf)
           (type (unsigned-byte 16) s1 s2)
           (type fixnum end)
           (optimize speed))
  ;; with 64bit accumulators, we need to do the MOD every 380368439
  ;; adds. formula = (+ (* (1+ n) 65520) (* (/ (* n (1+ n)) 2) 255))
  (let* ((unroll #1=#.+adler32-unroll+)
         (chunk-size ;(* unroll (floor 5552 unroll))
           (* unroll (floor 380368439 unroll)))
         (s1 s1)
         (s2 s2))
    (declare (type (unsigned-byte 64) s1 s2)
             (fixnum chunk-size))
    (assert (<= end (length buf)))
    (macrolet ((a (i)
                 `(progn
                    (setf s1 (ub64+ s1
                                    (locally
                                        (declare (optimize (safety 0)))
                                      (aref buf (the fixnum ,i)))))
                    (setf s2 (ub64+ s2 s1))))
               (unroll (n)
                 `(progn
                    ,@(loop for x below n
                            collect `(a (fixnum+ i ,x))))))
      (loop with i of-type fixnum = 0
            for rem fixnum = (the fixnum (- end i))
            for c fixnum = (fixnum+ i (min (* #1# (floor rem #1#))
                                           chunk-size))
            while (> rem #1#)
            do (loop while (< i c)
                     do (unroll #1#)
                        (locally (declare (optimize (safety 0)))
                          (setf i  (fixnum+ i #1#))))
               (setf s1 (mod s1 +adler32-prime+)
                     s2 (mod s2 +adler32-prime+))
            finally (progn
                      (assert (<= i end))
                      (loop for i fixnum from i below end
                            do (a i))))
      (setf s1 (mod s1 +adler32-prime+)
            s2 (mod s2 +adler32-prime+)))
    (locally (declare (type (unsigned-byte 16) s1 s2))
      (values s1 s2))))

(progn
  (eval-when (:compile-toplevel :load-toplevel :execute)
    (defconstant +accumulate-count+
      (let ((max most-positive-fixnum))
        (flet ((s (n)
                 (+ (* (1+ n) 65520)
                    (* (/ (* n (1+ n)) 2) 255))))
          (loop with n1 = 0
                with n = (/ max 2)
                with n2 = max
                when (>= (s n) max)
                  do (psetf n (floor (+ n n1) 2)
                            n2 n)
                else do (psetf n (floor (+ n n2) 2)
                            n1 n)
                until (< (- n2 n1) 2)
                finally (return n1))))))
  ;; need at least 20 or so bits of accumulator, and add a few more so
  ;; we can unroll
  (assert (> +accumulate-count+ 100))
 (defun adler32/fixnum (buf end s1 s2)
   (declare (type octet-vector buf)
            (type (unsigned-byte 16) s1 s2)
            (type non-negative-fixnum end)
            (optimize speed))
   (let* ((unroll #1=#.+adler32-unroll+)
          (chunk-size
            (* unroll (floor +accumulate-count+ unroll)))
          (s1 s1)
          (s2 s2))
     (declare (type non-negative-fixnum s1 s2 chunk-size))
     (assert (<= end (length buf)))
     (macrolet ((a (i)
                  `(progn
                    (setf s1 (the fixnum (+ s1
                                            (the octet (aref buf (the fixnum ,i))))))
                    (setf s2 (the fixnum (+ s2 s1)))))
                (unroll (n)
                  `(progn
                     ,@(loop for x below n
                             collect `(a (+ i ,x))))))
       (loop with i of-type non-negative-fixnum = 0
             for rem fixnum = (the fixnum (- end i))
             for c fixnum = (the fixnum (+ i
                                           (the fixnum
                                                (min (* #1# (floor rem #1#))
                                                     chunk-size))))
             while (> rem #1#)
             do (loop while (< i c)
                      do (unroll #1#)
                         (locally (declare (optimize (safety 0)))
                           (setf i (the fixnum (+ i #1#)))))
                (setf s1 (mod s1 +adler32-prime+)
                      s2 (mod s2 +adler32-prime+))
             finally (progn
                       (assert (<= i end))
                       (loop for i fixnum from i below end
                             do (a i))))
       (setf s1 (mod s1 +adler32-prime+)
             s2 (mod s2 +adler32-prime+)))
     (locally (declare (type (unsigned-byte 16) s1 s2))
       (values s1 s2)))))

(defun adler32/ub32 (buf end s1 s2)
  (declare (type octet-vector buf)
           (type (unsigned-byte 16) s1 s2)
           (type fixnum end)
           (optimize speed ))
  ;; with 32bit accumulators, we need to do the MOD every 5552 adds.
  (let* ((unroll #1=#.+adler32-unroll+)
         (chunk-size (* unroll (floor 5552 unroll)))
         (s1 s1)
         (s2 s2))
    (declare (type (unsigned-byte 32) s1 s2))
    (assert (<= end (length buf)))
    (macrolet ((a (i)
                 `(progn
                    (setf s1 (the (unsigned-byte 32) (+ s1 (aref buf ,i))))
                    (setf s2 (the (unsigned-byte 32) (+ s2 s1)))))
               (unroll (n)
                 `(progn
                    ,@(loop for x below n
                            collect `(a (+ i ,x))))))
      (loop with i fixnum = 0
            while (> (- end i) #1#)
            for c fixnum = (+ i (min (* #1# (floor (- end i) #1#))
                                      chunk-size))
            do (loop while (< i c)
                     do (unroll #1#)
                        (locally (declare (optimize (safety 0)))
                          (incf i #1#)))
               (setf s1 (mod s1 +adler32-prime+)
                     s2 (mod s2 +adler32-prime+))
            finally (progn
                      (assert (<= i end))
                      (loop for i from i below end
                            do (a i))))
      (setf s1 (mod s1 +adler32-prime+)
            s2 (mod s2 +adler32-prime+)))
    (locally (declare (type (unsigned-byte 16) s1 s2))
      (values s1 s2))))

(declaim (inline adler32))
(defun adler32 (buf end s1 s2)
  #+#.(3bz::use-adler32 :ub64)
  (adler32/ub64 buf end s1 s2)
  #+#.(3bz::use-adler32 :fixnum)
  (adler32/fixnum buf end s1 s2)
  #+#.(3bz::use-adler32 :ub32)
  (adler32/ub32 buf end s1 s2))


(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun generate-crc32-table ()
    (let ((table (make-array 256 :element-type '(unsigned-byte 32))))
      (loop for n below (length table)
            do (setf (aref table n)
                     (let ((c n))
                       (loop for k below 8
                             if (oddp c)
                               do (setf c (logxor #xedb88320 (ash c -1)))
                             else
                               do (setf c (ash c -1)))
                       c)))
      table)))

(declaim (type (simple-array (unsigned-byte 32) (256)) +crc32/table+))
(alexandria:define-constant +crc32/table+
    (generate-crc32-table) :test 'equalp)


(defun crc32/table (buf end crc)
  (declare (type octet-vector buf)
           (type fixnum end)
           (type (unsigned-byte 32) crc)
           (optimize speed))
  (let ((crc (logxor crc #xffffffff)))
    (declare (type (unsigned-byte 32) crc))
    (loop for b across buf
          repeat end
          do (setf crc
                   (logxor (ldb (byte 24 8) crc)
                           (aref +crc32/table+
                                 (ldb (byte 8 0)
                                      (logxor crc b))))))
    (logxor crc #xffffffff)))
