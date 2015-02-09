(in-package "VL2014")
(progn

 (defun vl-printedlist->string (x)

   ;; Optimized PS->STRING routine.  We're going to build the return string in
   ;; two passes.  In the first pass we'll determine how big of an array we
   ;; need.  In the second, we'll fill in its characters with the reverse of
   ;; the elems.

   (let* ((size  (vl-printedlist-length x 0)))
     (unless (typep size 'fixnum)
       (er hard? 'vl-ps->string-fn
           "Printed list will will be longer than a fixnum (~x0).  You don't ~
            actually want to turn it into a string, I think." size))

     ;; Since the elems are in reverse order, we'll work backwards from the end
     ;; of the array.
     (let* ((ret (make-array size :element-type 'character))
            (i   (the fixnum (- (the fixnum size) 1))))
       (declare (type fixnum i))
       (loop while (consp x)
             do
             (let ((elem (car x)))
               (if (characterp elem)
                   (progn (setf (schar ret i) elem)
                          (decf i))

                 ;; For strings, things are trickier because the characters of
                 ;; the string *are* in the right order.  It's very helpful to
                 ;; think of a concrete example.  Suppose we do:
                 ;;
                 ;;   print #\A
                 ;;   print #\B
                 ;;   print #\C
                 ;;   print "abc"
                 ;;   print #\D
                 ;;   print #\E
                 ;;
                 ;; Then the rchars we'll have are (#\E #\D "abc" #\C #\B #\A).
                 ;; The ret array is 8 entries long and we've already set
                 ;;   ret[7] = #\E
                 ;;   ret[6] = #\D
                 ;; So we now want to set
                 ;;   ret[5] = #\c
                 ;;   ret[4] = #\b
                 ;;   ret[3] = #\a
                 ;;
                 ;; I think it's easiest to just go down from the end of the
                 ;; string so we can (decf i) like before.
                 (loop for j fixnum from (- (length (the string elem)) 1) downto 0 do
                       (setf (schar ret i) (schar elem j))
                       (decf i))))
             (setq x (cdr x)))
       ret))))
