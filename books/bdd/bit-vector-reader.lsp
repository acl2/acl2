#|
 Load this file into raw Lisp and it will understand bit-vector notation
 #vxxx as illustrated below.  Doing so is completely optional and, strictly
 speaking, not sanctioned as legal ACL2 operation.

  ACL2>(load "/proj/acl2/v2-5/acl2-sources/books/bdd/bit-vector-reader.lisp")
  Loading /proj/acl2/v2-5/acl2-sources/books/bdd/bit-vector-reader.lisp
  Finished loading /proj/acl2/v2-5/acl2-sources/books/bdd/bit-vector-reader.lisp
  T

  ACL2>#v01100
  (NIL NIL T T NIL)

  ACL2>(LP)

  ACL2 Version 2.5.  Level 1.  Cbd "/v/hank/v87/kaufmann/".
  Type :help for help.

  ACL2 !>#v01100
  (NIL NIL T T NIL)
  ACL2 !>
|#

(defun bit-vector-reader (stream subchar arg)
  ;;  We "unread" the vector character, and reread to get a symbol.  Otherwise
  ;;  the number following the vector character might be read as a leading zero
  ;;  of an integer.
  (declare (ignore subchar arg))
  (unread-char #\v stream)
  (let ((symbol (read stream t nil t)))
    ;;  Get rid of the vector character, reverse, and list for NQTHM.
    `(LIST ,@(map 'list #'(lambda (x)
                            (if (equal x #\1)
                                't
                              (if (equal x #\0)
                                  'nil
                                (error "Non-binary digits in --> ~s."
                                       symbol))))
                  (reverse (subseq (symbol-name symbol) 1))))))

(eval-when (load eval)
  (progn
    (set-dispatch-macro-character #\# #\v #'bit-vector-reader)
    (let ((*readtable* *acl2-readtable*))
      (set-dispatch-macro-character #\# #\v #'bit-vector-reader))))
