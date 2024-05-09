(in-package 3bz)
#++
(defconstant +static-huffman-tree+ (if (boundp '+static-huffman-tree+)
                                       +static-huffman-tree+
                                       (make-huffman-tree)))
#++
(build-tree +static-huffman-tree+ *fixed-lit/length-table* *fixed-dist-table*)
#++(dump-tree +static-huffman-tree+)
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar %static-huffman-tree/len% (make-huffman-tree))
  (defvar %static-huffman-tree/dist% (make-huffman-tree) )

  (build-trees %static-huffman-tree/len%
               %static-huffman-tree/dist%
               *fixed-lit/length-table* *fixed-dist-table*)

  (defconstant +static-huffman-tree/len+ (eval
                                          '(if (boundp '+static-huffman-tree/len+)
                                              +static-huffman-tree/len+
                                            %static-huffman-tree/len%)))
  (defconstant +static-huffman-tree/dist+ (eval
                                           '(if (boundp '+static-huffman-tree/dist+)
                                             +static-huffman-tree/dist+
                                             %static-huffman-tree/dist%))))
#-ccl
(eval-when (:compile-toplevel :load-toplevel :execute)
  (alexandria:define-constant +static-huffman-trees+
      (cons +static-huffman-tree/len+ +static-huffman-tree/dist+)
    :test 'equalp))
#+ccl
(defparameter +static-huffman-trees+
      (cons +static-huffman-tree/len+ +static-huffman-tree/dist+))

