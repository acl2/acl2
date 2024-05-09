(in-package :cl-user)
(defpackage xsubseq-test
  (:use :cl
        :xsubseq
        :prove))
(in-package :xsubseq-test)

(plan nil)

(defparameter *data1*
  (make-array 3 :element-type '(unsigned-byte 8) :initial-contents '(1 2 3)))
(defparameter *data2*
  (make-array 3 :element-type '(unsigned-byte 8) :initial-contents '(11 22 33)))

(defparameter *str1* "Hello")
(defparameter *str2* "World")

(subtest "xsubseq"
  (is-type (xsubseq *data1* 0 1) 'xsubseq
           "Can create a new XSUBSEQ")
  (is-type (xsubseq *data1* 0) 'xsubseq
           "Can omit END")
  (is-type (xsubseq *str1* 0 1) 'xsubseq
           "Can create a new XSUBSEQ (string)")
  (is-type (xsubseq *str2* 0) 'xsubseq
           "Can omit END (string)"))

(subtest "xnconc"
  (is-type (xnconc (xsubseq *data1* 0 1))
           'xsubseq
           "1 XSUBSEQ")
  (is-type (xnconc (xsubseq *data1* 0 1)
                   (xsubseq *data2* 2))
           'concatenated-xsubseqs
           "2 XSUBSEQs")
  (is-type (xnconc (xsubseq *data1* 0 1)
                   (xsubseq *data2* 2)
                   (xsubseq *data1* 1))
           'concatenated-xsubseqs
           "3 XSUBSEQs")
  (is-type (xnconc (xnconc (xsubseq *data1* 0 1)
                           (xsubseq *data2* 2))
                   (xsubseq *data1* 1))
           'concatenated-xsubseqs
           "Concat a CONCATENATED-XSUBSEQS and a XSUBSEQ")
  (is-type (xnconc (xnconc (xsubseq *data1* 0 1)
                           (xsubseq *data2* 2))
                   (xnconc (xsubseq *data1* 0 1)
                           (xsubseq *data2* 2)))
           'concatenated-xsubseqs
           "Concat 2 CONCATENATED-XSUBSEQSs"))

(subtest "coerce-to-sequence"
  (is (coerce-to-sequence (xsubseq *data1* 0 2))
      #(1 2)
      :test #'equalp
      "XSUBSEQ")
  (is (coerce-to-sequence (xnconc (xsubseq *data1* 0 1)
                                  (xsubseq *data2* 2)
                                  (xsubseq *data1* 1)))
      #(1 33 2 3)
      :test #'equalp
      "CONCATENATED-XSUBSEQ")
  (is (coerce-to-sequence (xsubseq *str1* 0 2))
      "He"
      :test #'equal
      "XSUBSEQ (string)")
  (is (coerce-to-sequence (xnconc (xsubseq *str1* 0 1)
                                  (xsubseq *str2* 2)
                                  (xsubseq *str1* 1)))
      "Hrldello"
      :test #'equal
      "CONCATENATED-XSUBSEQ (string)"))

(subtest "coerce-to-string"
  (is (coerce-to-string (xnconc (xsubseq *data2* 2)
                                (xsubseq *data2* 2)))
      "!!"
      :test #'equal)
  (is (coerce-to-string (xnconc (xsubseq *str1* 0 1)
                                (xsubseq *str2* 2)))
      "Hrld"
      :test #'equal))

(subtest "xlength"
  (is (xlength (xsubseq *data1* 0 1)) 1)
  (is (xlength (xsubseq *data1* 2)) 1)
  (is (xlength (xnconc (xsubseq *data1* 0 1)
                       (xsubseq *data2* 2)))
      2))

(subtest "with-xsubseqs"
  (is (with-xsubseqs (result)
        (xnconcf result (xsubseq *data1* 0 1))
        (xnconcf result (xsubseq *data2* 2))
        (xnconcf result (xsubseq *data1* 1)))
      #(1 33 2 3)
      :test #'equalp)
  (is (with-xsubseqs (result :initial-value (xsubseq *data1* 0))
        (xnconcf result (xsubseq *data2* 2))
        (xnconcf result (xsubseq *data1* 1)))
      #(1 2 3 33 2 3)
      :test #'equalp))

(finalize)
