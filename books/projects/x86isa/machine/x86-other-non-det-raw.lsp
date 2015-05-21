(in-package "X86ISA")

(CCL::open-shared-library *shared-other-non-det-dir-path*)

;; ======================================================================
;; INSTRUCTION: RDRAND
;; ======================================================================

(defun HW_RND_GEN$notinline (size x86)
  (declare (xargs :mode :program :stobjs x86)
           (type (integer 2 8) size))

  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
                   t)
            (equal (f-get-global 'in-verify-flg
                                 ACL2::*the-live-state*)
                   t))
    (return-from HW_RND_GEN$notinline
                 (HW_RND_GEN-logic size x86)))
  (let ((rand-and-cf
         (case size
           (2
            (multiple-value-bind (_str ptr)
                                 ;; Note that ptr stands in for *num.
                                 (ccl::make-heap-ivector 1 '(unsigned-byte 16))
                                 (declare (ignorable _str))
                                 (let* ((cf (ccl::external-call "_rdrand16"
                                                                :address ptr
                                                                (:unsigned 64)))
                                        (num (ccl::%get-unsigned-word ptr 0)))
                                   (ccl::dispose-heap-ivector ptr)
                                   (cons num cf))))
           (4
            (multiple-value-bind (_str ptr)
                                 ;; Note that ptr stands in for *num.
                                 (ccl::make-heap-ivector 1 '(unsigned-byte 32))
                                 (declare (ignorable _str))
                                 (let* ((cf (ccl::external-call "_rdrand32"
                                                                :address ptr
                                                                (:unsigned 64)))
                                        (num (ccl::%get-unsigned-long ptr 0)))
                                   (ccl::dispose-heap-ivector ptr)
                                   (cons num cf))))
           (8
            (multiple-value-bind (_str ptr)
                                 ;; Note that ptr stands in for *num.
                                 (ccl::make-heap-ivector 1 '(unsigned-byte 64))
                                 (declare (ignorable _str))
                                 (let* ((cf (ccl::external-call "_rdrand64"
                                                                :address ptr
                                                                (:unsigned 64)))
                                        (num (ccl::%%get-unsigned-longlong ptr 0)))
                                   (ccl::dispose-heap-ivector ptr)
                                   (cons num cf))))
           (otherwise
            (er hard! 'HW_RND_GEN
                "Illegal size specified for HW_RND_GEN!"))
           )))
    (mv rand-and-cf x86)))

;; ======================================================================
