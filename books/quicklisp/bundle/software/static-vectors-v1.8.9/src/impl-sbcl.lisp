;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-
;;;
;;; --- SBCL implementation
;;;

(in-package :static-vectors)

(declaim (inline fill-foreign-memory))
(defun fill-foreign-memory (pointer length value)
  "Fill LENGTH octets in foreign memory area POINTER with VALUE."
  (foreign-funcall "memset" :pointer pointer :int value :size length :pointer)
  pointer)

(declaim (inline replace-foreign-memory))
(defun replace-foreign-memory (dst-ptr src-ptr length)
  "Copy LENGTH octets from foreign memory area SRC-PTR to DST-PTR."
  (foreign-funcall "memcpy" :pointer dst-ptr :pointer src-ptr :size length :pointer)
  dst-ptr)

(defconstant +array-header-size+
  (* sb-vm:vector-data-offset sb-vm:n-word-bytes))

(declaim (inline vector-widetag-and-n-bits))
(defun vector-widetag-and-n-bits (type)
  (let ((upgraded-type (upgraded-array-element-type type)))
    (case upgraded-type
      ((nil t) (error "~A is not a specializable array element type" type))
      (t
       #+#.(cl:if (cl:find-symbol "%VECTOR-WIDETAG-AND-N-BITS" "SB-IMPL")
                  '(and) '(or))
       (sb-impl::%vector-widetag-and-n-bits type)
       #+#.(cl:if (cl:find-symbol "%VECTOR-WIDETAG-AND-N-BITS-SHIFT" "SB-IMPL")
                  '(and) '(or))
       (multiple-value-bind (widetag shift)
           (sb-impl::%vector-widetag-and-n-bits-shift type)
         (values widetag (ash 1 shift)))))))

(defun %allocate-static-vector (length element-type)
  (labels ((string-widetag-p (widetag)
             (= widetag sb-vm:simple-character-string-widetag))
           (allocation-size (length widetag n-bits)
             (+ (* 2 sb-vm:n-word-bytes
                   (ceiling
                    (* (if (string-widetag-p widetag)
                           (1+ length)  ; for the final #\Null
                           length)
                       n-bits)
                    (* 2 sb-vm:n-word-bits)))
                +array-header-size+)))
    (multiple-value-bind (widetag n-bits)
        (vector-widetag-and-n-bits element-type)
      (let* ((size (allocation-size length widetag n-bits))
             (pointer (foreign-alloc :char :count size)))
        (setf (sb-sys:sap-ref-word pointer 0) widetag
              (sb-sys:sap-ref-word pointer sb-vm:n-word-bytes) (sb-vm:fixnumize length))
        (sb-kernel:%make-lisp-obj (logior (pointer-address pointer)
                                          sb-vm:other-pointer-lowtag))))))

(declaim (inline static-vector-address))
(defun static-vector-address (vector)
  "Return a foreign pointer to VECTOR(including its header).
VECTOR must be a vector created by MAKE-STATIC-VECTOR."
  (logandc2 (sb-kernel:get-lisp-obj-address vector)
            sb-vm:lowtag-mask))

(declaim (inline static-vector-pointer))
(defun static-vector-pointer (vector &key (offset 0))
  "Return a foreign pointer to the beginning of VECTOR + OFFSET octets.
VECTOR must be a vector created by MAKE-STATIC-VECTOR."
  (check-type offset unsigned-byte)
  (make-pointer (+ (static-vector-address vector)
                   +array-header-size+
                   offset)))

(declaim (inline free-static-vector))
(defun free-static-vector (vector)
  "Free VECTOR, which must be a vector created by MAKE-STATIC-VECTOR."
  (declare (sb-ext:muffle-conditions sb-ext:compiler-note))
  (foreign-free (make-pointer (static-vector-address vector)))
  (values))

(defmacro with-static-vector ((var length &rest args
                               &key (element-type ''(unsigned-byte 8))
                                 initial-contents initial-element)
                              &body body &environment env)
  "Bind PTR-VAR to a static vector of length LENGTH and execute BODY
within its dynamic extent. The vector is freed upon exit."
  (declare (ignorable element-type initial-contents initial-element))
  (multiple-value-bind (real-element-type length type-spec)
      (canonicalize-args env element-type length)
    (let ((args (copy-list args)))
      (remf args :element-type)
      `(sb-sys:without-interrupts
         (let ((,var (make-static-vector ,length ,@args
                                         :element-type ,real-element-type)))
           (declare (type ,type-spec ,var))
           (unwind-protect
                (sb-sys:with-local-interrupts ,@body)
             (when ,var (free-static-vector ,var))))))))
