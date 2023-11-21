;;;; tests.lisp -- tests for various bits of functionality

(cl:defpackage :nibbles-tests
  (:use :cl))

(cl:in-package :nibbles-tests)

;;; Basic tests for correctness.

(defun make-byte-combiner (n-bytes big-endian-p)
  (let ((count 0)
        (buffer 0))
    #'(lambda (byte)
        (setf buffer
              (if big-endian-p
                  (logior (ash buffer 8) byte)
                  (let ((x (logior (ash byte (* 8 count)) buffer)))
                    (if (= count n-bytes)
                        (ash x -8)
                        x))))
        (unless (= count n-bytes)
          (incf count))
        (cond
          ((= count n-bytes)
           (let ((val (ldb (byte (* 8 n-bytes) 0) buffer)))
             (multiple-value-prog1 (values val t)
               (setf buffer val))))
          (t (values 0 nil))))))

(defun generate-random-octet-vector (n-octets)
  (loop with v = (nibbles:make-octet-vector n-octets)
        for i from 0 below n-octets
        do (setf (aref v i) (random 256))
        finally (return v)))

(defun generate-reffed-values (byte-vector bitsize signedp big-endian-p
			       &optional (rolling-p t))
  (do* ((byte-kind (if signedp 'signed-byte 'unsigned-byte))
        (bytesize (truncate bitsize 8))
	(n-bytes-to-read (if rolling-p
			     (length byte-vector)
			     (* (floor (length byte-vector) bytesize)
				bytesize)))
        (n-values (if rolling-p
		      (- (length byte-vector) (1- bytesize))
		      (truncate n-bytes-to-read bytesize)))
        (expected-values (make-array n-values :element-type `(,byte-kind ,bitsize)))
        (i 0 (1+ i))
        (j 0)
        (combiner (make-byte-combiner bytesize big-endian-p)))
      ((>= i n-bytes-to-read) expected-values)
    (multiple-value-bind (aggregate set-p) (funcall combiner (aref byte-vector i))
      (when set-p
        (setf (aref expected-values j)
              (if (and signedp (logbitp (1- bitsize) aggregate))
                  (dpb aggregate (byte bitsize 0) -1)
                  aggregate))
	(unless rolling-p
	  (setf combiner (make-byte-combiner bytesize big-endian-p)))
        (incf j)))))

(defvar *default-n-values* 4096)

(defun generate-random-test (bitsize signedp big-endian-p
                             &optional (n-values *default-n-values*))
  (let* ((n-bytes (truncate bitsize 8))
	 (total-octets (+ n-values (1- n-bytes)))
         (random-octets (generate-random-octet-vector total-octets))
         (expected-vector
          (generate-reffed-values random-octets bitsize signedp big-endian-p)))
    (values random-octets expected-vector)))

(defun compile-quietly (form)
  (handler-bind ((style-warning #'muffle-warning)
                 #+sbcl (sb-ext:compiler-note #'muffle-warning))
    (compile nil form)))

(defun ref-test (reffer bitsize signedp big-endian-p
                 &optional (n-octets *default-n-values*))
  (multiple-value-bind (byte-vector expected-vector)
      (generate-random-test bitsize signedp big-endian-p n-octets)
    (flet ((run-test (reffer)
             (loop for i from 0 below n-octets
                   for j from 0
                   do (let ((reffed-val (funcall reffer byte-vector i))
                            (expected-val (aref expected-vector j)))
                        (unless (= reffed-val expected-val)
                          (error "wanted ~D, got ~D from ~A"
                                 expected-val reffed-val
                                 (subseq byte-vector i
					 (+ i (truncate bitsize 8))))))
                   finally (return :ok))))
      (run-test reffer)
      (when (typep byte-vector '(simple-array (unsigned-byte 8) (*)))
        (let ((compiled (compile-quietly
                           `(lambda (v i)
                              (declare (type (simple-array (unsigned-byte 8) (*)) v))
                              (declare (type (integer 0 #.(1- array-dimension-limit)) i))
                              (declare (optimize speed (debug 0)))
                              (,reffer v i)))))
          (run-test compiled))))))

(defun set-test (reffer bitsize signedp big-endian-p
                 &optional (n-octets *default-n-values*))
  ;; We use GET-SETF-EXPANSION to avoid reaching too deeply into
  ;; internals.  This bit relies on knowing that the writer-form will be
  ;; a simple function call whose CAR is the internal setter, but I
  ;; think that's a bit better than :: references everywhere.
  (multiple-value-bind (vars vals store-vars writer-form reader-form)
      (get-setf-expansion `(,reffer x i))
    (declare (ignore vars vals store-vars reader-form))
    (let ((setter (car writer-form)))
      ;; Sanity check.
      (unless (eq (symbol-package setter) (find-package :nibbles))
        (error "need to update setter tests!"))
      (multiple-value-bind (byte-vector expected-vector)
          (generate-random-test bitsize signedp big-endian-p n-octets)
        (flet ((run-test (setter)
                 (loop with fill-vec = (let ((v (copy-seq byte-vector)))
                                         (fill v 0)
                                         v)
                       for i from 0 below n-octets
                       for j from 0
                       do (funcall setter fill-vec i (aref expected-vector j))
                       finally (return
                                 (if (mismatch fill-vec byte-vector)
                                     (error "wanted ~A, got ~A" byte-vector fill-vec)
                                     :ok)))))
          (run-test setter)
          (when (typep byte-vector '(simple-array (unsigned-byte 8) (*)))
            (let ((compiled (compile-quietly
                             `(lambda (v i new)
                                (declare (type (simple-array (unsigned-byte 8) (*)) v))
                                (declare (type (integer 0 #.(1- array-dimension-limit)) i))
                                (declare (type (,(if signedp 'signed-byte 'unsigned-byte)
                                                 ,bitsize) new))
                                (declare (optimize speed (debug 0)))
                                (,setter v i new)))))
              (run-test compiled))))))))

;;; Big-endian integer ref tests

(rtest:deftest :ub16ref/be
  (ref-test 'nibbles:ub16ref/be 16 nil t)
  :ok)

(rtest:deftest :sb16ref/be
  (ref-test 'nibbles:sb16ref/be 16 t t)
  :ok)

(rtest:deftest :ub32ref/be
  (ref-test 'nibbles:ub32ref/be 32 nil t)
  :ok)

(rtest:deftest :sb32ref/be
  (ref-test 'nibbles:sb32ref/be 32 t t)
  :ok)

(rtest:deftest :ub64ref/be
  (ref-test 'nibbles:ub64ref/be 64 nil t)
  :ok)

(rtest:deftest :sb64ref/be
  (ref-test 'nibbles:sb64ref/be 64 t t)
  :ok)

;;; Big-endian integer set tests

(rtest:deftest :ub16set/be
  (set-test 'nibbles:ub16ref/be 16 nil t)
  :ok)

(rtest:deftest :sb16set/be
  (set-test 'nibbles:sb16ref/be 16 t t)
  :ok)

(rtest:deftest :ub32set/be
  (set-test 'nibbles:ub32ref/be 32 nil t)
  :ok)

(rtest:deftest :sb32set/be
  (set-test 'nibbles:sb32ref/be 32 t t)
  :ok)

(rtest:deftest :ub64set/be
  (set-test 'nibbles:ub64ref/be 64 nil t)
  :ok)

(rtest:deftest :sb64set/be
  (set-test 'nibbles:sb64ref/be 64 t t)
  :ok)

;;; Little-endian integer ref tests

(rtest:deftest :ub16ref/le
  (ref-test 'nibbles:ub16ref/le 16 nil nil)
  :ok)

(rtest:deftest :sb16ref/le
  (ref-test 'nibbles:sb16ref/le 16 t nil)
  :ok)

(rtest:deftest :ub32ref/le
  (ref-test 'nibbles:ub32ref/le 32 nil nil)
  :ok)

(rtest:deftest :sb32ref/le
  (ref-test 'nibbles:sb32ref/le 32 t nil)
  :ok)

(rtest:deftest :ub64ref/le
  (ref-test 'nibbles:ub64ref/le 64 nil nil)
  :ok)

(rtest:deftest :sb64ref/le
  (ref-test 'nibbles:sb64ref/le 64 t nil)
  :ok)

;;; Little-endian integer set tests

(rtest:deftest :ub16set/le
  (set-test 'nibbles:ub16ref/le 16 nil nil)
  :ok)

(rtest:deftest :sb16set/le
  (set-test 'nibbles:sb16ref/le 16 t nil)
  :ok)

(rtest:deftest :ub32set/le
  (set-test 'nibbles:ub32ref/le 32 nil nil)
  :ok)

(rtest:deftest :sb32set/le
  (set-test 'nibbles:sb32ref/le 32 t nil)
  :ok)

(rtest:deftest :ub64set/le
  (set-test 'nibbles:ub64ref/le 64 nil nil)
  :ok)

(rtest:deftest :sb64set/le
  (set-test 'nibbles:sb64ref/le 64 t nil)
  :ok)

;;; Floating point.

(defun normal-float-p (bits bitsize)
  "Return true when BITS represents a IEEE floating point number that is
neither an infinity nor a NaN.  Additionally, for CLISP, the number may not be
denormalized."
  (ecase bitsize
    (32 (let ((exponent (ldb (byte 8 23) bits)))
          (and (/= exponent 255) #+clisp (/= exponent 0))))
    (64 (let ((exponent (ldb (byte 11 52) bits)))
          (and (/= exponent 2047) #+clisp (/= exponent 0))))))

(defun random-float-bits (bitsize)
  (let ((bits (random (expt 2 bitsize))))
    (if (normal-float-p bits bitsize)
        bits
        (random-float-bits bitsize))))

(defun generate-random-float-vector (n-floats bitsize big-endian-p)
  (let* ((bytesize (truncate bitsize 8))
         (octets (* n-floats bytesize))
         (v (nibbles:make-octet-vector octets)))
    (loop for i from 0 below octets by bytesize do
      (let ((bits (random-float-bits bitsize)))
        (ecase bitsize
          (32 (if big-endian-p
                  (setf (nibbles:ub32ref/be v i) bits)
                  (setf (nibbles:ub32ref/le v i) bits)))
          (64 (if big-endian-p
                  (setf (nibbles:ub64ref/be v i) bits)
                  (setf (nibbles:ub64ref/le v i) bits))))))
    v))

(defun generate-reffed-floats (byte-vector n-floats bitsize big-endian-p)
  (let ((bytesize (truncate bitsize 8))
        (expected-values
          (make-array n-floats :element-type (if (= bitsize 32) 'single-float 'double-float))))
    (loop for i from 0 by bytesize
          for j from 0 below n-floats
          do (let ((bits
                     (ecase bitsize
                       (32 (if big-endian-p
                               (nibbles:ub32ref/be byte-vector i)
                               (nibbles:ub32ref/le byte-vector i)))
                       (64 (if big-endian-p
                               (nibbles:ub64ref/be byte-vector i)
                               (nibbles:ub64ref/le byte-vector i))))))
               (setf (aref expected-values j)
                     (ecase bitsize
                       (32 (nibbles::make-single-float bits))
                       (64 (nibbles::make-double-float (ldb (byte 32 32) bits)
                                                       (ldb (byte 32 0) bits)))))))
    expected-values))

(defvar *default-float-values* 4096)

(defun generate-random-float-test (bitsize big-endian-p
                                   &optional (n-floats *default-float-values*))
  (let* ((random-octets (generate-random-float-vector n-floats bitsize big-endian-p))
         (expected-vector (generate-reffed-floats random-octets n-floats bitsize big-endian-p)))
    (values random-octets expected-vector)))

(defun ref-float-test (reffer bitsize big-endian-p
                       &optional (n-floats *default-float-values*))
  (multiple-value-bind (byte-vector expected-vector)
      (generate-random-float-test bitsize big-endian-p n-floats)
    (flet ((run-test (reffer)
             (let ((bytesize (truncate bitsize 8)))
               (loop for i from 0 by bytesize
                     for j from 0 below n-floats
                     do (let ((reffed-val (funcall reffer byte-vector i))
                              (expected-val (aref expected-vector j)))
                          (unless (= reffed-val expected-val)
                            (error "wanted ~D, got ~D from ~A"
                                   expected-val reffed-val
                                   (subseq byte-vector i (+ i bytesize)))))
                     finally (return :ok)))))
      (run-test reffer)
      (when (typep byte-vector '(simple-array (unsigned-byte 8) (*)))
        (let ((compiled (compile-quietly
                           `(lambda (v i)
                              (declare (type (simple-array (unsigned-byte 8) (*)) v))
                              (declare (type (integer 0 #.(1- array-dimension-limit)) i))
                              (declare (optimize speed (debug 0)))
                              (,reffer v i)))))
          (run-test compiled))))))

(defun set-float-test (reffer bitsize big-endian-p
                 &optional (n-floats *default-float-values*))
  ;; We use GET-SETF-EXPANSION to avoid reaching too deeply into
  ;; internals.  This bit relies on knowing that the writer-form will be
  ;; a simple function call whose CAR is the internal setter, but I
  ;; think that's a bit better than :: references everywhere.
  (multiple-value-bind (vars vals store-vars writer-form reader-form)
      (get-setf-expansion `(,reffer x i))
    (declare (ignore vars vals store-vars reader-form))
    (let ((setter (car writer-form)))
      ;; Sanity check.
      (unless (eq (symbol-package setter) (find-package :nibbles))
        (error "need to update setter tests!"))
      (multiple-value-bind (byte-vector expected-vector)
          (generate-random-float-test bitsize big-endian-p n-floats)
        (flet ((run-test (setter)
                 (let ((bytesize (truncate bitsize 8)))
                   (loop with fill-vec = (let ((v (copy-seq byte-vector)))
                                           (fill v 0)
                                           v)
                         for i from 0 by bytesize
                         for j from 0 below n-floats
                         do (funcall setter fill-vec i (aref expected-vector j))
                         finally (return
                                   (if (mismatch fill-vec byte-vector)
                                       (error "wanted ~A, got ~A" byte-vector fill-vec)
                                       :ok))))))
          (run-test setter)
          (when (typep byte-vector '(simple-array (unsigned-byte 8) (*)))
            (let ((compiled (compile-quietly
                             `(lambda (v i new)
                                (declare (type (simple-array (unsigned-byte 8) (*)) v))
                                (declare (type (integer 0 #.(1- array-dimension-limit)) i))
                                (declare (type ,(if (= bitsize 32) 'single-float 'double-float)
                                               new))
                                (declare (optimize speed (debug 0)))
                                (,setter v i new)))))
              (run-test compiled))))))))

;;; Big-endian float ref tests

(rtest:deftest :ieee-single-ref/be
  (ref-float-test 'nibbles:ieee-single-ref/be 32 t)
  :ok)

(rtest:deftest :ieee-double-ref/be
  (ref-float-test 'nibbles:ieee-double-ref/be 64 t)
  :ok)

;;; Big-endian float set tests

(rtest:deftest :ieee-single-set/be
  (set-float-test 'nibbles:ieee-single-ref/be 32 t)
  :ok)

(rtest:deftest :ieee-double-set/be
  (set-float-test 'nibbles:ieee-double-ref/be 64 t)
  :ok)

;;; Little-endian float ref tests

(rtest:deftest :ieee-single-ref/le
  (ref-float-test 'nibbles:ieee-single-ref/le 32 nil)
  :ok)

(rtest:deftest :ieee-double-ref/le
  (ref-float-test 'nibbles:ieee-double-ref/le 64 nil)
  :ok)

;;; Little-endian float set tests

(rtest:deftest :ieee-single-set/le
  (set-float-test 'nibbles:ieee-single-ref/le 32 nil)
  :ok)

(rtest:deftest :ieee-double-set/le
  (set-float-test 'nibbles:ieee-double-ref/le 64 nil)
  :ok)


;;; Stream reading tests

(defvar *path* #.*compile-file-truename*)

(defun read-file-as-octets (pathname)
  (with-open-file (stream pathname :direction :input
                          :element-type '(unsigned-byte 8))
    (let ((v (nibbles:make-octet-vector (file-length stream))))
      (read-sequence v stream)
      v)))

(defun read-test (reader bitsize signedp big-endian-p)
  (let* ((pathname *path*)
         (file-contents (read-file-as-octets pathname))
         (expected-values (generate-reffed-values file-contents bitsize
                                                  signedp big-endian-p)))
    (with-open-file (stream pathname :direction :input
                            :element-type '(unsigned-byte 8))
      (loop with n-values = (length expected-values)
            for i from 0 below n-values
            do (file-position stream i)
               (let ((read-value (funcall reader stream))
                     (expected-value (aref expected-values i)))
                 (unless (= read-value expected-value)
                   (return :bad)))
            finally (return :ok)))))

(defun read-sequence-test (result-type reader bitsize signedp big-endian-p)
  (let* ((pathname *path*)
	 (file-contents (subseq (read-file-as-octets pathname) 0 8))
	 (expected-values (generate-reffed-values file-contents bitsize
						  signedp big-endian-p nil)))
    (with-open-file (stream pathname :direction :input
			    :element-type '(unsigned-byte 8))
      (let* ((n-values (truncate (length file-contents)
				 (truncate bitsize 8)))
	     (read-values (funcall reader result-type stream n-values)))
	(if (or (not (typep read-values result-type))
		(mismatch read-values expected-values))
	    :bad
	    :ok)))))

(rtest:deftest :read-ub16/be
  (read-test 'nibbles:read-ub16/be 16 nil t)
  :ok)

(rtest:deftest :read-sb16/be
  (read-test 'nibbles:read-sb16/be 16 t t)
  :ok)

(rtest:deftest :read-ub32/be
  (read-test 'nibbles:read-ub32/be 32 nil t)
  :ok)

(rtest:deftest :read-sb32/be
  (read-test 'nibbles:read-sb32/be 32 t t)
  :ok)

(rtest:deftest :read-ub64/be
  (read-test 'nibbles:read-ub64/be 64 nil t)
  :ok)

(rtest:deftest :read-sb64/be
  (read-test 'nibbles:read-sb64/be 64 t t)
  :ok)

(rtest:deftest :read-ub16/le
  (read-test 'nibbles:read-ub16/le 16 nil nil)
  :ok)

(rtest:deftest :read-sb16/le
  (read-test 'nibbles:read-sb16/le 16 t nil)
  :ok)

(rtest:deftest :read-ub32/le
  (read-test 'nibbles:read-ub32/le 32 nil nil)
  :ok)

(rtest:deftest :read-sb32/le
  (read-test 'nibbles:read-sb32/le 32 t nil)
  :ok)

(rtest:deftest :read-ub64/le
  (read-test 'nibbles:read-ub64/le 64 nil nil)
  :ok)

(rtest:deftest :read-sb64/le
  (read-test 'nibbles:read-sb64/le 64 t nil)
  :ok)

(rtest:deftest :read-ub16/be-vector
  (read-sequence-test 'vector 'nibbles:read-ub16/be-sequence 16 nil t)
  :ok)

(rtest:deftest :read-sb16/be-vector
  (read-sequence-test 'vector 'nibbles:read-sb16/be-sequence 16 t t)
  :ok)

(rtest:deftest :read-ub32/be-vector
  (read-sequence-test 'vector 'nibbles:read-ub32/be-sequence 32 nil t)
  :ok)

(rtest:deftest :read-sb32/be-vector
  (read-sequence-test 'vector 'nibbles:read-sb32/be-sequence 32 t t)
  :ok)

(rtest:deftest :read-ub64/be-vector
  (read-sequence-test 'vector 'nibbles:read-ub64/be-sequence 64 nil t)
  :ok)

(rtest:deftest :read-sb64/be-vector
  (read-sequence-test 'vector 'nibbles:read-sb64/be-sequence 64 t t)
  :ok)

(rtest:deftest :read-ub16/le-vector
  (read-sequence-test 'vector 'nibbles:read-ub16/le-sequence 16 nil nil)
  :ok)

(rtest:deftest :read-sb16/le-vector
  (read-sequence-test 'vector 'nibbles:read-sb16/le-sequence 16 t nil)
  :ok)

(rtest:deftest :read-ub32/le-vector
  (read-sequence-test 'vector 'nibbles:read-ub32/le-sequence 32 nil nil)
  :ok)

(rtest:deftest :read-sb32/le-vector
  (read-sequence-test 'vector 'nibbles:read-sb32/le-sequence 32 t nil)
  :ok)

(rtest:deftest :read-ub64/le-vector
  (read-sequence-test 'vector 'nibbles:read-ub64/le-sequence 64 nil nil)
  :ok)

(rtest:deftest :read-sb64/le-vector
  (read-sequence-test 'vector 'nibbles:read-sb64/le-sequence 64 t nil)
  :ok)

(rtest:deftest :read-ub16/be-list
  (read-sequence-test 'list 'nibbles:read-ub16/be-sequence 16 nil t)
  :ok)

(rtest:deftest :read-sb16/be-list
  (read-sequence-test 'list 'nibbles:read-sb16/be-sequence 16 t t)
  :ok)

(rtest:deftest :read-ub32/be-list
  (read-sequence-test 'list 'nibbles:read-ub32/be-sequence 32 nil t)
  :ok)

(rtest:deftest :read-sb32/be-list
  (read-sequence-test 'list 'nibbles:read-sb32/be-sequence 32 t t)
  :ok)

(rtest:deftest :read-ub64/be-list
  (read-sequence-test 'list 'nibbles:read-ub64/be-sequence 64 nil t)
  :ok)

(rtest:deftest :read-sb64/be-list
  (read-sequence-test 'list 'nibbles:read-sb64/be-sequence 64 t t)
  :ok)

(rtest:deftest :read-ub16/le-list
  (read-sequence-test 'list 'nibbles:read-ub16/le-sequence 16 nil nil)
  :ok)

(rtest:deftest :read-sb16/le-list
  (read-sequence-test 'list 'nibbles:read-sb16/le-sequence 16 t nil)
  :ok)

(rtest:deftest :read-ub32/le-list
  (read-sequence-test 'list 'nibbles:read-ub32/le-sequence 32 nil nil)
  :ok)

(rtest:deftest :read-sb32/le-list
  (read-sequence-test 'list 'nibbles:read-sb32/le-sequence 32 t nil)
  :ok)

(rtest:deftest :read-ub64/le-list
  (read-sequence-test 'list 'nibbles:read-ub64/le-sequence 64 nil nil)
  :ok)

(rtest:deftest :read-sb64/le-list
  (read-sequence-test 'list 'nibbles:read-sb64/le-sequence 64 t nil)
  :ok)

;;; Stream writing tests

(defvar *output-directory*
  (merge-pathnames (make-pathname :name nil :type nil
                                  :directory '(:relative "test-output"))
                   (make-pathname :directory (pathname-directory *path*))))

(defun write-test (writer bitsize signedp big-endian-p)
  (multiple-value-bind (byte-vector expected-values)
      (generate-random-test bitsize signedp big-endian-p)
    (let ((tmpfile (make-pathname :name "tmp" :defaults *output-directory*)))
      (ensure-directories-exist tmpfile)
      (with-open-file (stream tmpfile :direction :output
                              :element-type '(unsigned-byte 8)
                              :if-does-not-exist :create
                              :if-exists :supersede)
        (loop with n-values = (length expected-values)
              for i from 0 below n-values
              do (file-position stream i)
                 (funcall writer (aref expected-values i) stream)))
      (let ((file-contents (read-file-as-octets tmpfile)))
        (delete-file tmpfile)
        (if (mismatch byte-vector file-contents)
            :bad
            :ok)))))

(defun read-sequence-from-file (filename seq-type reader n-values)
  (with-open-file (stream filename :direction :input
			  :element-type '(unsigned-byte 8)
			  :if-does-not-exist :error)
    (funcall reader seq-type stream n-values)))

(defun write-sequence-test (seq-type reader writer
			    bitsize signedp big-endian-p)
  (multiple-value-bind (byte-vector expected-values)
      (generate-random-test bitsize signedp big-endian-p)
    (declare (ignore byte-vector))
    (let ((tmpfile (make-pathname :name "tmp" :defaults *output-directory*))
	  (values-seq (coerce expected-values seq-type)))
      (ensure-directories-exist tmpfile)
      (flet ((run-random-test (values expected-start expected-end)
	       (with-open-file (stream tmpfile :direction :output
				       :element-type '(unsigned-byte 8)
				       :if-does-not-exist :create
				       :if-exists :supersede)
		 (funcall writer values stream :start expected-start
			  :end expected-end))
	       (let ((file-contents (read-sequence-from-file tmpfile
							     seq-type
							     reader
							     (- expected-end expected-start))))
		 (mismatch values file-contents
			   :start1 expected-start
			   :end1 expected-end))))
	(let* ((block-size (truncate (length expected-values) 4))
	       (upper-quartile (* block-size 3)))
	  (unwind-protect
	       (loop repeat 32
		     when (run-random-test values-seq (random block-size)
						      (+ upper-quartile
							 (random block-size)))
		       do (return :bad)
		     finally (return :ok))
	    (delete-file tmpfile)))))))

(rtest:deftest :write-ub16/be
  (write-test 'nibbles:write-ub16/be 16 nil t)
  :ok)

(rtest:deftest :write-sb16/be
  (write-test 'nibbles:write-sb16/be 16 t t)
  :ok)

(rtest:deftest :write-ub32/be
  (write-test 'nibbles:write-ub32/be 32 nil t)
  :ok)

(rtest:deftest :write-sb32/be
  (write-test 'nibbles:write-sb32/be 32 t t)
  :ok)

(rtest:deftest :write-ub64/be
  (write-test 'nibbles:write-ub64/be 64 nil t)
  :ok)

(rtest:deftest :write-sb64/be
  (write-test 'nibbles:write-sb64/be 64 t t)
  :ok)

(rtest:deftest :write-ub16/le
  (write-test 'nibbles:write-ub16/le 16 nil nil)
  :ok)

(rtest:deftest :write-sb16/le
  (write-test 'nibbles:write-sb16/le 16 t nil)
  :ok)

(rtest:deftest :write-ub32/le
  (write-test 'nibbles:write-ub32/le 32 nil nil)
  :ok)

(rtest:deftest :write-sb32/le
  (write-test 'nibbles:write-sb32/le 32 t nil)
  :ok)

(rtest:deftest :write-ub64/le
  (write-test 'nibbles:write-ub64/le 64 nil nil)
  :ok)

(rtest:deftest :write-sb64/le
  (write-test 'nibbles:write-sb64/le 64 t nil)
  :ok)

(rtest:deftest :write-ub16/be-vector
  (write-sequence-test 'vector
		       'nibbles:read-ub16/be-sequence
		       'nibbles:write-ub16/be-sequence 16 nil t)
  :ok)

(rtest:deftest :write-sb16/be-vector
  (write-sequence-test 'vector
		       'nibbles:read-sb16/be-sequence
		       'nibbles:write-sb16/be-sequence 16 t t)
  :ok)

(rtest:deftest :write-ub32/be-vector
  (write-sequence-test 'vector
		       'nibbles:read-ub32/be-sequence
		       'nibbles:write-ub32/be-sequence 32 nil t)
  :ok)

(rtest:deftest :write-sb32/be-vector
  (write-sequence-test 'vector
		       'nibbles:read-sb32/be-sequence
		       'nibbles:write-sb32/be-sequence 32 t t)
  :ok)

(rtest:deftest :write-ub64/be-vector
  (write-sequence-test 'vector
		       'nibbles:read-ub64/be-sequence
		       'nibbles:write-ub64/be-sequence 64 nil t)
  :ok)

(rtest:deftest :write-sb64/be-vector
  (write-sequence-test 'vector
		       'nibbles:read-sb64/be-sequence
		       'nibbles:write-sb64/be-sequence 64 t t)
  :ok)

(rtest:deftest :write-ub16/le-vector
  (write-sequence-test 'vector
		       'nibbles:read-ub16/le-sequence
		       'nibbles:write-ub16/le-sequence 16 nil nil)
  :ok)

(rtest:deftest :write-sb16/le-vector
  (write-sequence-test 'vector
		       'nibbles:read-sb16/le-sequence
		       'nibbles:write-sb16/le-sequence 16 t nil)
  :ok)

(rtest:deftest :write-ub32/le-vector
  (write-sequence-test 'vector
		       'nibbles:read-ub32/le-sequence
		       'nibbles:write-ub32/le-sequence 32 nil nil)
  :ok)

(rtest:deftest :write-sb32/le-vector
  (write-sequence-test 'vector
		       'nibbles:read-sb32/le-sequence
		       'nibbles:write-sb32/le-sequence 32 t nil)
  :ok)

(rtest:deftest :write-ub64/le-vector
  (write-sequence-test 'vector
		       'nibbles:read-ub64/le-sequence
		       'nibbles:write-ub64/le-sequence 64 nil nil)
  :ok)

(rtest:deftest :write-sb64/le-vector
  (write-sequence-test 'vector
		       'nibbles:read-sb64/le-sequence
		       'nibbles:write-sb64/le-sequence 64 t nil)
  :ok)

(rtest:deftest :write-ub16/be-list
  (write-sequence-test 'list
		       'nibbles:read-ub16/be-sequence
		       'nibbles:write-ub16/be-sequence 16 nil t)
  :ok)

(rtest:deftest :write-sb16/be-list
  (write-sequence-test 'list
		       'nibbles:read-sb16/be-sequence
		       'nibbles:write-sb16/be-sequence 16 t t)
  :ok)

(rtest:deftest :write-ub32/be-list
  (write-sequence-test 'list
		       'nibbles:read-ub32/be-sequence
		       'nibbles:write-ub32/be-sequence 32 nil t)
  :ok)

(rtest:deftest :write-sb32/be-list
  (write-sequence-test 'list
		       'nibbles:read-sb32/be-sequence
		       'nibbles:write-sb32/be-sequence 32 t t)
  :ok)

(rtest:deftest :write-ub64/be-list
  (write-sequence-test 'list
		       'nibbles:read-ub64/be-sequence
		       'nibbles:write-ub64/be-sequence 64 nil t)
  :ok)

(rtest:deftest :write-sb64/be-list
  (write-sequence-test 'list
		       'nibbles:read-sb64/be-sequence
		       'nibbles:write-sb64/be-sequence 64 t t)
  :ok)

(rtest:deftest :write-ub16/le-list
  (write-sequence-test 'list
		       'nibbles:read-ub16/le-sequence
		       'nibbles:write-ub16/le-sequence 16 nil nil)
  :ok)

(rtest:deftest :write-sb16/le-list
  (write-sequence-test 'list
		       'nibbles:read-sb16/le-sequence
		       'nibbles:write-sb16/le-sequence 16 t nil)
  :ok)

(rtest:deftest :write-ub32/le-list
  (write-sequence-test 'list
		       'nibbles:read-ub32/le-sequence
		       'nibbles:write-ub32/le-sequence 32 nil nil)
  :ok)

(rtest:deftest :write-sb32/le-list
  (write-sequence-test 'list
		       'nibbles:read-sb32/le-sequence
		       'nibbles:write-sb32/le-sequence 32 t nil)
  :ok)

(rtest:deftest :write-ub64/le-list
  (write-sequence-test 'list
		       'nibbles:read-ub64/le-sequence
		       'nibbles:write-ub64/le-sequence 64 nil nil)
  :ok)

(rtest:deftest :write-sb64/le-list
  (write-sequence-test 'list
		       'nibbles:read-sb64/le-sequence
		       'nibbles:write-sb64/le-sequence 64 t nil)
  :ok)
