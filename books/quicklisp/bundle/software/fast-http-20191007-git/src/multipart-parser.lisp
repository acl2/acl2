(in-package :cl-user)
(defpackage fast-http.multipart-parser
  (:use :cl
        :fast-http.byte-vector
        :fast-http.error)
  (:import-from :fast-http.parser
                :callbacks-body
                :callbacks-headers-complete
                :callbacks-message-begin
                :callbacks-message-complete
                :make-callbacks
                :parse-headers)
  (:import-from :fast-http.http
                :http-state
                :make-http
                :+state-headers+
                :+state-body+)
  (:import-from :fast-http.util
                :tagcasev
                :casev)
  (:import-from :alexandria
                :format-symbol
                :when-let)
  (:export :ll-multipart-parser
           :ll-multipart-parser-state
           :make-ll-multipart-parser
           :http-multipart-parse))
(in-package :fast-http.multipart-parser)

(defstruct (ll-multipart-parser (:constructor make-ll-multipart-parser
                                  (&key boundary
                                   &aux (header-parser
                                         (let ((parser (make-http)))
                                           (setf (http-state parser) +state-headers+)
                                           parser)))))
  (state 0 :type fixnum)
  (header-parser)
  boundary
  body-mark
  body-buffer
  boundary-mark
  boundary-buffer)

#.`(eval-when (:compile-toplevel :load-toplevel :execute)
     ,@(loop for i from 0
             for state in '(parsing-delimiter-dash-start
                            parsing-delimiter-dash
                            parsing-delimiter
                            parsing-delimiter-end
                            parsing-delimiter-almost-done
                            parsing-delimiter-done
                            header-field-start
                            body-start
                            looking-for-delimiter
                            maybe-delimiter-start
                            maybe-delimiter-first-dash
                            maybe-delimiter-second-dash
                            body-almost-done
                            body-done)
             collect `(defconstant ,(format-symbol t "+~A+" state) ,i)))

(defun http-multipart-parse (parser callbacks data &key (start 0) end)
  (declare (type simple-byte-vector data))
  (let* ((end (or end (length data)))
         (boundary (map '(simple-array (unsigned-byte 8) (*)) #'char-code (ll-multipart-parser-boundary parser)))
         (boundary-length (length boundary))
         (header-parser (ll-multipart-parser-header-parser parser)))
    (declare (type simple-byte-vector boundary))
    (when (= start end)
      (return-from http-multipart-parse start))

    (macrolet ((with-body-cb (callback &body body)
                 `(handler-case (when-let (,callback (callbacks-body callbacks))
                                  ,@body)
                    (error (e)
                      (error 'cb-body :error e))))
               (call-body-cb (&optional (end '(ll-multipart-parser-boundary-mark parser)))
                 (let ((g-end (gensym "END")))
                   `(with-body-cb callback
                      (when (ll-multipart-parser-body-buffer parser)
                        (funcall callback parser
                                 (ll-multipart-parser-body-buffer parser)
                                 0 (length (ll-multipart-parser-body-buffer parser)))
                        (setf (ll-multipart-parser-body-buffer parser) nil))
                      (when-let (,g-end ,end)
                        (funcall callback parser data
                                 (ll-multipart-parser-body-mark parser)
                                 ,g-end)))))
               (flush-boundary-buffer ()
                 `(with-body-cb callback
                    (when (ll-multipart-parser-boundary-buffer parser)
                      (funcall callback parser
                               (ll-multipart-parser-boundary-buffer parser)
                               0 (length (ll-multipart-parser-boundary-buffer parser)))
                      (setf (ll-multipart-parser-boundary-buffer parser) nil)))))
      (let* ((p start)
             (byte (aref data p)))
        #+fast-http-debug
        (log:debug (code-char byte))
        (tagbody
           (macrolet ((go-state (tag &optional (advance 1))
                          `(progn
                             ,(case advance
                                (0 ())
                                (1 '(incf p))
                                (otherwise `(incf p ,advance)))
                             (setf (ll-multipart-parser-state parser) ,tag)
                             #+fast-http-debug
                             (log:debug ,(princ-to-string tag))
                             ,@(and (not (eql advance 0))
                                    `((when (= p end)
                                        (go exit-loop))
                                      (setq byte (aref data p))
                                      #+fast-http-debug
                                      (log:debug (code-char byte))))
                             (go ,tag))))
             (tagcasev (ll-multipart-parser-state parser)
               (+parsing-delimiter-dash-start+
                (unless (= byte +dash+)
                  (go-state +header-field-start+ 0))
                (go-state +parsing-delimiter-dash+))

               (+parsing-delimiter-dash+
                (unless (= byte +dash+)
                  (error 'invalid-multipart-body))
                (go-state +parsing-delimiter+))

               (+parsing-delimiter+
                (let ((end2 (+ p boundary-length)))
                  (cond
                    ((ll-multipart-parser-boundary-buffer parser)
                     (when (< (+ end (length (ll-multipart-parser-boundary-buffer parser)) -3) end2)
                       (setf (ll-multipart-parser-boundary-buffer parser)
                             (concatenate 'simple-byte-vector
                                          (ll-multipart-parser-boundary-buffer parser)
                                          data))
                       (go exit-loop))
                     (let ((data2 (make-array boundary-length :element-type '(unsigned-byte 8)))
                           (boundary-buffer-length (length (ll-multipart-parser-boundary-buffer parser))))
                       (replace data2 (ll-multipart-parser-boundary-buffer parser)
                                :start2 2)
                       (replace data2 data
                                :start1 (- boundary-buffer-length 2))
                       (unless (search boundary data2)
                         ;; Still in the body
                         (when (ll-multipart-parser-body-mark parser)
                           (call-body-cb nil)
                           (flush-boundary-buffer)
                           (go-state +looking-for-delimiter+))
                         (error 'invalid-boundary))
                       (go-state +parsing-delimiter-end+ (- boundary-length boundary-buffer-length -2))))
                    ((< (1- end) end2)
                     ;; EOF
                     (setf (ll-multipart-parser-boundary-buffer parser)
                           (if (ll-multipart-parser-boundary-buffer parser)
                               (concatenate 'simple-byte-vector
                                            (ll-multipart-parser-boundary-buffer parser)
                                            (subseq data (max 0 (- p 2))))
                               (subseq data (max 0 (- p 2)))))
                     (go exit-loop))
                    (T
                     (unless (search boundary data :start2 p :end2 end2)
                       ;; Still in the body
                       (when (ll-multipart-parser-body-mark parser)
                         (go-state +looking-for-delimiter+))
                       (error 'invalid-boundary))
                     (go-state +parsing-delimiter-end+ boundary-length)))))

               (+parsing-delimiter-end+
                (casev byte
                  (+cr+ (go-state +parsing-delimiter-almost-done+))
                  (+lf+ (go-state +parsing-delimiter-almost-done+ 0))
                  (+dash+ (go-state +body-almost-done+))
                  (otherwise
                   ;; Still in the body
                   (when (ll-multipart-parser-body-mark parser)
                     (call-body-cb nil)
                     (flush-boundary-buffer)
                     (go-state +looking-for-delimiter+))
                   (error 'invalid-boundary))))

               (+parsing-delimiter-almost-done+
                (unless (= byte +lf+)
                  (error 'invalid-boundary))
                (when (ll-multipart-parser-body-mark parser)
                  ;; got a part
                  (when (ll-multipart-parser-boundary-mark parser)
                    (call-body-cb))
                  (when-let (callback (callbacks-message-complete callbacks))
                    (handler-case (funcall callback parser)
                      (error (e)
                        (error 'cb-message-complete :error e)))))
                (go-state +parsing-delimiter-done+))

               (+parsing-delimiter-done+
                (when-let (callback (callbacks-message-begin callbacks))
                  (handler-case (funcall callback parser)
                    (error (e)
                      (error 'cb-message-begin :error e))))
                (setf (ll-multipart-parser-body-mark parser) p)
                (go-state +header-field-start+ 0))

               (+header-field-start+
                (let ((next (parse-headers header-parser callbacks data p end)))
                  (setq p (1- next)) ;; XXX
                  ;; parsing headers done
                  (when (= (http-state header-parser) +state-body+)
                    (when-let (callback (callbacks-headers-complete callbacks))
                      (handler-case (funcall callback parser)
                        (error (e)
                          (error 'cb-headers-complete :error e))))
                    (setf (http-state header-parser) +state-headers+))
                  (go-state +body-start+ 0)))

               (+body-start+
                (setf (ll-multipart-parser-body-mark parser) (1+ p))
                (go-state +looking-for-delimiter+))

               (+looking-for-delimiter+
                (setf (ll-multipart-parser-boundary-mark parser) nil)
                (casev byte
                  (+cr+ (setf (ll-multipart-parser-boundary-mark parser) p)
                        (go-state +maybe-delimiter-start+))
                  (otherwise (go-state +looking-for-delimiter+))))

               (+maybe-delimiter-start+
                (unless (= byte +lf+)
                  (go-state +looking-for-delimiter+ 0))
                (go-state +maybe-delimiter-first-dash+))

	       (+maybe-delimiter-first-dash+
                (if (= byte +dash+)
                    (go-state +maybe-delimiter-second-dash+)
		    (if (= byte +cr+)
			(progn
			  (setf (ll-multipart-parser-boundary-mark parser) p)
			  (go-state +maybe-delimiter-start+))
			(go-state +looking-for-delimiter+))))

               (+maybe-delimiter-second-dash+
                (if (= byte +dash+)
                    (go-state +parsing-delimiter+)
                    (go-state +looking-for-delimiter+)))

               (+body-almost-done+
                (casev byte
                  (+dash+ (go-state +body-done+ 0))
                  (otherwise (error 'invalid-multipart-body))))

               (+body-done+
                (when (ll-multipart-parser-body-mark parser)
                  ;; got a part
                  (setf (ll-multipart-parser-body-buffer parser) nil)
                  (call-body-cb)
                  (when-let (callback (callbacks-message-complete callbacks))
                    (handler-case (funcall callback parser)
                      (error (e)
                        (error 'cb-message-complete :error e))))
                  (setf (ll-multipart-parser-body-mark parser) nil))
                (go exit-loop))))
         exit-loop)
        (when (ll-multipart-parser-body-mark parser)
          (when (<= +looking-for-delimiter+
                    (ll-multipart-parser-state parser)
                    +maybe-delimiter-second-dash+)
            (call-body-cb (or (ll-multipart-parser-boundary-mark parser) p)))
          ;; buffer the last part
          (when (ll-multipart-parser-boundary-mark parser)
            (setf (ll-multipart-parser-body-buffer parser)
                  (if (ll-multipart-parser-body-buffer parser)
                      (concatenate 'simple-byte-vector
                                   (ll-multipart-parser-body-buffer parser)
                                   (subseq data (ll-multipart-parser-boundary-mark parser)))
                      (subseq data (ll-multipart-parser-boundary-mark parser)))))

          (setf (ll-multipart-parser-body-mark parser) 0
                (ll-multipart-parser-boundary-mark parser) nil))
        p))))
