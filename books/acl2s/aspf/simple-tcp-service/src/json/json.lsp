;; SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :acl2s-json)

(setq json::*json-identifier-name-to-lisp* 'json::simplified-camel-case-to-lisp)

(defun recordp (val)
  (and (acl2::alistp val)
       (assoc :0TAG val)))

(defparameter *encode-alists-as-plain-lists* nil
  "This controls whether things that look like alists (e.g. that are
nonempty lists where the first element is a cons of something onto an
atom) get encoded as regular lists or as special alist values.")

#|
string -> string
symbol -> { type: "sym", val: "<symbol in readable form here>" }
rational -> { type: "rat", n: number, d: number }
list -> [ <item1>, ... , <itemn> ]
defdata object -> { type: "defdata", 0tag: string, fields... }
|#

(defun encode-alist-pair (val &optional (stream *standard-output*))
  (format stream "\"~a\": " (car val))
  (encode-value (cdr val) stream))

(defun encode-alist (val &optional (stream *standard-output*))
  (write-string "{" stream)
  (if (consp val)
      (progn
        (loop for pair in (butlast val) do
              (encode-alist-pair pair stream)
              (write-string "," stream))
        (encode-alist-pair (car (last val)) stream))
    nil)
  (write-string "}" stream))

(defun encode-value (val &optional (stream *standard-output*))
  (cond
   ((characterp val) (format stream "\"~a\"" val))
   ((stringp val) (format stream "~s" val))
   ((integerp val) (encode-alist `((type . "int")
                                   (val . ,(write-to-string val)))
                                 stream))
   ((acl2::rationalp val) (encode-alist
                           `((type . "rat")
                             (n . ,(write-to-string (acl2::numerator val)))
                             (d . ,(write-to-string (acl2::denominator val))))
                           stream))
   ((acl2::complex-rationalp val) (encode-alist
                                   `((type . "complex")
                                     (real . (acl2::realpart val))
                                     (imag . (acl2::imagpart val)))))
   ;;((numberp val) (write-string (write-to-string val) stream))
   ((symbolp val) (encode-alist
                   `((type . "sym")
                     (package . ,(package-name (symbol-package val)))
                     (name . ,(symbol-name val)))
                   stream))
   ((recordp val) (encode-record val stream))
   ((and (not *encode-alists-as-plain-lists*)
         (consp val)
         (consp (car val))
         (not (consp (cdar val))))
    ;; can't use encode-alist here, so we've gotta do it ourself.
    (write-string "{" stream)
    (encode-alist-pair '(type . "alist") stream)
    (format stream ",\"~a\": " 'elements)
    (encode-list val stream)
    (write-string "}" stream))
   ((consp val) (encode-list val stream))
   (t (error "Don't know how to encode ~S" val))))

(defun encode-list (val &optional (stream *standard-output*))
  (write-string "[" stream)
  (loop for elt in (butlast val) do
	(encode-value elt stream)
	(write-string ", " stream))
  (encode-value (car (last val)) stream)
  ;; this is needed so we don't just drop the last element of an
  ;; improper list.
  (when (and (consp (last val)) (not (null (cdr (last val)))))
    (write-string ", " stream)
    (encode-value (cdr (last val)) stream))
  (write-string "]" stream))

(defun encode-record (val &optional (stream *standard-output*))
  (write-line "{" stream)
  (encode-alist-pair '(type . "defdata") stream)
  (write-string "," stream)
  (loop for pair in (butlast val) do
	(encode-alist-pair pair stream)
	(write-line "," stream))
  (encode-alist-pair (car (last val)) stream)
  (write-line "" stream)
  (write-string "}" stream))

;;(encode-value 2)
;;(encode-value (list 1 2 3 4))
;;(encode-value (acl2s::nth-foo 324))
;;(encode-value (acl2s::nth-foo 3292834))
;;(encode-value (mapcar #'acl2s::nth-foo (list 1 2 3 4 5)))

(defun encode-to-string (val)
  (let ((s (make-string-output-stream)))
    (handler-case
        (progn
          (encode-value val s)
          (get-output-stream-string s))
      (error (condition) (progn (close s)
                                (signal condition)))
      (:no-error (val) (progn (close s) val)))))

(defun decode-from-string (str)
  (let ((val (json:decode-json-from-string str)))
    (decode-value val)))

(defun decode-from-stream (stream)
  (let ((val (json:decode-json stream)))
    (decode-value val)))


(defun decode-value (val)
  (cond
   ((stringp val) val)
   ((acl2::alistp val) (decode-alist val))
   ((listp val) (mapcar #'decode-value val))
   (t (error "Don't know how to decode ~s" val))))

(defun alist-get (key val)
  (cdr (assoc key val)))

(defun alist-remove (key val)
  (remove-if (lambda (pair) (equal (car pair) key)) val))

(defun decode-alist (val)
  (if (assoc :type val)
      (let ((ty (cdr (assoc :type val))))
        (match ty
          ("int" (values (parse-integer (alist-get :val val))))
          ("rat" (/ (parse-integer (alist-get :n val))
                    (parse-integer (alist-get :d val))))
          ("sym" (values (intern (alist-get :name val) (alist-get :package val))))
          ("defdata" (decode-record (alist-remove :type val)))
          (otherwise (error "Don't know how to decode type ~s" ty))))
    (error "Decoding general alists is not currently supported")))

(defun decode-record (val)
  (mapcar #'(lambda (pair) (cons (car pair) (decode-value (cdr pair)))) val))

;;(decode-from-string (encode-to-string 1))
;;(decode-from-string (encode-to-string "hi"))
;;(decode-from-string (encode-to-string 'hi))
;;(decode-from-string (encode-to-string :hi))
;;(decode-from-string (encode-to-string (acl2s::nth-foo 1)))

;; TODO: only do this if val is a quoted defdata record
(defun unquote-if-needed (val)
  (if (acl2::quotep val)
      (acl2::unquote val)
    val))

(defun encode-counterexample (ctrex &optional (stream *standard-output*))
  (write-string "{" stream)
  (loop for var-ctrex in (butlast ctrex) do
        (encode-alist-pair (cons (car var-ctrex) (unquote-if-needed (second var-ctrex))) stream)
        (write-string "," stream))
  (let ((var-ctrex (car (last ctrex))))
    (encode-alist-pair (cons (car var-ctrex) (unquote-if-needed (second var-ctrex))) stream))
  (write-string "}" stream))

(defun encode-counterexamples (ctrexes &optional (stream *standard-output*))
  (write-string "[" stream)
  (loop for ctrex in (butlast ctrexes) do
        (encode-counterexample ctrex stream)
        (write-string "," stream))
  (encode-counterexample (car (last ctrexes)) stream)
  (write-string "]" stream))
