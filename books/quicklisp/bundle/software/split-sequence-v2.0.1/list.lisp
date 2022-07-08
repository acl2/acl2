;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-

(in-package :split-sequence)

(declaim (inline
          collect-until count-while
          split-list split-list-if split-list-if-not
          split-list-from-end split-list-from-start split-list-internal))

(declaim (ftype (function (&rest t) (values list unsigned-byte))
                split-list split-list-if split-list-if-not))

(declaim (ftype (function (function list unsigned-byte (or null unsigned-byte) (or null unsigned-byte)
                                    boolean)
                          (values list unsigned-byte))
                split-list-from-start split-list-from-end split-list-internal))

(defun collect-until (predicate list end)
  "Collect elements from LIST until one that satisfies PREDICATE is found.

  At most END elements will be examined. If END is null, all elements will be examined.

  Returns four values:

  * The collected items.
  * The remaining items.
  * The number of elements examined.
  * Whether the search ended by running off the end, instead of by finding a delimiter."
  (let ((examined 0)
        (found nil))
    (flet ((examine (value)
             (incf examined)
             (setf found (funcall predicate value))))
      (loop :for (value . remaining) :on list
            :until (eql examined end)
            :until (examine value)
            :collect value :into result
            :finally (return (values result
                                     remaining
                                     examined
                                     (and (not found)
                                          (or (null end)
                                              (= end examined)))))))))

(defun count-while (predicate list end)
  "Count the number of elements satisfying PREDICATE at the beginning of LIST.

  At most END elements will be counted. If END is null, all elements will be examined."
  (if end
      (loop :for value :in list
            :for i :below end
            :while (funcall predicate value)
            :summing 1)
      (loop :for value :in list
            :while (funcall predicate value)
            :summing 1)))

(defun split-list-internal (predicate list start end count remove-empty-subseqs)
  (let ((count count)
        (done nil)
        (index start)
        (end (when end (- end start)))
        (list (nthcdr start list)))
    (flet ((should-collect-p (chunk)
             (unless (and remove-empty-subseqs (null chunk))
               (when (numberp count) (decf count))
               t))
           (gather-chunk ()
             (multiple-value-bind (chunk remaining examined ran-off-end)
                 (collect-until predicate list end)
               (incf index examined)
               (when end (decf end examined))
               (setf list remaining
                     done ran-off-end)
               chunk)))
      (values (loop :with chunk
                    :until (or done (eql 0 count))
                    :do (setf chunk (gather-chunk))
                    :when (should-collect-p chunk)
                      :collect chunk)
              (+ index
                 (if remove-empty-subseqs
                     (count-while predicate list end) ; chew off remaining empty seqs
                     0))))))

(defun split-list-from-end (predicate list start end count remove-empty-subseqs)
  (let ((length (length list)))
    (multiple-value-bind (result index)
        (split-list-internal predicate (reverse list)
                             (if end (- length end) 0)
                             (- length start) count remove-empty-subseqs)
      (loop :for cons on result
            :for car := (car cons)
            :do (setf (car cons) (nreverse car)))
      (values (nreverse result) (- length index)))))

(defun split-list-from-start (predicate list start end count remove-empty-subseqs)
  (split-list-internal predicate list start end count remove-empty-subseqs))

(defun split-list-if (predicate list start end from-end count remove-empty-subseqs key)
  (let ((predicate (lambda (x) (funcall predicate (funcall key x)))))
    (if from-end
        (split-list-from-end predicate list start end count remove-empty-subseqs)
        (split-list-from-start predicate list start end count remove-empty-subseqs))))

(defun split-list-if-not (predicate list start end from-end count remove-empty-subseqs key)
  (split-list-if (complement predicate) list start end from-end count remove-empty-subseqs key))

(defun split-list
    (delimiter list start end from-end count remove-empty-subseqs test test-not key)
  (let ((predicate (if test-not
                       (lambda (x) (not (funcall test-not delimiter (funcall key x))))
                       (lambda (x) (funcall test delimiter (funcall key x))))))
    (if from-end
        (split-list-from-end predicate list start end count remove-empty-subseqs)
        (split-list-from-start predicate list start end count remove-empty-subseqs))))
