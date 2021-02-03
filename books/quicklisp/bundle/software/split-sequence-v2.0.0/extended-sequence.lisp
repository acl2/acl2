;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-

(in-package :split-sequence)

;;; For extended sequences, we make the assumption that all extended sequences
;;; can be at most ARRAY-DIMENSION-LIMIT long. This seems to match what SBCL
;;; assumes about them.

;;; TODO test this code. This will require creating such an extended sequence.

(deftype extended-sequence ()
  '(and sequence (not list) (not vector)))

(declaim (inline
          split-extended-sequence split-extended-sequence-if split-extended-sequence-if-not
          split-extended-sequence-from-end split-extended-sequence-from-start))

(declaim (ftype (function (&rest t) (values list unsigned-byte))
                split-extended-sequence split-extended-sequence-if split-extended-sequence-if-not))

(declaim (ftype (function (function extended-sequence array-index
                                    (or null fixnum) (or null fixnum) boolean)
                          (values list fixnum))
                split-extended-sequence-from-start split-extended-sequence-from-end))

(defun split-extended-sequence
    (delimiter sequence start end from-end count remove-empty-subseqs test test-not key)
  (cond
    ((and (not from-end) (null test-not))
     (split-extended-sequence-from-start (lambda (sequence start)
                                           (position delimiter sequence :start start :key key :test test))
                                         sequence start end count remove-empty-subseqs))
    ((and (not from-end) test-not)
     (split-extended-sequence-from-start (lambda (sequence start)
                                           (position delimiter sequence :start start :key key :test-not test-not))
                                         sequence start end count remove-empty-subseqs))
    ((and from-end (null test-not))
     (split-extended-sequence-from-end (lambda (sequence end)
                                         (position delimiter sequence :end end :from-end t :key key :test test))
                                       sequence start end count remove-empty-subseqs))
    (t
     (split-extended-sequence-from-end (lambda (sequence end)
                                         (position delimiter sequence :end end :from-end t :key key :test-not test-not))
                                       sequence start end count remove-empty-subseqs))))

(defun split-extended-sequence-if
    (predicate sequence start end from-end count remove-empty-subseqs key)
  (if from-end
      (split-extended-sequence-from-end (lambda (sequence end)
                                          (position-if predicate sequence :end end :from-end t :key key))
                                        sequence start end count remove-empty-subseqs)
      (split-extended-sequence-from-start (lambda (sequence start)
                                            (position-if predicate sequence :start start :key key))
                                          sequence start end count remove-empty-subseqs)))

(defun split-extended-sequence-if-not
    (predicate sequence start end from-end count remove-empty-subseqs key)
  (if from-end
      (split-extended-sequence-from-end (lambda (sequence end)
                                          (position-if-not predicate sequence :end end :from-end t :key key))
                                        sequence start end count remove-empty-subseqs)
      (split-extended-sequence-from-start (lambda (sequence start)
                                            (position-if-not predicate sequence :start start :key key))
                                          sequence start end count remove-empty-subseqs)))

(defun split-extended-sequence-from-end (position-fn sequence start end count remove-empty-subseqs)
  (declare (optimize (speed 3) (debug 0))
           (type (function (extended-sequence fixnum) (or null fixnum)) position-fn))
  (loop
    :with length = (length sequence)
    :with end = (or end length)
    :for right := end :then left
    :for left := (max (or (funcall position-fn sequence right) -1)
                      (1- start))
    :unless (and (= right (1+ left)) remove-empty-subseqs)
      :if (and count (>= nr-elts count))
        :return (values (nreverse subseqs) right)
      :else
        :collect (subseq sequence (1+ left) right) into subseqs
        :and :sum 1 :into nr-elts :of-type fixnum
    :until (< left start)
    :finally (return (values (nreverse subseqs) (1+ left)))))

(defun split-extended-sequence-from-start (position-fn sequence start end count remove-empty-subseqs)
  (declare (optimize (speed 3) (debug 0))
           (type (function (extended-sequence fixnum) (or null fixnum)) position-fn))
  (loop
    :with length = (length sequence)
    :with end = (or end length)
    :for left := start :then (1+ right)
    :for right := (min (or (funcall position-fn sequence left) length)
                       end)
    :unless (and (= right left) remove-empty-subseqs)
      :if (and count (>= nr-elts count))
        :return (values subseqs left)
      :else
        :collect (subseq sequence left right) :into subseqs
        :and :sum 1 :into nr-elts :of-type fixnum
    :until (>= right end)
    :finally (return (values subseqs right))))
