(in-package :cl-utilities)

(defun copy-array (array &key (undisplace nil))
  "Shallow copies the contents of any array into another array with
equivalent properties.  If array is displaced, then this function will
normally create another displaced array with similar properties,
unless UNDISPLACE is non-NIL, in which case the contents of the array
will be copied into a completely new, not displaced, array."
  (declare (type array array))
  (let ((copy (%make-array-with-same-properties array undisplace)))
    (unless (array-displacement copy)
      (dotimes (n (array-total-size copy))
        (setf (row-major-aref copy n) (row-major-aref array n))))
    copy))

(defun %make-array-with-same-properties (array undisplace)
  "Make an array with the same properties (size, adjustability, etc.)
as another array, optionally undisplacing the array."
  (apply #'make-array
	 (list* (array-dimensions array)
		:element-type (array-element-type array)
		:adjustable (adjustable-array-p array)
		:fill-pointer (when (array-has-fill-pointer-p array)
				(fill-pointer array))
		(multiple-value-bind (displacement offset)
		    (array-displacement array)
		  (when (and displacement (not undisplace))
		    (list :displaced-to displacement
			  :displaced-index-offset offset))))))