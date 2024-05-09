(defpackage :cl-utilities
  (:use :common-lisp)
  (:export #:split-sequence
	   #:split-sequence-if
	   #:split-sequence-if-not
	   #:partition
	   #:partition-if
	   #:partition-if-not
	   
	   #:extremum
	   #:no-extremum
	   #:extremum-fastkey
	   #:extrema
	   #:n-most-extreme
	   #:n-most-extreme-not-enough-elements
	   #:n-most-extreme-not-enough-elements-n
	   #:n-most-extreme-not-enough-elements-subsequence
	   
	   #:read-delimited
	   #:read-delimited-bounds-error
	   #:read-delimited-bounds-error-start
	   #:read-delimited-bounds-error-end
	   #:read-delimited-bounds-error-sequence
	   
	   #:expt-mod
	   
	   #:collecting
	   #:collect
	   #:with-collectors
	   
	   #:with-unique-names
	   #:with-gensyms
	   #:list-binding-not-supported
	   #:list-binding-not-supported-binding

	   #:once-only
	   
	   #:rotate-byte
	   
	   #:copy-array

	   #:compose))

#+split-sequence-deprecated
(defpackage :split-sequence
  (:documentation "This package mimics SPLIT-SEQUENCE for compatibility with
packages that expect that system.")
  (:use :cl-utilities)
  (:export #:split-sequence #:split-sequence-if #:split-sequence-if-not))
