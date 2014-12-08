; logops-efficiency-hack.lsp -- an efficiency hack for logops definitions
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; [Jared] I split this out of logops-definitions because it was just comments
; and seems rather unweildy.

(in-package "ACL2")

;;;****************************************************************************
;;;
;;;    Efficiency Hack
;;;
;;;****************************************************************************

;   A hack that may increase the efficiency of logical operations and byte
;   operations.
;
;   WARNING: USING THIS HACK MAY RENDER ACL2 UNSOUND AND/OR CAUSE HARD LISP
;   ERRORS.  Note that this warning only applies if we have made a mistake in
;   programming this hack, or if you are calling these functions on values that
;   do not satisfy their guards.
;
;   Our extensions to the CLTL logical operations, and the portable
;   implementations of byte functions are coded to simplify formal reasoning.
;   Thus they are specified in terms of +, -, *, FLOOR, MOD, and EXPT.  One
;   would not expect that these definitions provide the most efficient
;   implementations of these functions, however.  Therefore, we have provided
;   the following hack, which may decrease the runtime for large applications
;   written in terms of the functions defined in this library.
;
;   The hack consists of redefining the logical operations and byte functions
;   "behind the back" of ACL2.  There is no guarantee that using this hack will
;   improve efficiency.  There is also no formal guarantee that these new
;   definitions are equivalent to those formally defined in the
;   "logops-definitions" book, or that the guards are satisfied for these new
;   definitions.  Thus, using this hack may render ACL2 unsound, or cause hard
;   lisp errors if we have coded this hack incorrectly.  The hack consists of a
;   set of definitions which are commented out in the source code for the book
;   "logops-definitions.lisp".  To use this hack, do the following:
;
;   1.  Locate the source code for "logops-definitions.lisp".
;
;   2.  Look at the very end of the file.
;
;   3.  Copy the hack definitions into another file.
;
;   4.  Leave the ACL2 command loop and enter the Common Lisp ACL2 package.
;
;   5.  Compile the hack definitions file and load the object code just created
;       into an ACL2 session.



;;  Begin Efficiency Hack Definitions

;;  The heuristic behind this hack is that logical operations are faster than
;;  arithmetic operations (esp. FLOOR and MOD), and the idea that it is
;;  faster to look up a value from a table than to create new integers.  We
;;  believe that for typical hardware specification applications that many of
;;  the integers presented to LOGHEAD and LOGEXT will already be in their
;;  normalized forms.
;;
;;  We define macros, e.g., |logmask|, that represent a simple efficient
;;  definition of the functions for use when the second heuristic fails.  We
;;  define macros, e. g., |fast-logmask| that define the table
;;  lookup-versions given certain preconditions.

#+monitor-logops (defvar |*loghead-monitor*| #(0 0 0 0))
#+monitor-logops (defvar |*logext-monitor*| #(0 0 0 0))
#+monitor-logops (defvar |*rdb-monitor*| #(0 0 0 0 0 0 0))
#+monitor-logops (defvar |*wrb-monitor*| #(0 0 0 0 0 0 0))

#+monitor-logops
(defun |reset-logops-monitors| ()
  (setf |*loghead-monitor*| #(0 0 0 0))
  (setf |*logext-monitor*| #(0 0 0 0))
  (setf |*rdb-monitor*| #(0 0 0 0 0 0 0))
  (setf |*wrb-monitor*| #(0 0 0 0 0 0 0)))

#+monitor-logops
(defun |print-logops-monitors| ()
  (|print-size-monitor| 'LOGHEAD |*loghead-monitor*|)
  (|print-size-monitor| 'LOGEXT |*logext-monitor*|)
  (|print-bsp-monitor| 'RDB |*rdb-monitor*|)
  (|print-bsp-monitor| 'WRB |*wrb-monitor*|))

#+monitor-logops
(defun |size-monitor| (monitor size i)
  (incf (aref monitor 0))
  (if (eq (type-of i) 'BIGNUM) (incf (aref monitor 1)))
  (if (< i 0) (incf (aref monitor 2)))
  (if (< size 32) (incf (aref monitor 3))))

#+monitor-logops
(defun |print-size-monitor| (fn monitor)
  (format t "~s was called: ~d times, on ~d BIGNUMS, on ~d negative ~
	       numbers,~%and ~d times with size < 32.~%~%"
	    fn (aref monitor 0) (aref monitor 1) (aref monitor 2)
	    (aref monitor 3)))

#+monitor-logops
(defun |bsp-monitor| (monitor bsp i)
  (let ((size (car bsp))
	  (pos (cdr bsp)))
    (incf (aref monitor 0))
    (if (eq (type-of i) 'BIGNUM) (incf (aref monitor 1)))
    (if (< i 0) (incf (aref monitor 2)))
    (if (< size 32) (incf (aref monitor 3)))
    (if (< pos 32) (incf (aref monitor 4)))
    (if (< (+ size pos) 32) (incf (aref monitor 5)))
    (if (= size 1) (incf (aref monitor 6)))))

#+monitor-logops
(defun |print-bsp-monitor| (fn monitor)
  (format t "~s was called: ~d times, on ~d BIGNUMS, on ~d negative ~
	       numbers,~%~
	       ~d times with size < 32, ~d times with pos < 32, ~%~
	       ~d times with size+pos < 32, and ~d times with size = 1.~%~%"
	    fn (aref monitor 0) (aref monitor 1) (aref monitor 2)
	    (aref monitor 3) (aref monitor 4) (aref monitor 5)
	    (aref monitor 6)))


(defconstant *logops-efficiency-hack-mask-table*
  #(#x00000000 #x00000001 #x00000003 #x00000007
	#x0000000F #x0000001F #x0000003F #x0000007F
	#x000000FF #x000001FF #x000003FF #x000007FF
	#x00000FFF #x00001FFF #x00003FFF #x00007FFF
	#x0000FFFF #x0001FFFF #x0003FFFF #x0007FFFF
	#x000FFFFF #x001FFFFF #x003FFFFF #x007FFFFF
	#x00FFFFFF #x01FFFFFF #x03FFFFFF #x07FFFFFF
	#x0FFFFFFF #x1FFFFFFF #x3FFFFFFF #x7FFFFFFF))

(defconstant *logops-efficiency-hack-mask-bar-table*
  #(#x-00000001 #x-00000002 #x-00000004 #x-00000008
	#x-00000010 #x-00000020 #x-00000040 #x-00000080
	#x-00000100 #x-00000200 #x-00000400 #x-00000800
	#x-00001000 #x-00002000 #x-00004000 #x-00008000
	#x-00010000 #x-00020000 #x-00040000 #x-00080000
	#x-00100000 #x-00200000 #x-00400000 #x-00800000
	#x-01000000 #x-02000000 #x-04000000 #x-08000000
	#x-10000000 #x-20000000 #x-40000000 #x-80000000))

(defconstant *logops-efficiency-hack-bit-mask-table*
  #(#x00000001 #x00000002 #x00000004 #x00000008
	#x00000010 #x00000020 #x00000040 #x00000080
	#x00000100 #x00000200 #x00000400 #x00000800
	#x00001000 #x00002000 #x00004000 #x00008000
	#x00010000 #x00020000 #x00040000 #x00080000
	#x00100000 #x00200000 #x00400000 #x00800000
	#x01000000 #x02000000 #x04000000 #x08000000
	#x10000000 #x20000000 #x40000000 #x80000000))

(defconstant *logops-efficiency-hack-bit-mask-bar-table*
  #(#x-00000002 #x-00000003 #x-00000005 #x-00000009
	#x-00000011 #x-00000021 #x-00000041 #x-00000081
	#x-00000101 #x-00000201 #x-00000401 #x-00000801
	#x-00001001 #x-00002001 #x-00004001 #x-00008001
	#x-00010001 #x-00020001 #x-00040001 #x-00080001
	#x-00100001 #x-00200001 #x-00400001 #x-00800001
	#x-01000001 #x-02000001 #x-04000001 #x-08000001
	#x-10000001 #x-20000001 #x-40000001 #x-80000001))

(defmacro |mask| (size)
  ;; size < 32
  `(AREF *LOGOPS-EFFICIENCY-HACK-MASK-TABLE* ,size))

(defmacro |mask-bar| (size)
  ;; size < 32
  `(AREF *LOGOPS-EFFICIENCY-HACK-MASK-BAR-TABLE* ,size))

(defmacro |bit-mask| (pos)
  ;; pos < 32
  `(AREF *LOGOPS-EFFICIENCY-HACK-BIT-MASK-TABLE* ,pos))

(defmacro |bit-mask-bar| (pos)
  ;; pos < 32
  `(AREF *LOGOPS-EFFICIENCY-HACK-BIT-MASK-BAR-TABLE* ,pos))

(defun logcar (i)
  (declare (type integer i))
  (if (oddp i) 1 0))

(defun logcdr (i)
  (declare (type integer i))
  (ash i -1))

(defun logcons (b i)
  (declare (type (integer 0 1) b) (type integer i))
  (logior b (ash i 1)))

(defmacro |logmask-bar| (size)
  `(ASH -1 ,size)))

(defmacro |logmask| (size)
  `(LOGNOT (|logmask-bar| ,size)))

(defun logmask (size)
  (declare (type (integer 0 *) size))
  (if (< size 32)
	  (|mask| size)
	(|logmask| size)))

(defmacro |loghead| (size i)
  (let ((mask (gensym)))
	`(LET ((,mask (IF (< ,size 32) (|mask| ,size) (|logmask| ,size))))
	   (IF (AND (>= ,i 0) (<= ,i ,mask))
	       ,i				;i already normalized.
	     (LOGAND ,i ,mask)))))

(defun loghead (size i)
  (declare (type (integer 0 *) size) (type integer i))
  #+monitor-logops (|size-monitor| |*loghead-monitor*| size i)
  (|loghead| size i))

(defmacro |logtail| (pos i)
  `(ASH ,i (- ,pos)))

(defun logtail (pos i)
  (declare (type (integer 0 *) pos) (type integer i))
  (|logtail| pos i))

(defmacro |logapp| (size i j)
  `(LOGIOR (LOGHEAD ,size ,i) (ASH ,j ,size)))

(defun logapp (size i j)
  (declare (type (integer 0 *) size) (type integer i j))
  (|logapp| size i j))

(defparameter *logops-efficiency-hack-logrpl-bsp* '(0 . 0))

(defun logrpl (size i j)
  (declare (type (integer 0 *) size) (type integer i j))
  (setf (car *logops-efficiency-hack-logrpl-bsp*) size)
  (wrb i *logops-efficiency-hack-logrpl-bsp* j))

(defun logext (size i)
  (declare (type (integer 0 *) size) (type integer i))
  #+monitor-logops (|size-monitor| |*logext-monitor*| size i)
  (if (<= size 32)
	  (if (= (the fixnum size) 0)
	      0
	    (let ((pos (the fixnum (- (the fixnum size) 1))))
	      (if (<= 0 i)
		  (let ((mask (|mask| pos)))
		    (if (<= i mask)
			i
		      (if (logbitp pos i)
			  (logorc2 i mask)
			(logand i mask))))
		(let ((mask (|mask-bar| pos)))
		  (if (<= mask i)
		      i
		    (if (logbitp pos i)
			(logior i mask)
		      (logandc2 i mask)))))))
	(let ((pos (1- size)))
	  (if (<= 0 i)
	      (let ((mask (|logmask| pos)))
		(if (<= i mask)
		    i
		  (if (logbitp pos i)
		      (logorc2 i mask)
		    (logand i mask))))
	    (let ((mask (|logmask-bar| pos)))
	      (if (<= mask i)
		  i
		(if (logbitp pos i)
		    (logior i mask)
		  (logandc2 i mask))))))))

;; In GCL, (BYTE size pos) = (CONS size pos) = (BSP size pos).
;;
;; Reading/writing single bits are an important use of RDB/WRB so we handle
;; them specially.  If the byte position is 0 we can also save a few
;; operations.

(defun rdb (bsp i)
  (declare (type cons bsp) (type integer i))
  #+monitor-logops (|bsp-monitor| |*rdb-monitor*| bsp i)
  (let ((size (car bsp))
	    (pos (cdr bsp)))
	(if (< size 32)
	    (if (= size 1)
		(if (logbitp pos i) 1 0)
	      (if (= pos 0)
		  (logand i (|mask| size))
		(logand (|logtail| pos i) (|mask| size))))
	  (if (= pos 0)
	      (logandc2 i (|logmask-bar| size))
	    (logandc2 (|logtail| pos i) (|logmask-bar| size))))))

(defun wrb (i bsp j)
  (declare (type cons bsp) (type integer i j))
  #+monitor-logops (|bsp-monitor| |*wrb-monitor*| bsp i)
  (let ((size (car bsp))
	    (pos (cdr bsp)))
	(if (< size 32)
	    (if (= size 1)
		(if (< pos 32)
		    (cond
		     ((= i 0) (logand j (|bit-mask-bar| pos)))
		     ((or (= i 1) (oddp i)) (logior j (|bit-mask| pos)))
		     (t (logand j (|bit-mask-bar| pos))))
		  (cond
		   ((= i 0) (logandc2 j (ash 1 pos)))
		   ((or (= i 1) (oddp i)) (logior j (ash 1 pos)))
		   (t (logandc2 j (ash 1 pos)))))
	      (if (= pos 0)
		  (logior (logand j (|mask-bar| size))
			  (|loghead| size i))
		(logior (logandc2 j (ash (|mask| size) pos))
			(ash (|loghead| size i) pos))))
	  (if (= pos 0)
	      (logior (logand j (|logmask-bar| size))
		      (|loghead| size i))
	    (logior (logandc2 j (ash (|logmask| size) pos))
		    (ash (|loghead| size i) pos))))))

(defun rdb-test (bsp i)
	(declare (type cons bsp) (type integer i))
	#+gcl
	(ldb-test bsp i)
	#-gcl
	(ldb-test (byte (car bsp) (cdr bsp)) i))

(defun rdb-field (bsp i)
	(declare (type cons bsp) (type integer i))
	#+gcl
	(mask-field bsp i)
	#-gcl
	(mask-field (byte (car bsp) (cdr bap)) i))

(defun wrb-field (i bsp j)
	(declare (type cons bsp) (type integer i j))
	#+gcl
	(deposit-field i bsp j)
	#-gcl
	(deposit-field i (byte (car bsp) (cdr bsp)) j))

;  MERGE-BYTE is optimized for merging bits.  This definition depends on
;  the strong guards from ACL2.

(defun merge-byte (i size pos j)
	(if (= i 0)
	    j
	  (+ j (if (= size 1)
		   (if (< pos 32)
		       (|bit-mask| pos)
		     (ash 1 pos))
		 (ash i pos)))))

