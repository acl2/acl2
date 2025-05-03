;; Some miscellaneous definitions from Y86 ACL2 books, including
;; here in case of dependencies. 

(in-package "ACL2")

(defmacro ! (x y)
  (declare (xargs :guard (symbolp x)))
  `(assign ,x ,y))

(defmacro !! (variable new-value)
  ;; Assign without printing the result.
  (declare (xargs :guard t))
  `(mv-let
    (erp result state)
    (assign ,variable ,new-value)
    (declare (ignore result))
    (value (if erp 'Error! ',variable))))

(defthm update-nth-update-nth-same-key
  (equal (update-nth r v1 (update-nth r v2 alst))
	 (update-nth r v1 alst)))

(defthm update-nth-update-nth-different-keys
  (implies (and (natp r1)
		(natp r2)
		(not (equal r1 r2)))
	   (equal (update-nth r1 v1 (update-nth r2 v2 alst))
		  (update-nth r2 v2 (update-nth r1 v1 alst )))))

(local (include-book "arithmetic-5/top" :dir :system))

(defmacro with-arithmetic-help-5 (&rest forms)
  `(encapsulate
    ()
    (local (include-book "arithmetic-5/top" :dir :system))
    (set-default-hints '((nonlinearp-default-hint
                          stable-under-simplificationp
                          hist
                          pspv)))
    ,@forms))

; Functions repeatedly used in processor definitions:
;   LOGAND, LOGIOR, LOGXOR, LOGNOT, and ASH.

 (defthm logand-logand
   (implies (and (natp k)
		 (natp n))
	    (equal (logand (logand k n) n)
		   (logand k n))))

(defthm logand-lessp
  (implies (and (natp k)
		(natp n)
		(< n (expt 2 k)))
	   (equal (logand n (1- (expt 2 k)))
		  n)))

(defthm ash-negative-shift-makes-input-smaller
  (implies (and (integerp x)
		(< 0 x)
		(integerp shift)
		(< shift 0))
	   (< (ash x shift) x))
  :rule-classes :linear)

 (defthm logand-less-than-or-equal
   (implies (natp x)
            (and (<= (binary-logand x y) x)
                 (<= (binary-logand y x) x)))
   :hints (("Goal" :cases ((equal x 0))))
   :rule-classes :linear)

 (defthm logand-greater-or-equal-to-zero
   (implies (or (natp x) (natp y))
            (and (integerp (binary-logand x y))
                 (<= 0 (binary-logand x y))))
   :hints (("Goal" :cases ((equal x 0))))
   :rule-classes :type-prescription)

 (defthm logior-greater-or-equal-to-zero
   (implies (and (natp x) (natp y))
            (and (integerp (logior x y))
                 (<= 0 (logior x y))
                 ))
   :rule-classes :type-prescription)

(encapsulate
 ()
 (local (defun ind-hint-3 (x y n)
	  (declare (xargs :measure (acl2-count n)))
	  (if (or (zp x) (zp y) (zp n))
	      42
	    (ind-hint-3 (floor x 2) (floor y 2) (+ -1 n)))))

 (local (defthm break-logior-apart
	  (implies (and (natp x)
			(natp y))
		   (equal (logior x y)
			  (+ (* 2 (logior (floor x 2)
					  (floor y 2)))
			     (logior (mod x 2)
				     (mod y 2)))))
	  :rule-classes nil))

 (defthm logior-less-than-or-equal
   (implies (and (natp x) (natp y)
                 (< x (expt 2 n))
                 (< y (expt 2 n)))
            (< (logior x y) (expt 2 n)))
   :hints (("Goal" :induct (ind-hint-3 x y n))
           ("Subgoal *1/2.10'4'" :use ((:instance break-logior-apart)))
           ("Subgoal *1/2.9'4'" :use ((:instance break-logior-apart)))
	   ("Subgoal *1/2.6'4'" :use ((:instance break-logior-apart))))
   :rule-classes :linear)
 )

(encapsulate
 ()

 (local
  (defun ind-hint-3 (x y n)
    (if (or (zp x) (zp y) (zp n))
        42
      (ind-hint-3 (floor x 2) (floor y 2) (+ -1 n)))))

 (local
  (defthm break-logxor-apart
    (implies (and (natp x)
                  (natp y))
             (equal (logxor x y)
                    (+ (* 2 (logxor (floor x 2)
                                    (floor y 2)))
                       (logxor (mod x 2)
                               (mod y 2)))))
    :rule-classes nil))

 (local
  (defun ind-hint-2 (x y)
    (if (or (zp x) (zp y))
        42
      (ind-hint-2 (floor x 2) (floor y 2)))))

 (defthm logxor-greater-or-equal-to-zero
   (implies (and (natp x) (natp y))
            (and (integerp (logxor x y))
                 (<= 0 (logxor x y))))
   :hints (("Goal" :induct (ind-hint-2 x y)))
   :rule-classes :type-prescription)

 (defthm logxor-<=-expt-2-to-n
   (implies (and (natp x) (natp y)
                 (< x (expt 2 n))
                 (< y (expt 2 n)))
            (< (logxor x y) (expt 2 n)))
   :hints (("Goal" :induct (ind-hint-3 x y n))
           ("Subgoal *1/2.6'4'" :use ((:instance break-logxor-apart)))
           ("Subgoal *1/2.10'4'" :use ((:instance break-logxor-apart))))
   :rule-classes :linear)
 )

 (defthm integerp-mod
   (implies (and (integerp x)
                 (integerp y))
            (integerp (mod x y))))

(defun gl-int (start by count)
  (declare (xargs :guard (and (natp start)
                              (natp by)
                              (natp count))))
  (if (zp count)
      nil
    (cons start
          (gl-int (+ by start) by (1- count)))))
