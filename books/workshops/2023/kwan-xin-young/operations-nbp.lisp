;; The following code pieces are modified from work by Warren A. Hunt, Jr.,
;; so that only theorems relevant to capabilities.lisp are included.

(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))
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

(defmacro nbp (n b)
  `(and (integerp ,n)
        (<= 0 ,n)
        (< ,n (expt 2 ,b))))

(defmacro mk-name (&rest x)
  `(intern (concatenate 'string ,@x) "ACL2"))

(defun nbp-def-n (n)
  (declare (xargs :mode :program    ;; PACKN is a :program mode function
                  :guard (posp n)))
  (let* ((str-n          (symbol-name (if (< n 10)
                                          (packn (list 0 n))
                                          (packn (list n)))))
         (str-2-to-n     (symbol-name (packn (list (expt 2 n)))))

         (nbp-n-logand-nbp-n-less-than
          (mk-name "NBP" str-n "-LOGAND-NBP" str-n "-LESS-THAN-" str-2-to-n)))
    (list
     `(defthm ,nbp-n-logand-nbp-n-less-than
        (implies (or (nbp x ,n)
                     (nbp y ,n))
                 (< (logand x y) ,(expt 2 n)))
        :rule-classes :linear))))

(defun nbp-defs (lst)
  (declare (xargs :mode :program
                  :guard (pos-listp lst)))
  (if (atom lst) nil
    (append (nbp-def-n (car lst))
            (nbp-defs (cdr lst)))))

(defmacro defuns-nbp (&rest lst)
  (cons 'progn (nbp-defs lst)))

(defuns-nbp 1 2 3 4 5 8 16 24 30 32 60 64 128)


; It is expected that all lemmas directly dealing with the functions
; have been proven -- so these function are disabled.

(in-theory (disable logand))
(in-theory (disable logxor))
(in-theory (disable logior))
(in-theory (disable ash))
