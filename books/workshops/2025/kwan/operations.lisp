;; Book containing macros and definitions related to machine word
;; arithmetic, modified from Y86 ACL2 books.
(in-package "ACL2")
(include-book "misc-events")

; Declarations
(defmacro u01 (x)   `(the (unsigned-byte  1) ,x))
(defmacro u02 (x)   `(the (unsigned-byte  2) ,x))
(defmacro u03 (x)   `(the (unsigned-byte  3) ,x))
(defmacro u04 (x)   `(the (unsigned-byte  4) ,x))
(defmacro u05 (x)   `(the (unsigned-byte  5) ,x))
(defmacro u08 (x)   `(the (unsigned-byte  8) ,x))
(defmacro u16 (x)   `(the (unsigned-byte 16) ,x))
(defmacro u24 (x)   `(the (unsigned-byte 24) ,x))
(defmacro u28 (x)   `(the (unsigned-byte 28) ,x))
(defmacro u32 (x)   `(the (unsigned-byte 32) ,x))
(defmacro u60 (x)   `(the (unsigned-byte 60) ,x))
(defmacro u64 (x)   `(the (unsigned-byte 64) ,x))
(defmacro u128 (x)   `(the (unsigned-byte 128) ,x))

; Natural-number recognizers
(defmacro n01p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2  1))))
(defmacro n02p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2  2))))
(defmacro n03p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2  3))))
(defmacro n04p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2  4))))
(defmacro n05p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2  5))))
(defmacro n07p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2  7))))
(defmacro n08p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2  8))))
(defmacro n10p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 10))))
(defmacro n16p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 16))))
(defmacro n20p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 20))))
(defmacro n21p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 21))))
(defmacro n24p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 24))))
(defmacro n28p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 28))))
(defmacro n30p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 30))))
(defmacro n32p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 32))))
(defmacro n60p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 60))))
(defmacro n64p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 64))))

(defmacro n06p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 6))))
(defmacro n09p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 9))))
(defmacro n11p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 11))))
(defmacro n12p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 12))))
(defmacro n13p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 13))))
(defmacro n14p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 14))))
(defmacro n17p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 17))))
(defmacro n24p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 24))))
(defmacro n26p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 26))))
(defmacro n128p (x) `(and (integerp ,x) (<= 0 ,x) (< ,x ,(expt 2 128))))

; Natural-number truncation
(defmacro n01 (x) `(logand ,x ,(1- (expt 2  1))))
(defmacro n02 (x) `(logand ,x ,(1- (expt 2  2))))
(defmacro n03 (x) `(logand ,x ,(1- (expt 2  3))))
(defmacro n04 (x) `(logand ,x ,(1- (expt 2  4))))
(defmacro n05 (x) `(logand ,x ,(1- (expt 2  5))))
(defmacro n07 (x) `(logand ,x ,(1- (expt 2  7))))
(defmacro n08 (x) `(logand ,x ,(1- (expt 2  8))))
(defmacro n10 (x) `(logand ,x ,(1- (expt 2 10))))
(defmacro n12 (x) `(logand ,x ,(1- (expt 2 12))))
(defmacro n16 (x) `(logand ,x ,(1- (expt 2 16))))
(defmacro n20 (x) `(logand ,x ,(1- (expt 2 20))))
(defmacro n21 (x) `(logand ,x ,(1- (expt 2 21))))
(defmacro n24 (x) `(logand ,x ,(1- (expt 2 24))))
(defmacro n28 (x) `(logand ,x ,(1- (expt 2 28))))
(defmacro n30 (x) `(logand ,x ,(1- (expt 2 30))))
(defmacro n32 (x) `(logand ,x ,(1- (expt 2 32))))
(defmacro n60 (x) `(logand ,x ,(1- (expt 2 60))))
(defmacro n64 (x) `(logand ,x ,(1- (expt 2 64))))

(defmacro n06 (x) `(logand ,x ,(1- (expt 2  6))))
(defmacro n09 (x) `(logand ,x ,(1- (expt 2 09))))
(defmacro n11 (x) `(logand ,x ,(1- (expt 2 11))))
(defmacro n13 (x) `(logand ,x ,(1- (expt 2 13))))
(defmacro n14 (x) `(logand ,x ,(1- (expt 2 14))))
(defmacro n17 (x) `(logand ,x ,(1- (expt 2 17))))
(defmacro n24 (x) `(logand ,x ,(1- (expt 2 24))))
(defmacro n26 (x) `(logand ,x ,(1- (expt 2 26))))
(defmacro n128 (x) `(logand ,x ,(1- (expt 2 128))))

; Fixed-width, natural-number addition
(defmacro n01+ (x y) `(n01 (+ ,x ,y)))
(defmacro n02+ (x y) `(n02 (+ ,x ,y)))
(defmacro n03+ (x y) `(n03 (+ ,x ,y)))
(defmacro n04+ (x y) `(n04 (+ ,x ,y)))
(defmacro n05+ (x y) `(n05 (+ ,x ,y)))
(defmacro n08+ (x y) `(n08 (+ ,x ,y)))
(defmacro n16+ (x y) `(n16 (+ ,x ,y)))
(defmacro n24+ (x y) `(n24 (+ ,x ,y)))
(defmacro n28+ (x y) `(n28 (+ ,x ,y)))
(defmacro n30+ (x y) `(n30 (+ ,x ,y)))
(defmacro n32+ (x y) `(n32 (+ ,x ,y)))
(defmacro n60+ (x y) `(n60 (+ ,x ,y)))
(defmacro n64+ (x y) `(n64 (+ ,x ,y)))
(defmacro n128+ (x y) `(n128 (+ ,x ,y)))

; Fixed-width, natural-number subtraction
(defmacro n01- (x y) `(n01 (- ,x ,y)))
(defmacro n02- (x y) `(n02 (- ,x ,y)))
(defmacro n03- (x y) `(n03 (- ,x ,y)))
(defmacro n04- (x y) `(n04 (- ,x ,y)))
(defmacro n05- (x y) `(n05 (- ,x ,y)))
(defmacro n08- (x y) `(n08 (- ,x ,y)))
(defmacro n16- (x y) `(n16 (- ,x ,y)))
(defmacro n24- (x y) `(n24 (- ,x ,y)))
(defmacro n28- (x y) `(n28 (- ,x ,y)))
(defmacro n30- (x y) `(n30 (- ,x ,y)))
(defmacro n32- (x y) `(n32 (- ,x ,y)))
(defmacro n60- (x y) `(n60 (- ,x ,y)))
(defmacro n64- (x y) `(n64 (- ,x ,y)))

(defmacro n128- (x y) `(n128 (- ,x ,y)))


; Function generator

(defmacro mk-name (&rest x)
  `(intern (concatenate 'string ,@x) "ACL2"))

(defun np-def-n (n)
  (declare (xargs :mode :program    ;; PACKN is a :program mode function
                  :guard (posp n)))
  (let* ((str-n          (symbol-name (if (< n 10)
                                          (packn (list 0 n))
                                        (packn (list n)))))
         (str-2-to-n     (symbol-name (packn (list (expt 2 n)))))

         (nXYp           (mk-name "N" str-n "P"))
         (iXYp           (mk-name "I" str-n "P"))
         (ntoi           (mk-name "N" str-n "-TO-I" str-n))
         (iton           (mk-name "I" str-n "-TO-N" str-n))

         (nXYp-logand-nXYp-less-than
          (mk-name "N" str-n "P-LOGAND-N" str-n "P-LESS-THAN-" str-2-to-n))
         (nXYp-logxor-nXYp-less-than
          (mk-name "N" str-n "P-LOGXOR-N" str-n "P-LESS-THAN-" str-2-to-n))
         (nXYp-logior-nXYp-less-than
          (mk-name "N" str-n "P-LOGIOR-N" str-n "P-LESS-THAN-" str-2-to-n))
         )
    (list
     ;; Integer functions
     `(defun ,iXYp (x)
        (declare (xargs :guard t))
        (and (integerp x)
             (<= ,(- (expt 2 (1- n))) x)
             (< x ,(expt 2 (1- n)))))

     `(defun ,ntoi (x)
        (declare (xargs :guard (,nXYp x)))
        (if (< x ,(expt 2 (1- n))) x (- x ,(expt 2 n))))

     `(defun ,iton (x)
        (declare (xargs :guard (,iXYp x)))
        (if (< x 0) (+ x ,(expt 2 n)) x))

     `(in-theory (disable ,iXYp))

     `(defthm ,nXYp-logand-nXYp-less-than
        (implies (or (,nXYp x)
                     (,nXYp y))
                 (< (logand x y) ,(expt 2 n)))
        :rule-classes :linear)

     `(defthm ,nXYp-logxor-nXYp-less-than
        (implies (and (,nXYp x)
                      (,nXYp y))
                 (< (logxor x y) ,(expt 2 n)))
        :rule-classes :linear
        :hints
        (("Goal"
          :in-theory (disable logxor logxor-<=-expt-2-to-n)
          :use ((:instance logxor-<=-expt-2-to-n (n ,n))))))

     `(defthm ,nXYp-logior-nXYp-less-than
        (implies (and (,nXYp x)
                      (,nXYp y))
                 (< (logior x y) ,(expt 2 n)))
        :rule-classes :linear
        :hints
        (("Goal"
          :in-theory (disable logior logior-less-than-or-equal)
          :use ((:instance logior-less-than-or-equal (n ,n))))))
     )))


(defmacro defuns-n ()
  (cons 'progn (np-def-n 1)))

; :trans (defuns-n)  ; For testing the NP-DEF-N macro

(defun np-defs (lst)
  (declare (xargs :mode :program
                  :guard (pos-listp lst)))
  (if (atom lst) nil
    (append (np-def-n (car lst))
            (np-defs (cdr lst)))))

(defmacro defuns-np (&rest lst)
  (cons 'progn (np-defs lst)))

(defuns-np 1 2 3 4 5 8 16 24 30 32 60 64 128)

; It is expected that all lemmas directly dealing with the functions
; have been proven -- so these function are disabled.
(in-theory (disable logand))
(in-theory (disable logxor))
(in-theory (disable logior))

(with-arithmetic-help-5
 (defthm ash-n02p-is-zero-or-positive
   (implies (natp x)
            (<= 0 (ash x n)))
   :rule-classes :linear))

(in-theory (disable ash))
