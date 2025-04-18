;; python type definitions

(in-package "ACL2S")
(include-book "string_enum_utils")
(include-book "py_listof")

(set-ccg-time-limit 5)  ;; 5 seconds

(make-event
 `(defconst *types-py-defdata-aliasing-was-enabled* ,(get-acl2s-defaults :defdata-aliasing-enabled (w state))))

(acl2s-defaults :set defdata-aliasing-enabled nil)

;; Strings
(defdata unicode-codepoint-string-brand "UNICODE-STRING")
(defdata unicode-codepoint-string
  (record (kind . unicode-codepoint-string-brand)
          (value . nat-list)))


(defconst *MAXSTRLEN* 1000)

(defun python-string-enum/acc (n seed)
  (declare (xargs :mode :program))
  (declare (ignore n))
  (declare (type (unsigned-byte 31) seed))
  (b* (((mv len seed)
        (select-from-ranges
         ((:min 0 :max 100 :weight 90)
          (:min 101 :max 1000 :weight 9)
          (:min 1001 :max 10000 :weight 1))
         seed))
       ((mv charset-choice seed)
        (defdata::weighted-switch-nat
          '(50 ;; ASCII-only
            2  ;; Emoji-only
            2  ;; Greek-only
            2  ;; Logic-only
            2  ;; Diacritics-only
            2  ;; Compound-only
            40 ;; mixed
            ) seed))
       (length (min *MAXSTRLEN* len))
       ((mv string-contents seed)
        (case charset-choice
          (0 ;; ASCII-only
           (ascii-only-codepoints-enum length seed))
          (1 ;; Emoji-only
           (emoji-only-codepoints-enum length seed))
          (2 ;; Greek-only
           (greek-only-codepoints-enum length seed))
          (3 ;; Logic-only
           (logic-only-codepoints-enum length seed))
          (4 ;; Diacritics-only
           (diacritics-only-codepoints-enum length seed))
          (5 ;; Compound-only
           (compound-only-codepoints-enum length seed))
          (t ;; Mixed
           (mixed-codepoints-enum length seed)))))
    (mv (unicode-codepoint-string "UNICODE-STRING" string-contents) seed)))

(defun python-string-enum (n)
  (declare (xargs :mode :program))
  (b* (((mv x &) (python-string-enum/acc 0 n)))
    x))

(defdata-attach unicode-codepoint-string :enumerator python-string-enum)
(defdata-attach unicode-codepoint-string :enum/acc python-string-enum/acc)

;; Integers

(defun signed-power-of-two-enum-seed (min-expt max-expt seed)
  (declare (xargs :mode :program))
  (declare (type (unsigned-byte 31) seed))
  (b* (((mv expt seed) (defdata::random-integer-between-seed min-expt max-expt seed))
       ((mv sign seed) (random-bool seed)))
    (mv (* (if sign 1 -1) (expt 2 expt)) seed)))

(defun make-nat-upto-2-expt-65 (r1 r2 r3)
  (declare (type (unsigned-byte 31) r1)
           (type (unsigned-byte 31) r2)
           (type (unsigned-byte 31) r3))
  (acl2::logapp 3 r3 (acl2::logapp 31 r1 r2)))

;; Must be able to generate 1- 2^65
(must-fail
  (thm (=> (and (unsigned-byte-p 31 r1)
                (unsigned-byte-p 31 r2)
                (unsigned-byte-p 31 r3))
           (!= (make-nat-upto-2-expt-65 r1 r2 r3) (1- (expt 2 65))))))
;; And 1- 2^65 should be the max that can be generated
(must-succeed
  (thm (=> (and (unsigned-byte-p 31 r1)
                (unsigned-byte-p 31 r2)
                (unsigned-byte-p 31 r3))
           (!= (make-nat-upto-2-expt-65 r1 r2 r3) (expt 2 65)))))

(defun python-int-enum/acc (n seed)  
  (declare (xargs :mode :program))
  (declare (ignore n)
           (type (unsigned-byte 31) seed))
  (b* (((mv choice seed)
        (defdata::weighted-switch-nat 
          '(
            85  ; +- 2^64 +- 2^16
            6   ; +- [1, ..., 2^65]
            6   ; +- powers of 2, + -1,0,1 (each equally likely)
            1   ; -1
            1   ; 0
            1   ; 1
            ) seed)))
    (case choice
      (0  ; +- 2^64 +- 2^16
       (b* (((mv val-64 seed)
             (signed-power-of-two-enum-seed 0 64 seed))
            ((mv val-16 seed)
             (signed-power-of-two-enum-seed 0 16 seed)))
         (mv (+ val-64 val-16) seed)))
      ;; Values between 1 and 2^65, inclusive
      (1 (b* (
              ;; We can't directly generate a random integer between 2 and 2^65. We
              ;; can only generate a random integer with a range of at most 2^63 (on
              ;; versions of ACL2 after e02efb635bcf31a36e55b40a4c56871af090ed30) or
              ;; at most 2^31 (on versions of ACL2 before the above commit).
              ;; I want this to work in both cases, so I will generate 3 random
              ;; integers up to (1- (expt 2 31)) inclusive and combine them.
              ((mv r1 seed) (defdata::genrandom-seed (1- (expt 2 31)) seed))
              ((mv r2 seed) (defdata::genrandom-seed (1- (expt 2 31)) seed))
              ((mv r3 seed) (defdata::genrandom-seed (1- (expt 2 31)) seed))
              (v (make-nat-upto-2-expt-65 r1 r2 r3))
              ((mv sign seed) (random-bool seed)))
           (mv (* (if sign 1 -1) (1+ v)) seed)))
      ;; powers of 2 with exponents between 1 and 65 + {-1,0,1}
      (2 (b* (;; generate a power of 2
              ((mv pow-2 seed) (signed-power-of-two-enum-seed 1 65 seed))
              ;; decide what constant to add to the power of 2 out of -1, 0, and 1
              ((mv constant+1 seed) (switch-nat-safe-seed 3 seed)))
           (mv (+ pow-2 (1- constant+1)) seed)))
      (3 (mv -1 seed))
      (4 (mv 0 seed))
      (t (mv 1 seed)))))

(defun python-int-enum (n)  
  (declare (xargs :mode :program))
  (b* (((mv x &) (python-int-enum/acc 0 n)))
    x))

;; TODO: don't alias, consider disabling for this whole file
(defdata py-integer integer) ;; python doesn't have special values
(defdata-attach py-integer :enumerator python-int-enum)
(defdata-attach py-integer :enum/acc python-int-enum/acc)

(defdata py-pos-inf-keyword "+inf")
(defdata py-neg-inf-keyword "-inf")
(defdata py-nan-keyword "nan")
(defdata py-neg-zero-keyword "-0")
(defdata py-keyword-brand "KEYWORD")
(defdata py-str string)

(defdata py-true-keyword "True")
(defdata py-false-keyword "False")

(defmacro def-py-keyword (name keyword)
  `(defdata ,name (record (kind . py-keyword-brand) (value . ,keyword))))

(def-py-keyword py-pos-inf py-pos-inf-keyword)
(def-py-keyword py-neg-inf py-neg-inf-keyword)
(def-py-keyword py-nan py-nan-keyword)
(def-py-keyword py-neg-zero py-neg-zero-keyword)

(defdata py-float-special-cases (oneof py-pos-inf
                                       py-neg-inf
                                       py-nan
                                       py-neg-zero))

(defconst *max-32-bit-float* (* (expt 2 127) (- 2 (expt 2 -23))))
(defconst *min-normal-32-bit-float* (expt 2 -126))
(defconst *min-subnormal-32-bit-float* (expt 2 -149))
(defconst *max-subnormal-32-bit-float* (* (expt 2 -126) (- 1 (expt 2 -23))))
(defconst *max-32-bit-integer-rep* (expt 2 24)) ;; 1+mantissa length

(defconst *max-64-bit-float* (* (expt 2 1023) (- 2 (expt 2 -52))))
(defconst *min-normal-64-bit-float* (expt 2 -1022))
(defconst *min-subnormal-64-bit-float* (expt 2 -1074))
(defconst *max-subnormal-64-bit-float* (* (expt 2 -1022) (- 1 (expt 2 -52))))
(defconst *max-64-bit-integer-rep* (expt 2 53))

(defun python-float-enum/acc (n seed)
  (declare (xargs :mode :program))
  (declare (ignore n))
  (declare (type (unsigned-byte 31) seed))
  (b* (((mv choice seed)
        (defdata::weighted-switch-nat 
          '(
            74  ;; n/k for n,k integers
            4   ;; +- 2^i + {-1,0,1} for |i| <= 64
            4   ;; +- 2^i + {-1,0,1} for 64 < |i| <= 1024
            3   ;; +- min/max magnitude normal 32-bit float + {-1,0,1}
            3   ;; +- min/max magnitude normal 64-bit float + {-1,0,1}
            2   ;; +- max integer representible as a 32/64 bit float
                ;; (e.g. largest integer x such that all integers from
                ;;  0 to x are exactly representable as floats, and x+1
                ;;  is not exactly representable as a float)
            2   ;; +- largest and smallest magnitude subnormals for 32,64 bit
            1   ; nan
            1   ; +inf
            1   ; -inf
	    1   ; -0
            ) seed)))
    (case choice
      (0 ;; n/k for n,k integers
       (b* (((mv num seed) (python-int-enum/acc 0 seed))
            ((mv den seed) (python-int-enum/acc 0 seed)))
         (mv (if (== den 0)
                 num
               (/ num den)) seed)))
      (1 ;; +- 2^i + {-1,0,1} for |i| <= 64
       (b* (((mv pow-2 seed) (signed-power-of-two-enum-seed -64 64 seed))
            ((mv constant+1 seed) (switch-nat-safe-seed 3 seed)))
         (mv (+ pow-2 (1- constant+1)) seed)))
      (2 ;; +- 2^i + {-1,0,1} for 64 < |i| <= 1024
       (b* (((mv expt-sign seed) (random-bool seed))
            ((mv pow-2 seed) (if expt-sign
                                  (signed-power-of-two-enum-seed 65 1024 seed)
                                (signed-power-of-two-enum-seed -1024 -65 seed)))
            ((mv constant+1 seed) (switch-nat-safe-seed 3 seed)))
         (mv (+ pow-2 (1- constant+1)) seed)))
      (3 ;; +- min/max magnitude normal 32-bit float + {-1,0,1}
       (b* (((mv sign seed) (random-bool seed))
            ((mv largest? seed) (random-bool seed))
            ((mv constant+1 seed) (switch-nat-safe-seed 3 seed)))
         (mv (* (if sign 1 -1)
                (+ (if largest? *min-normal-32-bit-float* *max-32-bit-float*)
                   (1- constant+1)))
             seed)))
      (4 ;; +- min/max magnitude normal 64-bit float + {-1,0,1}
       (b* (((mv sign seed) (random-bool seed))
            ((mv largest? seed) (random-bool seed))
            ((mv constant+1 seed) (switch-nat-safe-seed 3 seed)))
         (mv (* (if sign 1 -1)
                (+ (if largest? *min-normal-64-bit-float* *max-64-bit-float*)
                   (1- constant+1)))
             seed)))
      (5 ;; +- max integer representible as a 32/64 bit float
       (b* (((mv sign seed) (random-bool seed))
            ((mv 64-bit? seed) (random-bool seed)))
         (mv (* (if sign 1 -1)
                (if 64-bit? *max-32-bit-integer-rep* *max-64-bit-integer-rep*))
             seed)))
      (6 ;; +- largest and smallest magnitude subnormals for 32,64 bit
       (b* (((mv sign seed) (random-bool seed))
            ((mv 64-bit?-cross-largest? seed) (switch-nat-safe-seed 4 seed)))
         (mv (* (if sign 1 -1)
                (case 64-bit?-cross-largest?
                  (0 *min-subnormal-32-bit-float*)
                  (1 *max-subnormal-32-bit-float*)
                  (2 *min-subnormal-64-bit-float*)
                  (3 *max-subnormal-64-bit-float*)))
             seed)))
      (7 ;; nan
       (nth-py-nan/acc 0 seed))
      (8 ;; +inf
       (nth-py-pos-inf/acc 0 seed))
      (9 ;; -inf
       (nth-py-neg-inf/acc 0 seed))
      (t ;; -0
       (nth-py-neg-zero/acc 0 seed)))))

(defun python-float-enum (n)
  (declare (xargs :mode :program))
  (b* (((mv x &) (python-float-enum/acc 0 n)))
    x))

(defdata py-float (oneof rational py-float-special-cases))
(defdata-attach py-float :enumerator python-float-enum)
(defdata-attach py-float :enum/acc python-float-enum/acc)

(def-py-keyword py-true py-true-keyword)
(def-py-keyword py-false py-false-keyword)
(defdata py-bool (oneof py-true py-false))

;; nonetype
(defdata py-none-keyword "None")
(def-py-keyword py-none py-none-keyword)


;; bytes
(defnatrange u8 (expt 2 8)) ;; alternatively, (defdata u8 (range integer (0 <= _ < (expt 2 8))))
(defdata py-bytes (listof u8) :do-not-alias t)
(generate-attach-pylistof-enumerators 'py-bytes 'u8)


(acl2s-defaults :set defdata-aliasing-enabled *types-py-defdata-aliasing-was-enabled*)
