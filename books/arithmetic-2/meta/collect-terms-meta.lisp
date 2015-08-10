; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; collect-terms.lisp
;;;
;;; This book contains the code for constructing some meta-rules
;;; which will collect "like" addends/factors in a sum/product.
;;; The meta rules massage terms into forms such that the rules
;;; for collect-+ and friends (in common-meta.lisp) can do the
;;; real work.
;;;
;;; See top.lisp for a description of the theories exported from
;;; this book and cancel-terms-meta.
;;;
;;; Pseudo-Example:
;;; collect-addends
;;; (+ x y z (* 2 x))
;;; ===>
;;; (un-hide-+ (collect-+ (hide x) (hide (* 2 x)))
;;;            (hide (+ y z)))
;;;
;;; Organization of Book:
;;;
;;; 1. Background.
;;; 2. Making the meta-functions and -rules.
;;; 3. Cleanup.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 1. Background.

(in-package "ACL2")

(include-book "common-meta")

(local (include-book "../pass1/top"))

(local (in-theory (disable my-apply-1)))


;; NOTE: Should I do anything about gathering
;; (* (numerator x) ... (/ (denominator x))?

(local
 (defthm hide-revealed
   (equal (hide x)
	  x)
   :hints (("Goal" :expand (hide x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 2. Making the meta-functions and -rules.

(defmacro make-collecting-meta (name pattern-fun bin-op)

; Define a meta function, prove a meta rule, and locally disable
; the rule.

  (let ((fn-name (intern-name (list name "-FN")))
	(thm-name (intern-name (list name "-THM"))))

    `(progn

       (defun ,FN-NAME (term)
         (if (and (nvariablep term)
	          (not (fquotep term))
	          (eq (ffn-symb term) ,BIN-OP))
   	     (let ((pattern (my-apply-1 ,PATTERN-FUN (arg1 term))))
	       (mv-let (flag new-term)
                 (new-term (arg2 term) (arg1 term)
		           pattern ,PATTERN-FUN ,BIN-OP)
	         (if flag
		     new-term
	           term)))
           term))

       (defthm ,THM-NAME
         (equal (eva term a)
	        (eva (,FN-NAME term) a))
         :rule-classes ((:meta :trigger-fns (,(unquote BIN-OP)))))

       (local
	(in-theory (disable ,THM-NAME))))))

(make-collecting-meta collect-addends
		      'addend-pattern
		      'BINARY-+)

(make-collecting-meta collect-factors-gather-exponents
		      'factor-pattern-gather-exponents
		      'BINARY-*)

(make-collecting-meta collect-factors-scatter-exponents
		      'factor-pattern-scatter-exponents
		      'BINARY-*)

#|
 (PROGN (DEFUN COLLECT-ADDENDS-FN (TERM)
               (IF (AND (NVARIABLEP TERM)
                        (NOT (FQUOTEP TERM))
                        (EQ (FFN-SYMB TERM) 'BINARY-+))
                   (LET ((PATTERN (MY-APPLY-1 'ADDEND-PATTERN
                                              (ARG1 TERM))))
                        (MV-LET (FLAG NEW-TERM)
                                (NEW-TERM (ARG2 TERM)
                                          (ARG1 TERM)
                                          PATTERN 'ADDEND-PATTERN
                                          'BINARY-+)
                                (IF FLAG NEW-TERM TERM)))
                   TERM))
        (DEFTHM COLLECT-ADDENDS-THM
                (EQUAL (EVA TERM A)
                       (EVA (COLLECT-ADDENDS-FN TERM) A))
                :RULE-CLASSES
                ((:META :TRIGGER-FNS (BINARY-+))))
        (LOCAL (IN-THEORY (DISABLE COLLECT-ADDENDS-THM))))

 (PROGN (DEFUN COLLECT-FACTORS-GATHER-EXPONENTS-FN (TERM)
               (IF (AND (NVARIABLEP TERM)
                        (NOT (FQUOTEP TERM))
                        (EQ (FFN-SYMB TERM) 'BINARY-*))
                   (LET ((PATTERN (MY-APPLY-1 'FACTOR-PATTERN-GATHER-EXPONENTS
                                              (ARG1 TERM))))
                        (MV-LET (FLAG NEW-TERM)
                                (NEW-TERM (ARG2 TERM)
                                          (ARG1 TERM)
                                          PATTERN 'FACTOR-PATTERN-GATHER-EXPONENTS
                                          'BINARY-*)
                                (IF FLAG NEW-TERM TERM)))
                   TERM))
        (DEFTHM COLLECT-FACTORS-GATHER-EXPONENTS-THM
                (EQUAL (EVA TERM A)
                       (EVA (COLLECT-FACTORS-GATHER-EXPONENTS-FN TERM)
                            A))
                :RULE-CLASSES
                ((:META :TRIGGER-FNS (BINARY-*))))
        (LOCAL (IN-THEORY (DISABLE COLLECT-FACTORS-GATHER-EXPONENTS-THM))))

 (PROGN (DEFUN COLLECT-FACTORS-SCATTER-EXPONENTS-FN (TERM)
               (IF (AND (NVARIABLEP TERM)
                        (NOT (FQUOTEP TERM))
                        (EQ (FFN-SYMB TERM) 'BINARY-*))
                   (LET ((PATTERN (MY-APPLY-1 'FACTOR-PATTERN-SCATTER-EXPONENTS
                                              (ARG1 TERM))))
                        (MV-LET (FLAG NEW-TERM)
                                (NEW-TERM (ARG2 TERM)
                                          (ARG1 TERM)
                                          PATTERN 'FACTOR-PATTERN-SCATTER-EXPONENTS
                                          'BINARY-*)
                                (IF FLAG NEW-TERM TERM)))
                   TERM))
        (DEFTHM COLLECT-FACTORS-SCATTER-EXPONENTS-THM
                (EQUAL (EVA TERM A)
                       (EVA (COLLECT-FACTORS-SCATTER-EXPONENTS-FN TERM)
                            A))
                :RULE-CLASSES
                ((:META :TRIGGER-FNS (BINARY-*))))
        (LOCAL (IN-THEORY (DISABLE COLLECT-FACTORS-SCATTER-EXPONENTS-THM))))
|#
