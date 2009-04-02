(in-package "ACL2")

(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)

(defund bv-add (x y)
  (mod (+ (nfix x) (nfix y)) 32))

(defun make-bv-add (sym-list)
  (cond
   ((atom sym-list)
    nil)
   ((atom (cdr sym-list))
    (car sym-list))
   (t
    `(bv-add ,(car sym-list)
             ,(make-bv-add (cdr sym-list))))))

(defun concat-str-macro (lst)
  (if (consp lst)
      (if (consp (cdr lst))
	  (cons 'concatenate 
		(cons ''string (cons (car lst) 
				     (cons (concat-str-macro (cdr lst))
					   'nil))))
	(car lst))
    nil))

(defmacro concat-str (&rest args)
  (concat-str-macro args))

(defun symbol-from-str-num (str n)
  (intern (concat-str str (coerce (explode-atom n 10) 'string))
          "ACL2"))

(defun make-sym-list (n)
  (cond
   ((zp n)
    nil)
   (t
    (cons (symbol-from-str-num "X" (1- n))
          (make-sym-list (1- n))))))

(defun f-macro-problem-fn (n)
  (let ((sym-list (make-sym-list n)))
    `(equal (f ,(make-bv-add sym-list))
            (f ,(make-bv-add (revappend sym-list nil))))))

(defmacro f-macro-problem (n)
  (f-macro-problem-fn n))

(defstub f (x) t)

(defun macro-problem-fn (n)
  (let ((sym-list (make-sym-list n)))
    `(equal (f ,(make-bv-add sym-list))
            (f ,(make-bv-add (revappend sym-list nil))))))

(defmacro macro-problem (n)
  (macro-problem-fn n))

; Timings shown below are with output inhibited.  To inhibit some output
; interactively:
; (set-inhibit-output-lst '(prove proof-tree))
; Times were obtained on a 2.6 GHz Pentium\textregistered 4 processor with
; 2.0 gigabytes of random access memory, running Allegro Common Lisp 7.0.

(set-rewrite-stack-limit nil)

(comp t)

;;; Tests using ordinary rewriting

(encapsulate ()

(local (include-book "bv-add-common"))

(comp t)

(defthm example-problem-4
  (equal (f (bv-add x0 (bv-add x1 (bv-add x2 x3))))
         (f (bv-add x3 (bv-add x2 (bv-add x1 x0)))))
  :rule-classes nil)

(defthm example-problem-5-f
  (f-macro-problem 5)
  :rule-classes nil)

(defthm example-problem-5
  (macro-problem 5)
  :rule-classes nil)

(defthm example-problem-100-f
  (f-macro-problem 100)
  :rule-classes nil)

(defthm example-problem-100
  (macro-problem 100)
  :rule-classes nil)

(defthm example-problem-500-f
  (f-macro-problem 500)
  :rule-classes nil)

;Time:  11.26 seconds (prove: 11.24, print: 0.00, other: 0.02)
(defthm example-problem-500
  (macro-problem 500)
  :rule-classes nil)

; One big problem is enough, so we comment this out:
; (defthm f-example-problem-1000
;   (f-macro-problem 1000)
;   :rule-classes nil)

;Time:  64.43 seconds (prove: 64.41, print: 0.00, other: 0.02)
; But on Allegro CL 7.0, on a 2.4GHz P4:
;Time:  176.20 seconds (prove: 173.57, print: 0.00, other: 2.63)
; So, we comment the following out too; it doesn't add much to our testing.
; (defthm example-problem-1000
;   (macro-problem 1000)
;   :rule-classes nil)

)

; Next, without f:

; Tests using clause-processor rule

(encapsulate ()

(local (include-book "bv-add"))

(comp t)

(defthm cl-proc-example-problem-4
  (equal (f (bv-add x0 (bv-add x1 (bv-add x2 x3))))
         (f (bv-add x3 (bv-add x2 (bv-add x1 x0)))))
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

(defthm cl-proc-example-problem-5-f
  (f-macro-problem 5)
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

(defthm cl-proc-example-problem-5
  (macro-problem 5)
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

(defthm cl-proc-example-problem-100-f
  (f-macro-problem 100)
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

(defthm cl-proc-example-problem-100
  (macro-problem 100)
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

(defthm cl-proc-example-problem-500-f
  (f-macro-problem 500)
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

;Time:  0.02 seconds (prove: 0.01, print: 0.00, other: 0.01)
(defthm cl-proc-example-problem-500
  (macro-problem 500)
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

(defthm cl-proc-example-problem-1000-f
  (f-macro-problem 1000)
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

;Time:  0.05 seconds (prove: 0.02, print: 0.00, other: 0.03)
(defthm cl-proc-example-problem-1000
  (macro-problem 1000)
  :hints (("Goal"
           :clause-processor (:function bv-add-sort-cp)))
  :rule-classes nil)

)
