(in-package "ACL2")

; The below script normalizes Boolean formulas stated in terms of if
; expressions.

; Dr. Warren Hunt Jr. originally authored the script for his hardware
; verfication class in March of 2006, and David L. Rager modified it to use
; parallelism primitives during May of 2006.


; acl2

(defmacro bvl (variable new-value)
  (declare (xargs :guard t))
  `(mv-let
    (erp result state)
    (assign ,variable ,new-value)
    (declare (ignore result))
    (value (not erp))))

(defmacro bvl-file (variable file-name)
  `(er-let*
     ((my-list (read-list ,file-name 'top state)))
     (bvl ,variable my-list)))

(defmacro ! (x y)
  (declare (xargs :guard (symbolp x)))
  `(assign ,x ,y))

; A couple of math facts.

(defthm commutitivity2-of-+
  (equal (+ y x z)
         (+ x y z)))

(encapsulate
 ()

 (local
  (defthm commutativity-2-of-*-lemma
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (acl2-numberp z))
	     (equal (* (* x y) z)
		    (* (* y x) z)))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory (disable associativity-of-*)))))

 (defthm commutativity-2-of-*
   (equal (* x (* y z))
          (* y (* x z)))
   :hints
   (("Goal"
     :use commutativity-2-of-*-lemma))))


; A simple IF-expression recognizer and tautology checker.

; Recognize acceptable expressions -- the syntax.

(defun norm-if-exprp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (booleanp x)
    (and (consp (cdr x))
         (symbolp (car x))
         (not (booleanp (car x)))
         (norm-if-exprp (cadr x))
         (norm-if-exprp (cddr x)))))

(defun almost-norm-if-exprp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (booleanp x)
    (and (consp (cdr x))
         (symbolp (car x))
         (almost-norm-if-exprp (cadr x))
         (almost-norm-if-exprp (cddr x)))))

(defun boolean-exprp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (symbolp x)
    (and (consp (cdr x))
         (boolean-exprp (car x))
         (boolean-exprp (cadr x))
         (boolean-exprp (cddr x)))))

(defthm norm-if-exprp-is-boolean-exprp
  (implies (norm-if-exprp x)
           (boolean-exprp x)))


; Define suitable pairing of variables to their values.

(defun boolean-alistp (alst)
  (declare (xargs :guard t))
  (if (atom alst)
      (null alst)
    (and (consp (car alst))
         (symbolp (caar alst))
         (booleanp (cdar alst))
         (boolean-alistp (cdr alst)))))

(defun eval-norm-if-expr (x alst)
  (declare (xargs :guard (and (norm-if-exprp x)
                              (boolean-alistp alst))))
  (if (atom x)
      x
    (if (cdr (assoc (car x) alst))
        (eval-norm-if-expr (cadr x) alst)
      (eval-norm-if-expr (cddr x) alst))))


(defun if-depth (x)
  (declare (xargs :guard (boolean-exprp x)))
  (if (atom x)
      0
    (1+ (if-depth (car x)))))

(defun if-complexity (x)
  (declare (xargs :guard (boolean-exprp x)))
  (if (atom x)
      1
    (* (if-complexity (car x))
         (+ (if-complexity (cadr x))
            (if-complexity (cddr x))))))

(defun if-measure (x)
  (declare (xargs :guard (boolean-exprp x)))
  (make-ord (1+ (if-complexity x))
            1
            (if-depth x)))

(defun norm-ifs (x)
  ;; Normalize the IF expressions.
  (declare (xargs :guard (boolean-exprp x)
                  :measure (if-measure x)
                  :verify-guards t))
  (if (atom x)
      (if (booleanp x)
          x
        (list* x t nil))
    (let ((test  (car x))
          (left  (cadr x))
          (right (cddr x)))

      (if (and (atom left) (eq left right))
          (if (booleanp left) left (list* left t nil))

        (if (atom test)
            (if (booleanp test)
                (if test
                    (norm-ifs left)
                  (norm-ifs right))
              (let ((new-left  (norm-ifs left))
                     (new-right (norm-ifs right)))
                (if (and (atom new-left)
                         (eq new-left new-right))
                    (if (booleanp new-left)
                        new-left
                      (list* new-left t nil))
                  (list* test new-left new-right))))
          (norm-ifs (list* (car test)
                           (list* (cadr test) left right)
                           (list* (cddr test) left right))))))))

(defthm norm-if-exprp-norm-ifs
  (implies (boolean-exprp x)
           (norm-if-exprp (norm-ifs x))))

(defun norm-ifs-var (x t-vars f-vars)
  ;; Normalize the IF expressions.
  (declare (xargs :guard (and (boolean-exprp x)
                              (symbol-listp t-vars)
                              (symbol-listp f-vars))
                  :measure (if-measure x)
                  :verify-guards t))
  (if (atom x)
      (if (booleanp x)
          x
        (list* x t nil))
    (let ((test  (car x))
          (left  (cadr x))
          (right (cddr x)))

      (if (and (atom left) (eq left right))
          (if (booleanp left) left (list* left t nil))

        (if (atom test)
            (if (booleanp test)
                (if test
                    (norm-ifs-var left t-vars f-vars)
                  (norm-ifs-var right t-vars f-vars))

              (if (member test t-vars)
                  (norm-ifs-var left t-vars f-vars)

                (if (member test f-vars)
                    (norm-ifs-var right t-vars f-vars)

                  (let ((new-left  (norm-ifs-var left
                                                  (cons test t-vars) f-vars))
                         (new-right (norm-ifs-var right t-vars
                                                  (cons test f-vars))))
                    (if (and (atom new-left)
                             (eq new-left new-right))
                        (if (booleanp new-left)
                            new-left
                          (list* new-left t nil))
                      (list* test new-left new-right))))))

          (norm-ifs-var (list* (car test)
                           (list* (cadr test) left right)
                           (list* (cddr test) left right))
                    t-vars f-vars))))))

(defthm norm-if-var-exprp-norm-ifs
  (implies (boolean-exprp x)
           (norm-if-exprp (norm-ifs-var x t-vars f-vars))))

(defun tautology? (x tl fl)
  (declare (xargs :guard (and (norm-if-exprp x)
                              (symbol-listp tl)
                              (symbol-listp fl))))
  ;; Tautology? checks to see if input X is a tautology.
  (if (atom x)
      x
    (cond ((member (car x) tl)
           (tautology? (cadr x) tl fl))
          ((member (car x) fl)
           (tautology? (cddr x) tl fl))
          (t (and (tautology? (cadr x) (cons (car x) tl) fl)
                  (tautology? (cddr x) tl (cons (car x) fl)))))))

(defun taut? (x)
  (declare (xargs :guard t))
  (if (not (boolean-exprp x))
      'Bad-input-expression
    (tautology? (norm-ifs x) nil nil)))

; Gate abbreviations...

(defun b-not (x)
  (declare (xargs :guard t))
  (list* x nil t))

(defun b-or (x y)
  (declare (xargs :guard t))
  (list* x t (list* y t nil)))

(defun b-and (x y)
  (declare (xargs :guard t))
  (list* x (list* y t nil) nil))

(defun b-xor (x y)
  (declare (xargs :guard t))
  (list* x (list* y nil t) (list* y t nil)))

(defun b-eqv (x y)
  (declare (xargs :guard t))
  (list* x (list* y t nil) (list* y nil t)))

(defun b-if-gates (c a b)
  (declare (xargs :guard t))
  (b-or (b-and c a) (b-and (b-not c) b)))

(defun b-if (c a b)
  (declare (xargs :guard t))
  (list* c (list* a t nil) (list* b t nil)))

(defun b-xor3 (x y z)
  (declare (xargs :guard t))
  (b-xor x (b-xor y z)))

(defun b-maj (x y z)
  (declare (xargs :guard t))
  (b-if x (b-or y z) (b-and y z)))

(defun bv-adder (c a b)
  (declare (xargs :guard t))
  (if (or (atom a) (atom b))
      (list c)
    (cons (b-xor3 c (car a) (car b))
          (bv-adder (b-maj c (car a) (car b))
                    (cdr a)
                    (cdr b)))))

(defun two-bit-adder (c a b)
  (declare (xargs :guard (and (consp a) (consp (cdr a))
                              (consp b) (consp (cdr b)))))
  (let ((a0 (car a))
        (a1 (cadr a))
        (b0 (car b))
        (b1 (cadr b)))
    (list (b-xor3 c a0 b0)
          (b-xor3 (b-maj a0 b0 c) a1 b1)
          (b-maj (b-maj a0 b0 c) a1 b1))))

(defun one-bit-adder (c a b)
  (declare (xargs :guard (and (consp a)
                              (consp b))))
  (let ((a0 (car a))
        (b0 (car b)))
    (list (b-xor3 c a0 b0)
          (b-maj a0 b0 c))))


(defun three-bit-adder (c a b)
  (declare (xargs :guard (and (true-listp a)
                              (equal (length a) 3)
                              (true-listp b)
                              (equal (length b) 3))))
  (let* ((a0 (nth 0 a))
         (a1 (nth 1 a))
         (a2 (nth 2 a))
         (b0 (nth 0 b))
         (b1 (nth 1 b))
         (b2 (nth 2 b))
         (c0 (b-maj a0 b0 c))
         (s0 (b-xor3 a0 b0 c))
         (c1 (b-maj a1 b1 c0))
         (s1 (b-xor3 a1 b1 c0))
         (c2 (b-maj a2 b2 c1))
         (s2 (b-xor3 a2 b2 c1)))
    (list s0
          s1
          s2
          c2)))




(defun four-bit-adder (c a b)
  (declare (xargs :guard (and (true-listp a)
                              (equal (length a) 4)
                              (true-listp b)
                              (equal (length b) 4))))
  (let* ((a0 (nth 0 a))
         (a1 (nth 1 a))
         (a2 (nth 2 a))
         (a3 (nth 3 a))
         (b0 (nth 0 b))
         (b1 (nth 1 b))
         (b2 (nth 2 b))
         (b3 (nth 3 b))
         (c0 (b-maj a0 b0 c))
         (s0 (b-xor3 a0 b0 c))
         (c1 (b-maj a1 b1 c0))
         (s1 (b-xor3 a1 b1 c0))
         (c2 (b-maj a2 b2 c1))
         (s2 (b-xor3 a2 b2 c1))
         (c3 (b-maj a3 b3 c2))
         (s3 (b-xor3 a3 b3 c2)))
    (list s0
          s1
          s2
          s3
          c3)))










(defun 8-bit-ripple-carry-adder (c a b)
  (declare (xargs :guard (and (true-listp a)
                              (equal (length a) 8)
                              (true-listp b)
                              (equal (length b) 8))))
  (let* ((a0 (nth 0 a))
         (a1 (nth 1 a))
         (a2 (nth 2 a))
         (a3 (nth 3 a))
         (a4 (nth 4 a))
         (a5 (nth 5 a))
         (a6 (nth 6 a))
         (a7 (nth 7 a))

         (b0 (nth 0 b))
         (b1 (nth 1 b))
         (b2 (nth 2 b))
         (b3 (nth 3 b))
         (b4 (nth 4 b))
         (b5 (nth 5 b))
         (b6 (nth 6 b))
         (b7 (nth 7 b))

         (c0 (b-maj a0 b0 c))
         (s0 (b-xor3 a0 b0 c))
         (c1 (b-maj a1 b1 c0))
         (s1 (b-xor3 a1 b1 c0))
         (c2 (b-maj a2 b2 c1))
         (s2 (b-xor3 a2 b2 c1))
         (c3 (b-maj a3 b3 c2))
         (s3 (b-xor3 a3 b3 c2))

         (c4 (b-maj a4 b4 c3))
         (s4 (b-xor3 a4 b4 c3))

         (c5 (b-maj a5 b5 c4))
         (s5 (b-xor3 a5 b5 c4))

         (c6 (b-maj a6 b6 c5))
         (s6 (b-xor3 a6 b6 c5))

         (c7 (b-maj a7 b7 c6))
         (s7 (b-xor3 a7 b7 c6)))


    (list s0
          s1
          s2
          s3
          s4
          s5
          s6
          s7
          c7)))


(defun 10-bit-ripple-carry-adder (c a b)
  (declare (xargs :guard (and (true-listp a)
                              (equal (length a) 10)
                              (true-listp b)
                              (equal (length b) 10))))
  (let* ((a0 (nth 0 a))
         (a1 (nth 1 a))
         (a2 (nth 2 a))
         (a3 (nth 3 a))
         (a4 (nth 4 a))
         (a5 (nth 5 a))
         (a6 (nth 6 a))
         (a7 (nth 7 a))
         (a8 (nth 8 a))
         (a9 (nth 9 a))

         (b0 (nth 0 b))
         (b1 (nth 1 b))
         (b2 (nth 2 b))
         (b3 (nth 3 b))
         (b4 (nth 4 b))
         (b5 (nth 5 b))
         (b6 (nth 6 b))
         (b7 (nth 7 b))
         (b8 (nth 8 b))
         (b9 (nth 9 b))

         (c0 (b-maj a0 b0 c))
         (s0 (b-xor3 a0 b0 c))
         (c1 (b-maj a1 b1 c0))
         (s1 (b-xor3 a1 b1 c0))
         (c2 (b-maj a2 b2 c1))
         (s2 (b-xor3 a2 b2 c1))
         (c3 (b-maj a3 b3 c2))
         (s3 (b-xor3 a3 b3 c2))

         (c4 (b-maj a4 b4 c3))
         (s4 (b-xor3 a4 b4 c3))

         (c5 (b-maj a5 b5 c4))
         (s5 (b-xor3 a5 b5 c4))

         (c6 (b-maj a6 b6 c5))
         (s6 (b-xor3 a6 b6 c5))

         (c7 (b-maj a7 b7 c6))
         (s7 (b-xor3 a7 b7 c6))

         (c8 (b-maj a8 b8 c7))
         (s8 (b-xor3 a8 b8 c7))

         (c9 (b-maj a9 b9 c8))
         (s9 (b-xor3 a9 b9 c8)))

    (list s0
          s1
          s2
          s3
          s4
          s5
          s6
          s7
          s8
          s9
          c9)))


(defun 12-bit-ripple-carry-adder (c a b)
  (declare (xargs :guard (and (true-listp a)
                              (equal (length a) 12)
                              (true-listp b)
                              (equal (length b) 12))))
  (let* ((a0 (nth 0 a))
         (a1 (nth 1 a))
         (a2 (nth 2 a))
         (a3 (nth 3 a))
         (a4 (nth 4 a))
         (a5 (nth 5 a))
         (a6 (nth 6 a))
         (a7 (nth 7 a))
         (a8 (nth 8 a))
         (a9 (nth 9 a))
         (a10 (nth 10 a))
         (a11 (nth 11 a))

         (b0 (nth 0 b))
         (b1 (nth 1 b))
         (b2 (nth 2 b))
         (b3 (nth 3 b))
         (b4 (nth 4 b))
         (b5 (nth 5 b))
         (b6 (nth 6 b))
         (b7 (nth 7 b))
         (b8 (nth 8 b))
         (b9 (nth 9 b))
         (b10 (nth 10 b))
         (b11 (nth 11 b))


         (c0 (b-maj a0 b0 c))
         (s0 (b-xor3 a0 b0 c))
         (c1 (b-maj a1 b1 c0))
         (s1 (b-xor3 a1 b1 c0))
         (c2 (b-maj a2 b2 c1))
         (s2 (b-xor3 a2 b2 c1))
         (c3 (b-maj a3 b3 c2))
         (s3 (b-xor3 a3 b3 c2))

         (c4 (b-maj a4 b4 c3))
         (s4 (b-xor3 a4 b4 c3))

         (c5 (b-maj a5 b5 c4))
         (s5 (b-xor3 a5 b5 c4))

         (c6 (b-maj a6 b6 c5))
         (s6 (b-xor3 a6 b6 c5))

         (c7 (b-maj a7 b7 c6))
         (s7 (b-xor3 a7 b7 c6))

         (c8 (b-maj a8 b8 c7))
         (s8 (b-xor3 a8 b8 c7))

         (c9 (b-maj a9 b9 c8))
         (s9 (b-xor3 a9 b9 c8))

         (c10 (b-maj a10 b10 c9))
         (s10 (b-xor3 a10 b10 c9))

         (c11 (b-maj a11 b11 c10))
         (s11 (b-xor3 a11 b11 c10)))

    (list s0
          s1
          s2
          s3
          s4
          s5
          s6
          s7
          s8
          s9
          s10
          s11
          c11)))





(defun 16-bit-ripple-carry-adder (c a b)
  (declare (xargs :guard (and (true-listp a)
                              (equal (length a) 16)
                              (true-listp b)
                              (equal (length b) 16))))
  (let* ((a0 (nth 0 a))
         (a1 (nth 1 a))
         (a2 (nth 2 a))
         (a3 (nth 3 a))
         (a4 (nth 4 a))
         (a5 (nth 5 a))
         (a6 (nth 6 a))
         (a7 (nth 7 a))
         (a8 (nth 8 a))
         (a9 (nth 9 a))
         (a10 (nth 10 a))
         (a11 (nth 11 a))
         (a12 (nth 12 a))
         (a13 (nth 13 a))
         (a14 (nth 14 a))
         (a15 (nth 15 a))

         (b0 (nth 0 b))
         (b1 (nth 1 b))
         (b2 (nth 2 b))
         (b3 (nth 3 b))
         (b4 (nth 4 b))
         (b5 (nth 5 b))
         (b6 (nth 6 b))
         (b7 (nth 7 b))
         (b8 (nth 8 b))
         (b9 (nth 9 b))
         (b10 (nth 10 b))
         (b11 (nth 11 b))
         (b12 (nth 12 b))
         (b13 (nth 13 b))
         (b14 (nth 14 b))
         (b15 (nth 15 b))


         (c0 (b-maj a0 b0 c))
         (s0 (b-xor3 a0 b0 c))
         (c1 (b-maj a1 b1 c0))
         (s1 (b-xor3 a1 b1 c0))
         (c2 (b-maj a2 b2 c1))
         (s2 (b-xor3 a2 b2 c1))
         (c3 (b-maj a3 b3 c2))
         (s3 (b-xor3 a3 b3 c2))

         (c4 (b-maj a4 b4 c3))
         (s4 (b-xor3 a4 b4 c3))

         (c5 (b-maj a5 b5 c4))
         (s5 (b-xor3 a5 b5 c4))

         (c6 (b-maj a6 b6 c5))
         (s6 (b-xor3 a6 b6 c5))

         (c7 (b-maj a7 b7 c6))
         (s7 (b-xor3 a7 b7 c6))

         (c8 (b-maj a8 b8 c7))
         (s8 (b-xor3 a8 b8 c7))

         (c9 (b-maj a9 b9 c8))
         (s9 (b-xor3 a9 b9 c8))

         (c10 (b-maj a10 b10 c9))
         (s10 (b-xor3 a10 b10 c9))

         (c11 (b-maj a11 b11 c10))
         (s11 (b-xor3 a11 b11 c10))

         (c12 (b-maj a12 b12 c11))
         (s12 (b-xor3 a12 b12 c11))

         (c13 (b-maj a13 b13 c12))
         (s13 (b-xor3 a13 b13 c12))

         (c14 (b-maj a14 b14 c13))
         (s14 (b-xor3 a14 b14 c13))


         (c15 (b-maj a15 b15 c14))
         (s15 (b-xor3 a15 b15 c14)))

    (list s0
          s1
          s2
          s3
          s4
          s5
          s6
          s7
          s8
          s9
          s10
          s11
          s12
          s13
          s14
          s15
          c15)))



(defun b-eqv-list (x y)
  (declare (xargs :guard t))
  (if (or (atom x) (atom y))
      (and (atom x) (atom y))
    (b-and (b-eqv (car x) (car y))
           (b-eqv-list (cdr x) (cdr y)))))






(defun pnorm-ifs (x depth)
  ;; Normalize the IF expressions.
  (declare (xargs :guard (and (boolean-exprp x) (natp depth))
                  :measure (if-measure x)
                  :verify-guards t))
  (if (atom x)
      (if (booleanp x)
          x
        (list* x t nil))
    (let ((test  (car x))
          (left  (cadr x))
          (right (cddr x)))

      (if (and (atom left) (eq left right))
          (if (booleanp left) left (list* left t nil))

        (if (atom test)
           (if (booleanp test)
                (if test
                    (pnorm-ifs left (1+ depth))
                  (pnorm-ifs right (1+ depth)))
              (plet (declare (granularity (< depth 10)))
                    ((new-left  (pnorm-ifs left (1+ depth)))
                     (new-right (pnorm-ifs right (1+ depth))))
                    (if (and (atom new-left)
                             (eq new-left new-right))
                        (if (booleanp new-left)
                            new-left
                          (list* new-left t nil))
                      (list* test new-left new-right))))
          (pnorm-ifs (list* (car test)
                            (list* (cadr test) left right)
                            (list* (cddr test) left right))
                     depth))))))



(defun nthcar (x n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (if (atom x)
        nil
      (nthcar (car x) (1- n)))))

(defun pnorm-ifs-var (x t-vars f-vars)
  ;; Normalize the IF expressions.
  (declare (xargs :guard (and (boolean-exprp x)
                              (symbol-listp t-vars)
                              (symbol-listp f-vars))
                  :measure (if-measure x)
                  :verify-guards t))
  (if (atom x)
      (if (booleanp x)
          x
        (list* x t nil))
    (let ((test  (car x))
          (left  (cadr x))
          (right (cddr x)))

      (if (and (atom left) (eq left right))
          (if (booleanp left) left (list* left t nil))

        (if (atom test)
            (if (booleanp test)
                (if test
                    (pnorm-ifs-var left t-vars f-vars)
                  (pnorm-ifs-var right t-vars f-vars))

              (if (member test t-vars)
                  (pnorm-ifs-var left t-vars f-vars)

                (if (member test f-vars)
                    (pnorm-ifs-var right t-vars f-vars)

                  (plet (declare (granularity (and (nthcar left 3)
                                                        (nthcar right 3))))
                        ((new-left  (pnorm-ifs-var left
                                                   (cons test t-vars)
                                                   f-vars))
                         (new-right (pnorm-ifs-var right
                                                   t-vars
                                                   (cons test f-vars))))
                        (if (and (atom new-left)
                                 (eq new-left new-right))
                            (if (booleanp new-left)
                                new-left
                              (list* new-left t nil))
                          (list* test new-left new-right))))))

          (pnorm-ifs-var (list* (car test)
                                (list* (cadr test) left right)
                                (list* (cddr test) left right))
                         t-vars f-vars))))))


(defmacro test2 ()
  '(time$ (bvl two-bit-adder-ok
            (pnorm-ifs (b-eqv-list (two-bit-adder 'c '(a0 a1) '(b0 b1))
                                   (bv-adder      'c '(a0 a1) '(b0 b1)))
                       0))))



(defmacro test-2bit ()
  '(time$ (bvl two-bit-adder-ok
               (norm-ifs-var (b-eqv-list (two-bit-adder 'c '(a0 a1) '(b0 b1))
                                          (bv-adder      'c '(a0 a1) '(b0
                                                                       b1)))
                              nil
                              nil))))


(defmacro ptest-2bit ()
  '(time$ (bvl two-bit-adder-ok
               (pnorm-ifs-var (b-eqv-list (two-bit-adder 'c '(a0 a1) '(b0 b1))
                                          (bv-adder      'c '(a0 a1) '(b0
                                                                       b1)))
                              nil
                              nil
                              0))))


(defmacro test-3bit ()
  '(time$ (bvl three-bit-adder-ok
            (norm-ifs-var (b-eqv-list (three-bit-adder 'c '(a0 a1 a2) '(b0 b1 b2))
                                       (bv-adder      'c '(a0 a1 a2) '(b0 b1
                                                                          b2)))
                           nil
                           nil))))


(defmacro ptest-3bit ()
  '(time$ (bvl three-bit-adder-ok
               (pnorm-ifs-var (b-eqv-list (three-bit-adder 'c '(a0 a1 a2) '(b0 b1 b2))
                                          (bv-adder      'c '(a0 a1 a2) '(b0 b1
                                                                             b2)))
                              nil
                              nil
                              0))))



(defmacro test-4bit ()
  '(time$ (bvl four-bit-adder-ok
               (norm-ifs-var (b-eqv-list (four-bit-adder 'c
                                                         '(a0 a1 a2 a3)
                                                         '(b0 b1 b2 b3))

                                         (bv-adder      'c
                                                        '(a0 a1 a2 a3)
                                                        '(b0 b1 b2 a4)))
                             nil
                             nil))))

(defmacro ptest-4bit ()
  '(time$ (bvl four-bit-adder-ok
               (pnorm-ifs-var (b-eqv-list (four-bit-adder 'c
                                                         '(a0 a1 a2 a3)
                                                         '(b0 b1 b2 b3))

                                         (bv-adder      'c
                                                        '(a0 a1 a2 a3)
                                                        '(b0 b1 b2 a4)))
                             nil
                             nil
                             ))))



(defmacro test-8bit ()
  '(time$ (bvl eight-bit-adder-ok
               (norm-ifs-var (b-eqv-list
                              (8-bit-ripple-carry-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7)
                               '(b0 b1 b2 b3 b4 b5 b6 b7))

                              (bv-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7)
                               '(b0 b1 b2 b3 b4 b5 b6 b7)))

                             nil
                             nil))))


(defmacro ptest-8bit ()
  '(time$ (bvl eight-bit-adder-ok
               (pnorm-ifs-var (b-eqv-list
                              (8-bit-ripple-carry-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7)
                               '(b0 b1 b2 b3 b4 b5 b6 b7))

                              (bv-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7)
                               '(b0 b1 b2 b3 b4 b5 b6 b7)))

                             nil
                             nil
                             ))))





(defmacro test-10bit ()
  '(time$ (bvl ten-bit-adder-ok
               (norm-ifs-var (b-eqv-list
                              (10-bit-ripple-carry-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9))

                              (bv-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)))

                             nil
                             nil))))


(defmacro ptest-10bit ()
  '(time$ (bvl ten-bit-adder-ok
               (pnorm-ifs-var (b-eqv-list
                              (10-bit-ripple-carry-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9))

                              (bv-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)))

                             nil
                             nil
                             ))))

(defmacro test-12bit ()
  '(time$ (bvl twelve-bit-adder-ok
               (norm-ifs-var (b-eqv-list
                              (12-bit-ripple-carry-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11))

                              (bv-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11)))

                             nil
                             nil))))


(defmacro ptest-12bit ()
  '(time$ (bvl twelve-bit-adder-ok
               (pnorm-ifs-var (b-eqv-list
                              (12-bit-ripple-carry-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11))

                              (bv-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11)))

                             nil
                             nil))))


(defmacro test-16bit ()
  '(time$ (bvl sixteen-bit-adder-ok
               (norm-ifs-var (b-eqv-list
                              (16-bit-ripple-carry-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                                    a14 a15)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
                                    b14 b15))

                              (bv-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                                    a14 a15)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
                                    b14 b15)))

                             nil
                             nil))))



(defmacro ptest-16bit ()
  '(time$ (bvl sixteen-bit-adder-ok
               (pnorm-ifs-var (b-eqv-list
                              (16-bit-ripple-carry-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                                    a14 a15)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
                                    b14 b15))

                              (bv-adder
                               'c
                               '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                                    a14 a15)
                               '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
                                    b14 b15)))

                             nil
                             nil
                             0))))


#|

; Results

; Make sure to compile before running these forms

ACL2 !>
(test-10bit)
(test-10bit)
(test-10bit)
(ptest-10bit)
(ptest-10bit)
(ptest-10bit)

(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 71,376 milliseconds (71.376 seconds) to run.
Of that, 42,314 milliseconds (42.314 seconds) were spent in user mode
         12,390 milliseconds (12.390 seconds) were spent in system mode
         16,672 milliseconds (16.672 seconds) were spent executing other OS processes.
9,687 milliseconds (9.687 seconds) was spent in GC.
 10,845,832,160 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 71,221 milliseconds (71.221 seconds) to run.
Of that, 42,180 milliseconds (42.180 seconds) were spent in user mode
         12,360 milliseconds (12.360 seconds) were spent in system mode
         16,681 milliseconds (16.681 seconds) were spent executing other OS processes.
9,661 milliseconds (9.661 seconds) was spent in GC.
 10,845,832,088 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 71,244 milliseconds (71.244 seconds) to run.
Of that, 42,215 milliseconds (42.215 seconds) were spent in user mode
         12,362 milliseconds (12.362 seconds) were spent in system mode
         16,667 milliseconds (16.667 seconds) were spent executing other OS processes.
9,692 milliseconds (9.692 seconds) was spent in GC.
 10,845,832,088 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 62,601 milliseconds (62.601 seconds) to run.
Of that, 77,089 milliseconds (77.089 seconds) were spent in user mode
         56,385 milliseconds (56.385 seconds) were spent in system mode
28,936 milliseconds (28.936 seconds) was spent in GC.
 9,600 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 67,819 milliseconds (67.819 seconds) to run.
Of that, 81,599 milliseconds (81.599 seconds) were spent in user mode
         59,974 milliseconds (59.974 seconds) were spent in system mode
32,935 milliseconds (32.935 seconds) was spent in GC.
 6,528 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 67,097 milliseconds (67.097 seconds) to run.
Of that, 80,824 milliseconds (80.824 seconds) were spent in user mode
         63,183 milliseconds (63.183 seconds) were spent in system mode
31,042 milliseconds (31.042 seconds) was spent in GC.
 6,528 bytes of memory allocated.
 T
ACL2 !>


(test-12bit)
(test-12bit)
(test-12bit)
(ptest-12bit)
(ptest-12bit)
(ptest-12bit)





ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 1,403,485 milliseconds (1403.485 seconds) to run.
Of that, -353,442 milliseconds (-353.442 seconds) were spent in user mode
         -374,703 milliseconds (-374.703 seconds) were spent in system mode
         2,131,630 milliseconds (2131.630 seconds) were spent executing other OS processes.
235,564 milliseconds (235.564 seconds) was spent in GC.
 199,881,181,080 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 1,326,100 milliseconds (1326.100 seconds) to run.
Of that, 791,234 milliseconds (791.234 seconds) were spent in user mode
         227,454 milliseconds (227.454 seconds) were spent in system mode
         307,412 milliseconds (307.412 seconds) were spent executing other OS processes.
166,676 milliseconds (166.676 seconds) was spent in GC.
 199,881,181,080 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 1,327,331 milliseconds (1327.331 seconds) to run.
Of that, 792,392 milliseconds (792.392 seconds) were spent in user mode
         227,594 milliseconds (227.594 seconds) were spent in system mode
         307,345 milliseconds (307.345 seconds) were spent executing other OS processes.
169,447 milliseconds (169.447 seconds) was spent in GC.
 199,881,181,080 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 976,441 milliseconds (976.441 seconds) to run.
Of that, 1,069,622 milliseconds (1069.622 seconds) were spent in user mode
         787,418 milliseconds (787.418 seconds) were spent in system mode
459,338 milliseconds (459.338 seconds) was spent in GC.
 10,624 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 1,089,697 milliseconds (1089.697 seconds) to run.
Of that, 1,117,539 milliseconds (1117.539 seconds) were spent in user mode
         918,418 milliseconds (918.418 seconds) were spent in system mode
509,356 milliseconds (509.356 seconds) was spent in GC.
 7,552 bytes of memory allocated.
 T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 980,032 milliseconds (980.032 seconds) to run.
Of that, -1,207,063 milliseconds (-1207.063 seconds) were spent in user mode
         -384,060 milliseconds (-384.060 seconds) were spent in system mode
         2,571,155 milliseconds (2571.155 seconds) were spent executing other OS processes.
457,002 milliseconds (457.002 seconds) was spent in GC.
 7,552 bytes of memory allocated.
 T
ACL2 !>

|#