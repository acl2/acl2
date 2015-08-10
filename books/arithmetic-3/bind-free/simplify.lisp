; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; simplify.lisp
;;;
;;;
;;; This book contains two types of rules:
;;; 1. Cancel "like" terms on either side of an equality or inequality.
;;; 2. Move "negative" terms form one side of an equality or inequality
;;; to the other.
;;;
;;; For cancelling like factors there are two distinct behaviours.
;;; Under the theory scatter-exponents (the default) exponents
;;; consisting of sums are broken apart or scattered, e.g.,
;;; (expt x (+ m n)) ===> (* (expt x m) (expt x n)).
;;; Under the other theory, gather-exponents, the reverse is true,
;;; e.g., (* (expt x m) (expt x n)) ===> (expt x (+ m n)).
;;; These two theories are defined in top, using rules from this
;;; book and elsewhere.
;;;
;;; A simple example of cancelling like terms:
;;; (equal (+ a (* 2 c) d)
;;;        (+ b c d))
;;; ===>
;;; (equal (+ a c)
;;;        b)
;;;
;;; A simple oxample of moving a negative term to the other side:
;;; (< (+ a (- b) c)
;;;    (+ d e))
;;; ===>
;;; (< (+ a c)
;;;    (+ b d e))
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "simplify-helper"))

(local
 (include-book "basic"))

(include-book "common")

(table acl2-defaults-table :state-ok t)

(local
 (defthm rewrite-equal-<-to-iff-<
     (equal (equal (< a b)
                   (< c d))
            (iff (< a b)
                 (< c d)))))

(local
 (encapsulate
  ()

  (local (include-book "../pass1/top"))

  (defthm equal-*-/-1
      (equal (equal (* (/ x) y) z)
             (if (equal (fix x) 0)
                 (equal z 0)
               (and (acl2-numberp z)
                    (equal (fix y) (* x z))))))

  (defthm equal-*-/-2
      (equal (equal (* y (/ x)) z)
             (if (equal (fix x) 0)
                 (equal z 0)
               (and (acl2-numberp z)
                    (equal (fix y) (* z x))))))

  ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun insert-0 (x y)
  (declare (xargs :guard t))
  (declare (ignore x))
  y)

(defthm insert-0-x-y
    (equal (insert-0 x y)
           y))

(defthm insert-0-x-x
    (implies (equal x 0)
             (equal (insert-0 x x)
                    0)))

(defthm insert-0-+
    (equal (insert-0 x (+ y z))
           (+ (insert-0 x y) (insert-0 x z))))

(defthm insert-0-*
    (equal (insert-0 x (* y z))
           (* (insert-0 x y) (insert-0 x z))))

(in-theory (disable insert-0))

(theory-invariant (not (active-runep '(:definition insert-0)))
                  :error nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun addend-val (addend)
  (declare (xargs :guard (pseudo-termp addend)))
  (cond ((variablep addend)
	 1)
	((fquotep addend)
	 1)
	((eq (ffn-symb addend) 'UNARY--)
	 (addend-val (arg1 addend)))
	((and (eq (ffn-symb addend) 'BINARY-*)
	      (rational-constant-p (arg1 addend)))
	 (unquote (arg1 addend)))
	(t
	 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Deal with constants, and (expt x 2) with x.

(defun factors (product)
  (declare (xargs :guard (pseudo-termp product)))
  (if (eq (fn-symb product) 'BINARY-*)
      (cons (fargn product 1)
            (factors (fargn product 2)))
    (list product)))

(defun make-product (factors)
  (declare (xargs :guard (true-listp factors)))
  (cond ((null factors)
         ''1)
        ((null (cdr factors))
         (car factors))
        ((null (cddr factors))
         (list 'BINARY-* (car factors) (cadr factors)))
        (t
         (list 'BINARY-* (car factors) (make-product (cdr factors))))))

(defun remainder-bbb (common-factors sum)
  (declare (xargs :guard (and (true-listp common-factors)
                              (pseudo-termp sum))))
  (if (eq (fn-symb sum) 'BINARY-+)
      (let ((first (make-product (set-difference-equal (factors (fargn sum 1))
                                                       common-factors))))
        (list 'BINARY-+ first (remainder-bbb common-factors (fargn sum 2))))
    (make-product (set-difference-equal (factors sum)
                                        common-factors))))

; Intersection-equal was added to ACL2 in Version 4.0.

(defun common-factors-aaa (factors sum)
  (declare (xargs :measure (acl2-count sum)
                  :guard (and (true-listp factors)
                              (pseudo-termp sum))))
  (cond ((null factors)
         nil)
        ((eq (fn-symb sum) 'BINARY-+)
         (common-factors-aaa (intersection-equal factors (factors (fargn sum 1)))
                         (fargn sum 2)))
        (t
         (intersection-equal factors (factors sum)))))

(defun simplify-terms-such-as-a+ab-rel-0-fn (sum)
  (declare (xargs :guard (pseudo-termp sum)))
  (if (eq (fn-symb sum) 'BINARY-+)
      (let ((common-factors (common-factors-aaa (factors (fargn sum 1))
                                            (fargn sum 2))))
        (if common-factors
            (let ((common (make-product common-factors))
                  (remainder (remainder-bbb common-factors sum)))
              (list (cons 'common common)
                    (cons 'remainder remainder)))
          nil))
    nil))

(defthm simplify-terms-such-as-a+ab-=-0
    (implies (and (bind-free
                   (simplify-terms-such-as-a+ab-rel-0-fn sum)
                   (common remainder))
                  (acl2-numberp common)
                  (acl2-numberp remainder)
                  (equal sum
                         (* common remainder)))
             (equal (equal sum 0)
                    (or (equal common 0)
                        (equal remainder 0)))))

(defthm simplify-terms-such-as-a+ab-<-0
    (implies (and (bind-free
                   (simplify-terms-such-as-a+ab-rel-0-fn sum)
                   (common remainder))
                  (rationalp common)
                  (rationalp remainder)
                  (equal sum
                         (* common remainder)))
             (equal (< sum 0)
                    (cond ((< common 0)
                           (< 0 remainder))
                          ((< 0 common)
                           (< remainder 0))
                          (t
                           nil)))))

(defthm simplify-terms-such-as-0-<-a+ab
    (implies (and (bind-free
                   (simplify-terms-such-as-a+ab-rel-0-fn sum)
                   (common remainder))
                  (rationalp common)
                  (rationalp remainder)
                  (equal sum
                         (* common remainder)))
             (equal (< 0 sum)
                    (cond ((< 0 common)
                           (< 0 remainder))
                          ((< common 0)
                           (< remainder 0))
                          (t
                           nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-val-gather-exponents1 (exponent)
  (declare (xargs :guard (pseudo-termp exponent)))
  (cond ((variablep exponent)
         1)
        ((rational-constant-p exponent)
         (unquote exponent))
        ((eq (ffn-symb exponent) 'BINARY-*)
         (if (rational-constant-p (arg1 exponent))
             (unquote (arg1 exponent))
           1))
        ((eq (ffn-symb exponent) 'BINARY-+)
         (+ (factor-val-gather-exponents1 (arg1 exponent))
            (factor-val-gather-exponents1 (arg2 exponent))))
        (t
         1)))

(defun factor-val-gather-exponents (factor)
  (declare (xargs :guard (pseudo-termp factor)))
  (cond ((variablep factor)
	 1)
	((fquotep factor)
	 1)
	((eq (ffn-symb factor) 'UNARY-/)
	 (factor-val-gather-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'UNARY--)
	 (factor-val-gather-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'EXPT)
         (factor-val-gather-exponents1 (arg2 factor)))
	(t
	 1)))

(defun factor-val-scatter-exponents1 (exponent)
  (declare (xargs :guard (pseudo-termp exponent)))
  (cond ((variablep exponent)
         1)
        ((rational-constant-p exponent)
         (unquote exponent))
        ((eq (ffn-symb exponent) 'BINARY-*)
         (if (rational-constant-p (arg1 exponent))
             (unquote (arg1 exponent))
           1))
        ((eq (ffn-symb exponent) 'BINARY-+)
         (+ (factor-val-scatter-exponents1 (arg1 exponent))
            (factor-val-scatter-exponents1 (arg2 exponent))))
        (t
         1)))

(defun factor-val-scatter-exponents (factor)
  (declare (xargs :guard (pseudo-termp factor)))
  (cond ((variablep factor)
	 1)
	((fquotep factor)
	 1)
	((eq (ffn-symb factor) 'UNARY-/)
	 (factor-val-scatter-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'UNARY--)
	 (factor-val-scatter-exponents (arg1 factor)))
	((eq (ffn-symb factor) 'EXPT)
         (factor-val-scatter-exponents1 (arg2 factor)))
	(t
	 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun addend-info-entry (x)
  (declare (xargs :guard (pseudo-termp x)))
  (list (addend-pattern x) (addend-val x) x))

(defun info-entry-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (rationalp (cadr x))))

(defun addend-info-list (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (eq (fn-symb x) 'BINARY-+)
      (cons (addend-info-entry (arg1 x))
            (addend-info-list (arg2 x)))
    (list (addend-info-entry x))))

(defun info-list-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (info-entry-p (car x))
           (info-list-p (cdr x)))
    (eq x nil)))

(defthm rationalp-of-addend-val
  ;; [Jared] renaming from test-724 to something more sensible
  (implies (pseudo-termp x)
           (rationalp (addend-val x))))

(defthm info-list-p-of-addend-info-list
  ;; [Jared] renaming from test725 to something more sensible
  (implies (pseudo-termp x)
           (info-list-p (addend-info-list x))))

(defun assoc-addend (x info-list)
  (declare (xargs :guard (info-list-p info-list)))
  (cond ((endp info-list)
         nil)
        ((matching-addend-patterns-p x (caar info-list))
         (car info-list))
        (t
         (assoc-addend x (cdr info-list)))))

(defun first-match-in-addend-info-lists (info-list1 info-list2)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-addend (car (car info-list1)) info-list2)))
      (if temp
          (if (<= (cadr (car info-list1))
                  (cadr temp))
              (caddr (car info-list1))
            (caddr temp))
        (first-match-in-addend-info-lists (cdr info-list1) info-list2)))))

(defun find-matching-addends (lhs rhs)
  (declare (xargs :guard (and (pseudo-termp lhs)
                              (pseudo-termp rhs))))
  (let* ((info-list1 (addend-info-list lhs))
         (info-list2 (addend-info-list rhs))
         (match (first-match-in-addend-info-lists info-list1 info-list2)))
    (if match
        (list (cons 'x match))
      nil)))

(defthm simplify-sums-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (bind-free
                   (find-matching-addends lhs rhs)
                   (x)))
             (equal (equal lhs rhs)
                    (equal (+ (- x) lhs) (+ (- x) rhs)))))

(local
 (in-theory (disable simplify-sums-equal)))

(defthm simplify-sums-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (bind-free
                   (find-matching-addends lhs rhs)
                   (x)))
             (equal (< lhs rhs)
                    (< (+ (- x) lhs) (+ (- x) rhs)))))

(local
 (in-theory (disable simplify-sums-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun negative-addend-p (x)
  (declare (xargs :guard (pseudo-termp x)))
  (or (and (quotep x)
           (rationalp (unquote x))
           (< (unquote x) 0))
      (and (eq (fn-symb x) 'UNARY--)
           (or (variablep (arg1 x))
               (not (equal (ffn-symb (arg1 x)) 'UNARY--))))
      (and (eq (fn-symb x) 'BINARY-*)
           (rational-constant-p (arg1 x))
           (< (unquote (arg1 x)) 0))))

(defun find-negative-addend1 (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((not (eq (fn-symb x) 'BINARY-+))
         (if (negative-addend-p x)
             x
           nil))
        ((negative-addend-p (arg1 x))
         (arg1 x))
        ((eq (fn-symb (arg2 x)) 'BINARY-+)
         (find-negative-addend1 (arg2 x)))
        ((negative-addend-p (arg2 x))
         (arg2 x))
        (t
         nil)))

(defun find-negative-addend (lhs rhs)
  (declare (xargs :guard (and (pseudo-termp lhs)
                              (pseudo-termp rhs))))
  (let ((temp1 (find-negative-addend1 lhs)))
    (if temp1
        (list (cons 'x temp1))
      (let ((temp2 (find-negative-addend1 rhs)))
        (if temp2
            (list (cons 'x temp2))
          nil)))))

(defthm prefer-positive-addends-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (or (equal (fn-symb lhs) 'BINARY-+)
                               (equal (fn-symb rhs) 'BINARY-+)))
                  (bind-free
                   (find-negative-addend lhs rhs)
                   (x)))
             (equal (equal lhs rhs)
                    (equal (+ (- x) lhs) (+ (- x) rhs)))))

(local
 (in-theory (disable prefer-positive-addends-equal)))


(defthm prefer-positive-addends-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (or (equal (fn-symb lhs) 'BINARY-+)
                               (equal (fn-symb rhs) 'BINARY-+)))
                  (bind-free
                   (find-negative-addend lhs rhs)
                   (x)))
             (equal (< lhs rhs)
                    (< (+ (- x) lhs) (+ (- x) rhs)))))

(local
 (in-theory (disable prefer-positive-addends-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-gather-exponents-info-entry (x)
  (declare (xargs :guard (pseudo-termp x)))
  (list (factor-pattern-gather-exponents x)
        (factor-val-gather-exponents x)
        x))

(defun assoc-factor-gather-exponents (x info-list)
  (declare (xargs :guard (info-list-p info-list)))
  (cond ((endp info-list)
         nil)
        ((matching-factor-gather-exponents-patterns-p x (caar info-list))
         (car info-list))
        (t
         (assoc-factor-gather-exponents x (cdr info-list)))))

(defun factor-gather-exponents-intersect-info-lists (info-list1 info-list2)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-gather-exponents (caar info-list1) info-list2)))
      (cond ((not temp)
             (factor-gather-exponents-intersect-info-lists (cdr info-list1)
                                                           info-list2))
            ((<= (cadr temp) (cadr (car info-list1)))
             (cons temp
                   (factor-gather-exponents-intersect-info-lists (cdr info-list1)
                                                                 info-list2)))
            (t
             (cons (car info-list1)
                   (factor-gather-exponents-intersect-info-lists (cdr info-list1)
                                                                 info-list2)))))))

(defthm info-entry-p-of-assoc-factor-gather-exponents
  ;; [Jared] renaming from test-283 to something more sensible
  (implies (and (info-list-p info-list)
                (assoc-factor-gather-exponents x info-list))
           (info-entry-p (assoc-factor-gather-exponents x info-list))))

(defthm info-list-p-of-factor-gather-exponents-intersect-info-lists
  ;; [Jared] renaming from test-284 to something more sensible
  (implies (and (info-list-p info-list-1)
                (info-list-p info-list-2))
           (info-list-p (factor-gather-exponents-intersect-info-lists
                         info-list-1
                         info-list-2))))

(defthm rationalp-of-factor-val-gather-exponents
  ;; [Jared] renaming from test-285 to something more sensible; also changing
  ;; from :rewrite to :type-prescription
  (rationalp (factor-val-gather-exponents x))
  :rule-classes :type-prescription)

(defun factor-gather-exponents-info-list (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (let ((temp (factor-gather-exponents-info-list (arg2 x))))
           (if temp
               (factor-gather-exponents-intersect-info-lists
                temp
                (factor-gather-exponents-info-list (arg1 x)))
             nil)))
        ((eq (fn-symb x) 'BINARY-*)
         (cons (factor-gather-exponents-info-entry (arg1 x))
               (factor-gather-exponents-info-list (arg2 x))))
        (t
         (list (factor-gather-exponents-info-entry x)))))

;; [Jared] removing because it is redundant with, and worse than
;; rationalp-of-factor-val-gather-exponents
;; (defthm test-726
;;     (implies (pseudo-termp x)
;;              (rationalp (factor-val-gather-exponents x))))

(defthm info-list-p-of-factor-gather-exponents-info-list
  ;; [Jared] renaming from test727 to something more sensible
  (implies (pseudo-termp x)
           (info-list-p (factor-gather-exponents-info-list x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun first-match-in-factor-gather-exponents-info-lists (info-list1 info-list2)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-gather-exponents (car (car info-list1)) info-list2)))
      (if temp
          (if (<= (cadr (car info-list1))
                  (cadr temp))
              (caddr (car info-list1))
            (caddr temp))
        (first-match-in-factor-gather-exponents-info-lists (cdr info-list1) info-list2)))))

(defun find-matching-factors-gather-exponents (lhs rhs)
  (declare (xargs :guard (and (pseudo-termp lhs)
                              (pseudo-termp rhs))))
  (let* ((info-list1 (factor-gather-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-gather-exponents-info-list rhs)
                       nil))
         (match (if info-list2
                    (first-match-in-factor-gather-exponents-info-lists info-list1
                                                                       info-list2)
                  nil)))
    (if match
        (list (cons 'x match))
      nil)))

(defthm simplify-products-gather-exponents-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (bind-free
                   (find-matching-factors-gather-exponents lhs rhs)
                   (x))
                  (case-split (acl2-numberp x)))
             (equal (equal lhs rhs)
                    (if (equal x 0)
                        (equal (insert-0 x lhs) (insert-0 x rhs))
                      (equal (* (/ x) lhs) (* (/ x) rhs))))))

(local
 (in-theory (disable simplify-products-gather-exponents-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun first-rational-match-in-factor-gather-exponents-info-lists
    (info-list1 info-list2 mfc state)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-gather-exponents (car (car info-list1)) info-list2)))
      (if (and temp
               (proveably-rational (caddr temp) mfc state))
          (if (<= (cadr (car info-list1))
                  (cadr temp))
              (caddr (car info-list1))
            (caddr temp))
        (first-rational-match-in-factor-gather-exponents-info-lists (cdr info-list1) info-list2
                                                                    mfc state)))))

(defun find-rational-matching-factors-gather-exponents (lhs rhs mfc state)
  (declare (xargs :guard (and (pseudo-termp lhs)
                              (pseudo-termp rhs))))
  (let* ((info-list1 (factor-gather-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-gather-exponents-info-list rhs)
                       nil))
         (match (if info-list2
                    (first-rational-match-in-factor-gather-exponents-info-lists info-list1
                                                                                info-list2
                                                                                mfc state)
                  nil)))
    (if match
        (list (cons 'x match))
      nil)))

(defthm simplify-products-gather-exponents-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (bind-free
                   (find-rational-matching-factors-gather-exponents lhs rhs
                                                                    mfc state)
                   (x))
                  (case-split (rationalp x)))
             (equal (< lhs rhs)
                    (cond ((equal x 0)
                           (< (insert-0 x lhs) (insert-0 x rhs)))
                          ((< 0 x)
                           (< (* (/ x) lhs) (* (/ x) rhs)))
                          (t
                           (< (* (/ x) rhs) (* (/ x) lhs)))))))

(local
 (in-theory (disable simplify-products-gather-exponents-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factor-scatter-exponents-info-entry (x)
  (declare (xargs :guard (pseudo-termp x)))
  (list (factor-pattern-scatter-exponents x)
        (factor-val-scatter-exponents x)
        x))

(defun assoc-factor-scatter-exponents (x info-list)
  (declare (xargs :guard (info-list-p info-list)))
  (cond ((endp info-list)
         nil)
        ((matching-factor-scatter-exponents-patterns-p x (caar info-list))
         (car info-list))
        (t
         (assoc-factor-scatter-exponents x (cdr info-list)))))

(defun factor-scatter-exponents-intersect-info-lists (info-list1 info-list2)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-scatter-exponents (caar info-list1) info-list2)))
      (cond ((not temp)
             (factor-scatter-exponents-intersect-info-lists (cdr info-list1)
                                                           info-list2))
            ((<= (cadr temp) (cadr (car info-list1)))
             (cons temp
                   (factor-scatter-exponents-intersect-info-lists (cdr info-list1)
                                                                 info-list2)))
            (t
             (cons (car info-list1)
                   (factor-scatter-exponents-intersect-info-lists (cdr info-list1)
                                                                 info-list2)))))))

(defthm info-entry-p-of-assoc-factor-scatter-exponents
  ;; [Jared] renaming from test-287 to something more sensible
  (implies (and (info-list-p info-list)
                (assoc-factor-scatter-exponents x info-list))
           (info-entry-p (assoc-factor-scatter-exponents x info-list))))

(defthm info-list-p-of-factor-scatter-exponents-intersect-info-lists
  ;; [Jared] renaming from test-288 to something more sensible
  (implies (and (info-list-p info-list-1)
                (info-list-p info-list-2))
           (info-list-p (factor-scatter-exponents-intersect-info-lists
                         info-list-1
                         info-list-2))))

(defthm rationalp-of-factor-val-scatter-exponents
  ;; [Jared] renaming from test-289 to something more sensible; changing from
  ;; :rewrite to :type-prescription
  (rationalp (factor-val-scatter-exponents x))
  :rule-classes :type-prescription)

(defun factor-scatter-exponents-info-list (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (let ((temp (factor-scatter-exponents-info-list (arg2 x))))
           (if temp
               (factor-scatter-exponents-intersect-info-lists
                temp
                (factor-scatter-exponents-info-list (arg1 x)))
             nil)))
        ((eq (fn-symb x) 'BINARY-*)
         (cons (factor-scatter-exponents-info-entry (arg1 x))
               (factor-scatter-exponents-info-list (arg2 x))))
        (t
         (list (factor-scatter-exponents-info-entry x)))))

;; [Jared] removing because it's redundant with and worse than
;; rationalp-of-factor-val-scatter-exponents
;; (defthm test-728
;;     (implies (pseudo-termp x)
;;              (rationalp (factor-val-gather-exponents x))))

(defthm info-list-p-of-factor-gather-exponents-info-list
  ;; [Jared] renaming from test729 to something more sensible
  (implies (pseudo-termp x)
           (info-list-p (factor-gather-exponents-info-list x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun first-match-in-factor-scatter-exponents-info-lists (info-list1 info-list2)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-scatter-exponents (car (car info-list1)) info-list2)))
      (if temp
          (if (<= (cadr (car info-list1))
                  (cadr temp))
              (caddr (car info-list1))
            (caddr temp))
        (first-match-in-factor-scatter-exponents-info-lists (cdr info-list1) info-list2)))))

(defun find-matching-factors-scatter-exponents (lhs rhs)
  (declare (xargs :guard (and (pseudo-termp lhs)
                              (pseudo-termp rhs))))
  (let* ((info-list1 (factor-scatter-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-scatter-exponents-info-list rhs)
                       nil))
         (match (if info-list2
                    (first-match-in-factor-scatter-exponents-info-lists info-list1
                                                                       info-list2)
                  nil)))
    (if match
        (list (cons 'x match))
      nil)))

(defthm simplify-products-scatter-exponents-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (bind-free
                   (find-matching-factors-scatter-exponents lhs rhs)
                   (x))
                  (case-split (acl2-numberp x)))
             (equal (equal lhs rhs)
                    (if (equal x 0)
                        (equal (insert-0 x lhs) (insert-0 x rhs))
                      (equal (* (/ x) lhs) (* (/ x) rhs))))))

(local
 (in-theory (disable simplify-products-scatter-exponents-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun first-rational-match-in-factor-scatter-exponents-info-lists
    (info-list1 info-list2 mfc state)
    (declare (xargs :guard (and (info-list-p info-list1)
                                (info-list-p info-list2))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-factor-scatter-exponents (car (car info-list1)) info-list2)))
      (if (and temp
               (proveably-rational (caddr temp) mfc state))
          (if (<= (cadr (car info-list1))
                  (cadr temp))
              (caddr (car info-list1))
            (caddr temp))
        (first-rational-match-in-factor-scatter-exponents-info-lists (cdr info-list1) info-list2
                                                                     mfc state)))))

(defun find-rational-matching-factors-scatter-exponents (lhs rhs mfc state)
  (declare (xargs :guard (and (pseudo-termp lhs)
                              (pseudo-termp rhs))))
  (let* ((info-list1 (factor-scatter-exponents-info-list lhs))
         (info-list2 (if info-list1
                         (factor-scatter-exponents-info-list rhs)
                       nil))
         (match (if info-list2
                    (first-rational-match-in-factor-scatter-exponents-info-lists info-list1
                                                                                info-list2
                                                                                mfc state)
                  nil)))
    (if match
        (list (cons 'x match))
      nil)))

(defthm simplify-products-scatter-exponents-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (bind-free
                   (find-rational-matching-factors-scatter-exponents lhs rhs
                                                                    mfc state)
                   (x))
                  (case-split (rationalp x)))
             (equal (< lhs rhs)
                    (cond ((equal x 0)
                           (< (insert-0 x lhs) (insert-0 x rhs)))
                          ((< 0 x)
                           (< (* (/ x) lhs) (* (/ x) rhs)))
                          (t
                           (< (* (/ x) rhs) (* (/ x) lhs)))))))

(local
 (in-theory (disable simplify-products-scatter-exponents-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(defthm prefer-positive-exponents-gather-exponents-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (bind-free
                   (find-rational-negative-factor-gather-exponents lhs rhs
                                                                   mfc state)
                   (x))
                  (case-split (rationalp x)))
             (equal (< lhs rhs)
                    (cond ((equal x 0)
                           (< (insert-0 x lhs) (insert-0 x rhs)))
                          ((< 0 x)
                           (< (* (/ x) lhs) (* (/ x) rhs)))
                          (t
                           (< (* (/ x) rhs) (* (/ x) lhs)))))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-negative-factor-scatter-exponents2 (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((or (variablep x)
             (fquotep x))
         nil)
        ((eq (ffn-symb x) 'UNARY-/)
         x)
        ((eq (ffn-symb x) 'EXPT)
         (cond ((eq (fn-symb (arg1 x)) 'UNARY-/)
                x)
               ((and (quotep (arg1 x))
                     (not (integerp (cadr (arg1 x))))
                     (rationalp (cadr (arg1 x)))
                     (eql (numerator (cadr (arg1 x))) 1))
                x)
               ((eq (fn-symb (arg2 x)) 'UNARY--)
                x)
               ((and (eq (fn-symb (arg2 x)) 'BINARY-*)
                     (rational-constant-p (arg1 (arg2 x)))
                     (< (unquote (arg1 (arg2 x))) 0))
                x)
               (t
                nil)))
        ((eq (ffn-symb x) 'BINARY-*)
         (let ((temp (find-negative-factor-scatter-exponents2 (arg1 x))))
           (if temp
               temp
             (find-negative-factor-scatter-exponents2 (arg2 x)))))
        (t
         nil)))

(defun find-negative-factor-scatter-exponents1 (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((or (variablep x)
             (fquotep x))
         nil)
        ((eq (ffn-symb x) 'BINARY-+)
         (let ((temp (find-negative-factor-scatter-exponents2 (arg1 x))))
           (if temp
               temp
             (find-negative-factor-scatter-exponents1 (arg2 x)))))
        (t
         (find-negative-factor-scatter-exponents2 x))))

(defun find-negative-factor-scatter-exponents (lhs rhs)
  (declare (xargs :guard (and (pseudo-termp lhs)
                              (pseudo-termp rhs))))
  (let ((temp1 (find-negative-factor-scatter-exponents1 lhs)))
    (if temp1
        (list (cons 'x temp1))
      (let ((temp2 (find-negative-factor-scatter-exponents1 rhs)))
        (if temp2
            (list (cons 'x temp2))
          nil)))))

(defthm prefer-positive-exponents-scatter-exponents-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (equal rhs ''0)))
                  (syntaxp (not (equal lhs ''0)))
                  (bind-free
                   (find-negative-factor-scatter-exponents lhs rhs)
                   (x))
                  (case-split (acl2-numberp x)))
             (equal (equal lhs rhs)
                    (if (equal x 0)
                        (equal (insert-0 x lhs) (insert-0 x rhs))
                      (equal (* (/ x) lhs) (* (/ x) rhs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-rational-negative-factor-scatter-exponents2 (x mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((or (variablep x)
             (fquotep x))
         nil)
        ((eq (ffn-symb x) 'UNARY-/)
         (if (proveably-rational x mfc state)
             x
           nil))
        ((eq (ffn-symb x) 'EXPT)
         (cond ((eq (fn-symb (arg1 x)) 'UNARY-/)
                (if (proveably-rational x mfc state)
                    x
                  nil))
               ((and (quotep (arg1 x))
                     (not (integerp (cadr (arg1 x))))
                     (rationalp (cadr (arg1 x)))
                     (eql (numerator (cadr (arg1 x))) 1))
                (if (proveably-rational x mfc state)
                    x
                  nil))
               ((eq (fn-symb (arg2 x)) 'UNARY--)
                (if (proveably-rational x mfc state)
                    x
                  nil))
               ((and (eq (fn-symb (arg2 x)) 'BINARY-*)
                     (rational-constant-p (arg1 (arg2 x)))
                     (< (unquote (arg1 (arg2 x))) 0))
                (if (proveably-rational x mfc state)
                    x
                  nil))
               (t
                nil)))
        ((eq (ffn-symb x) 'BINARY-*)
         (let ((temp (find-rational-negative-factor-scatter-exponents2 (arg1 x) mfc state)))
           (if temp
               temp
             (find-rational-negative-factor-scatter-exponents2 (arg2 x) mfc state))))
        (t
         nil)))

(defun find-rational-negative-factor-scatter-exponents1 (x mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((or (variablep x)
             (fquotep x))
         nil)
        ((eq (ffn-symb x) 'BINARY-+)
         (let ((temp (find-rational-negative-factor-scatter-exponents2 (arg1 x) mfc state)))
           (if temp
               temp
             (find-rational-negative-factor-scatter-exponents1 (arg2 x) mfc state))))
        (t
         (find-rational-negative-factor-scatter-exponents2 x mfc state))))

(defun find-rational-negative-factor-scatter-exponents (lhs rhs mfc state)
  (declare (xargs :guard (and (pseudo-termp lhs)
                              (pseudo-termp rhs))))
  (let ((temp1 (find-rational-negative-factor-scatter-exponents1 lhs mfc state)))
    (if temp1
        (list (cons 'x temp1))
      (let ((temp2 (find-rational-negative-factor-scatter-exponents1 rhs mfc state)))
        (if temp2
            (list (cons 'x temp2))
          nil)))))

(defthm prefer-positive-exponents-scatter-exponents-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (equal rhs ''0)))
                  (syntaxp (not (equal lhs ''0)))
                  (bind-free
                   (find-rational-negative-factor-scatter-exponents lhs rhs
                                                                    mfc state)
                   (x))
                  (case-split (rationalp x)))
             (equal (< lhs rhs)
                    (cond ((equal x 0)
                           (< (insert-0 x lhs) (insert-0 x rhs)))
                          ((< 0 x)
                           (< (* (/ x) lhs) (* (/ x) rhs)))
                          (t
                           (< (* (/ x) rhs) (* (/ x) lhs)))))))
