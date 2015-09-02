; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; normalize.lisp
;;;
;;; This book comtains some rules to gather "like" terms within
;;; a sum or product.
;;;
;;; For gathering products there are two distinct behaviours.
;;; Under the theory scatter-exponents (the default) exponents
;;; consisting of sums are broken apart or scattered, e.g.,
;;; (expt x (+ m n)) ===> (* (expt x m) (expt x n)).
;;; Under the other theory, gather-exponents, the reverse is true,
;;; e.g., (* (expt x m) (expt x n)) ===> (expt x (+ m n)).
;;; These two theories are defined in top, using rules from this
;;; book and elsewhere.
;;;
;;; Some simple examples of gathering like terms:
;;; 1. (+ a b (* 3 a)) ===> (+ b (* 4 a))
;;; 2. gather-exponents:
;;;    (* a b (expt a n)) ===> (* b (expt a (+ n 1)))
;;; 3. scatter-exponents:
;;;    (* a b (expt a n)) no change
;;; 4. both gather-exponents and scatter-exponents:
;;;    (* a b b) ===> (* a (expt b 2))
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "basic"))

(include-book "common")

(local
 (in-theory (enable collect-+)))

(local
 (in-theory (enable collect-*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun distribute-* (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (* x y))

(defthm distribute-*-distributes-1
    (equal (distribute-* x y)
           (* x y)))

(defthm distribute-*-distributes-2
    (equal (distribute-* (+ x y) z)
           (+ (* x z) (distribute-* y z))))

(in-theory (disable distribute-*))

(defun factors (product)
  (declare (xargs :guard (pseudo-termp product)))
  (if (eq (fn-symb product) 'BINARY-*)
      (cons (fargn product 1)
            (factors (fargn product 2)))
    (list product)))

(defun factors-other-than-denominator (addend denominator)
  (declare (xargs :guard (and (pseudo-termp addend)
                              (pseudo-termp denominator))))
  (if (eq (fn-symb addend) 'BINARY-*)
      (if (and (eq (fn-symb (fargn addend 1)) 'UNARY-/)
               (equal (fargn (fargn addend 1) 1) denominator))
          (factors-other-than-denominator (fargn addend 2) denominator)
        (cons (fargn addend 1)
              (factors-other-than-denominator (fargn addend 2) denominator)))
    (if (and (eq (fn-symb addend) 'UNARY-/)
             (equal (fargn addend 1) denominator))
        nil
      (list addend))))

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

(defun number-of-addends (sum)
  (declare (xargs :guard (pseudo-termp sum)))
  (if (eq (fn-symb sum) 'BINARY-+)
      (+ 1 (number-of-addends (fargn sum 2)))
    1))

(defun find-denominators-with-sums (addend denominator-list
                                    number-of-addends-in-sum)
  (declare (xargs :guard (and (pseudo-termp addend)
                              (integerp number-of-addends-in-sum))))
  (cond ((or (variablep addend)
             (fquotep addend))
         denominator-list)
        ((eq (fn-symb addend) 'BINARY-*)
         (if (and (eq (fn-symb (fargn addend 1)) 'UNARY-/)
                  (eq (fn-symb (fargn (fargn addend 1) 1)) 'BINARY-+)
                  (consp (cdr (fargn (fargn addend 1) 1)))  ;; for guards
                  (<= (number-of-addends (fargn (fargn addend 1) 1))
                      number-of-addends-in-sum))
             (find-denominators-with-sums (fargn addend 2)
                                          (cons (fargn (fargn addend 1) 1)
                                                denominator-list)
                                          number-of-addends-in-sum)
           (find-denominators-with-sums (fargn addend 2)
                                        denominator-list
                                        number-of-addends-in-sum)))
        ((and (eq (fn-symb addend) 'UNARY-/)
              (eq (fn-symb (fargn addend 1)) 'BINARY-+)
              (consp (cdr (fargn addend 1)))
              (<= (number-of-addends (fargn addend 1))
                  number-of-addends-in-sum))
         (cons (fargn addend 1) denominator-list))
        (t
         denominator-list)))

(defun to-be-found (denominator saved-denominator factors to-be-found)
  (declare (xargs :guard (and (pseudo-termp denominator)
                              (true-listp factors)
                              (true-listp to-be-found))))
  (if (eq (fn-symb denominator) 'BINARY-+)
      (let ((factors-2 (factors (fargn denominator 1))))
        (if (intersectp-equal factors factors-2)
            nil
          (to-be-found (fargn denominator 2) saved-denominator factors
                       (cons (cons saved-denominator (append factors-2 factors))
                             to-be-found))))
    (let ((factors-2 (factors denominator)))
      (if (intersectp-equal factors factors-2)
          nil
        (reverse (cons (cons saved-denominator (append factors-2 factors))
                       to-be-found))))))

(defun set-equal (a b)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b))))
  (and (subsetp-equal a b)
       (subsetp-equal b a)))

(defun remainder-aaa (to-be-found rest remainder)
  (declare (xargs :guard (and (true-list-listp to-be-found)
                              (pseudo-termp rest)
                              (pseudo-termp remainder))))
  (cond ((endp to-be-found)
         remainder)
        ((null rest)
         nil)
        ((eq (fn-symb rest) 'BINARY-+)
         (if (set-equal (factors (fargn rest 1)) (car to-be-found))
             (remainder-aaa (cdr to-be-found) (fargn rest 2) remainder)
           (remainder-aaa to-be-found (fargn rest 2)
                          (if (null remainder)
                              (fargn rest 1)
                            (list 'BINARY-+ (fargn rest 1) remainder)))))
        ((null (cdr to-be-found))
         (if (set-equal (factors rest) (car to-be-found))
             (if remainder
                 remainder
               ''0)
           nil))
        (t
         nil)))


;; [Jared]  localizing since this seems like it should be local
(local (defthm test381
         (implies (and (true-list-listp x)
                       (true-list-listp y))
                  (true-list-listp (revappend x y)))))

;; [Jared]  localizing since this seems like it should be local
(local (defthm test382
         (implies (true-listp x)
                  (true-listp (append a x)))))

;; [Jared]  localizing since this seems like it should be local
(local (defthm test392
         (implies (and (pseudo-termp denominator)
                       (true-listp factors)
                       (true-list-listp to-be-found))
                  (true-list-listp (to-be-found denominator
                                                saved-denominator
                                                factors
                                                to-be-found)))))

;; [Jared]  localizing since this seems like it should be local
(local (defthm test-302
         (implies (and (not (equal (car denominator) 'quote))
                       (consp denominator)
                       (pseudo-termp denominator))
                  (pseudo-termp (cadr denominator)))
         :hints (("goal" :expand (pseudo-termp denominator)))))

;; [Jared]  localizing since this seems like it should be local
(local (defthm test-303
         (implies (and (not (equal (car denominator) 'quote))
                       (consp denominator)
                       (pseudo-termp denominator))
                  (pseudo-termp (caddr denominator)))
         :hints (("goal" :expand (pseudo-termp denominator)))))

(defun denominatorp (denominator)
  (declare (xargs :guard t))
  (and (pseudo-termp denominator)
       (not (variablep denominator))
       (not (equal (car denominator) 'QUOTE))
       (consp (cdr denominator))))

(defun normalize-terms-such-as-a/a+b-+-b/a+b-fn-2 (denominator addend rest)
  (declare (xargs :guard (and (denominatorp denominator)
                              (pseudo-termp addend)
                              (pseudo-termp rest))))
  (let ((factors1 (factors-other-than-denominator addend denominator))
        (factors2 (factors (fargn denominator 1))))
    (if (intersectp-equal factors1 factors2)
        (let* ((factors (set-difference-equal factors1 factors2))
               (to-be-found (to-be-found (fargn denominator 2)
                                         (list 'UNARY-/ denominator)
                                         factors nil))
               (remainder (remainder-aaa to-be-found rest nil)))
          (if remainder
              (list (cons 'factor (make-product factors))
                    (cons 'denominator denominator)
                    (cons 'remainder remainder)
                    (cons 'a (fargn denominator 1)))
            nil))
      nil)))

(defun denominator-list-p (denominator-list)
  (declare (xargs :guard t))
  (if (atom denominator-list)
      (equal denominator-list nil)
    (and (denominatorp (car denominator-list))
         (denominator-list-p (cdr denominator-list)))))

(defun normalize-terms-such-as-a/a+b-+-b/a+b-fn-1 (denominator-list addend rest)
  (declare (xargs :guard (and (denominator-list-p denominator-list)
                              (pseudo-termp addend)
                              (pseudo-termp rest))))
  (if (endp denominator-list)
      nil
    (let ((binding-alist
           (normalize-terms-such-as-a/a+b-+-b/a+b-fn-2 (car denominator-list)
                                                       addend rest)))
      (if binding-alist
          binding-alist
        (normalize-terms-such-as-a/a+b-+-b/a+b-fn-1 (cdr denominator-list)
                                                    addend rest)))))

;; [Jared]  localizing since this seems like it should be local
(local (defthm test-928
         (implies (AND (integerp int)
                       (PSEUDO-TERMP X)
                       (CONSP X)
                       (EQUAL (CAR X) 'BINARY-*)
                       (denominator-list-p ans))
                  (DENOMINATOR-LIST-P
                   (FIND-DENOMINATORS-WITH-SUMS X ans int)))))

; We do not catch things such as
; (+ (* a x (/ (+ a (* b x)))) (* b (expt x 2) (/ (+ a (* b x)))))

(defun normalize-terms-such-as-a/a+b-+-b/a+b-fn (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (if (eq (fn-symb x) 'BINARY-*)
      (normalize-terms-such-as-a/a+b-+-b/a+b-fn-1
       (find-denominators-with-sums x
                                    nil
                                    (+ 1 (number-of-addends y)))
       x
       y)
    nil))

(encapsulate
 ()

 (local
  (include-book "../pass1/top"))

 (defthm normalize-terms-such-as-a/a+b-+-b/a+b
     (implies (and (bind-free
                    (normalize-terms-such-as-a/a+b-+-b/a+b-fn x y)
                    (factor denominator remainder a))
                   (acl2-numberp remainder)
                   (acl2-numberp denominator)
                   (equal x (* factor a (/ denominator)))
                   (equal y
                          (+ (* factor (distribute-* (- denominator a)
                                                     (/ denominator)))
                             remainder)))
              (equal (+ x y)
                     (if (equal denominator 0)
                         remainder
                       (+ factor remainder)))))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defun common-factors (factors sum)
  (declare (xargs :measure (acl2-count sum)
                  :guard (and (pseudo-term-listp factors)
                              (pseudo-termp sum))))
  (cond ((null factors)
         nil)
        ((eq (fn-symb sum) 'BINARY-+)
         (common-factors (intersection-equal factors (factors (fargn sum 1)))
                         (fargn sum 2)))
        (t
         (intersection-equal factors (factors sum)))))

(defthm pseudo-term-listp-of-factors
  ;; [Jared] renamed from test529 to something more sensible
  (implies (pseudo-termp x)
           (pseudo-term-listp (factors x))))

(defun normalize-terms-such-as-1/ax+bx-fn (sum)
  (declare (xargs :guard (pseudo-termp sum)))
  (if (and (eq (fn-symb sum) 'BINARY-+)
           (eq (fn-symb (fargn sum 1)) 'BINARY-*))
      (let ((common-factors (common-factors (factors (fargn sum 1))
                                            (fargn sum 2))))
        (if common-factors
            (let ((common (make-product common-factors))
                  (remainder (remainder-bbb common-factors sum)))
              (list (cons 'common common)
                    (cons 'remainder remainder)))
          nil))
    nil))

(defthm normalize-terms-such-as-1/ax+bx
    (implies (and (bind-free
                   (normalize-terms-such-as-1/ax+bx-fn sum)
                   (common remainder))
                  (equal sum
                         (* common remainder)))
             (equal (/ sum)
                    (* (/ common) (/ remainder)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-matching-addend (to-match x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (cond ((matching-addend-p to-match (arg1 x))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-+)
                (find-matching-addend to-match (arg2 x)))
               ((matching-addend-p to-match (arg2 x))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((matching-addend-p to-match x)
         (list (cons 'match x)))
        (t
         nil)))

(defthm normalize-addends
    (implies (bind-free
              (find-matching-addend (addend-pattern x) y)
              (match))
             (equal (+ x y)
                    (+ (bubble-down x match) y))))

(theory-invariant
 (or (not (active-runep '(:rewrite normalize-addends)))
     (and (active-runep '(:rewrite bubble-down-+-bubble-down))
          (active-runep '(:rewrite bubble-down-+-match-1))
          (active-runep '(:rewrite bubble-down-+-match-2))
          (not (active-runep '(:rewrite bubble-down)))
          (not (active-runep '(:executable-counterpart bubble-down)))))
 :error nil)

(local
 (in-theory (disable normalize-addends)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-matching-factor-gather-exponents (to-match x)
  (declare (xargs :guard (and (true-listp to-match)
                              (pseudo-termp x))))
  (cond ((eq (fn-symb x) 'BINARY-*)
         (cond ((matching-factor-gather-exponents-p to-match (arg1 x))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-*)
                (find-matching-factor-gather-exponents to-match (arg2 x)))
               ((matching-factor-gather-exponents-p to-match (arg2 x))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((matching-factor-gather-exponents-p to-match x)
         (list (cons 'match x)))
        (t
         nil)))

(defthm normalize-factors-gather-exponents
    (implies (bind-free
              (find-matching-factor-gather-exponents
               (factor-pattern-gather-exponents x) y)
              (match))
             (equal (* x y)
                    (* (bubble-down x match) y))))

(theory-invariant
 (or (not (active-runep '(:rewrite normalize-factors-gather-exponents)))
     (and (active-runep '(:rewrite bubble-down-*-bubble-down))
          (active-runep '(:rewrite bubble-down-*-match-1))
          (active-runep '(:rewrite bubble-down-*-match-2))
          (not (active-runep '(:rewrite bubble-down)))
          (not (active-runep '(:executable-counterpart bubble-down)))))
 :error nil)

(local
 (in-theory (disable normalize-factors-gather-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-matching-factor-scatter-exponents (to-match x)
  (declare (xargs :guard (and (true-listp to-match)
                              (pseudo-termp x))))
  (cond ((eq (fn-symb x) 'BINARY-*)
         (cond ((matching-factor-scatter-exponents-p to-match (arg1 x))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-*)
                (find-matching-factor-scatter-exponents to-match (arg2 x)))
               ((matching-factor-scatter-exponents-p to-match (arg2 x))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((matching-factor-scatter-exponents-p to-match x)
         (list (cons 'match x)))
        (t
         nil)))

(defthm normalize-factors-scatter-exponents
    (implies (bind-free
              (find-matching-factor-scatter-exponents
               (factor-pattern-scatter-exponents x) y)
              (match))
             (equal (* x y)
                    (* (bubble-down x match) y))))

(theory-invariant
 (or (not (active-runep '(:rewrite normalize-scatter-exponents)))
     (and (active-runep '(:rewrite bubble-down-*-bubble-down))
          (active-runep '(:rewrite bubble-down-*-match-1))
          (active-runep '(:rewrite bubble-down-*-match-2))
          (not (active-runep '(:rewrite bubble-down)))
          (not (active-runep '(:executable-counterpart bubble-down)))))
 :error nil)

(local
 (in-theory (disable normalize-factors-scatter-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(theory-invariant
 (not (and (active-runep '(:rewrite normalize-factors-gather-exponents))
           (active-runep '(:rewrite normalize-factors-scatter-exponents))))
 :error nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(defun denominator-matches (denominator z)
  (declare (xargs :guard t))
  (cond ((or (variablep z)
             (fquotep z))
         nil)
        ((eq (ffn-symb z) 'UNARY-/)
         (equal (fargn z 1) denominator))
        ((eq (ffn-symb z) 'BINARY-*)
         (or (denominator-matches denominator (fargn z 1))
             (denominator-matches denominator (fargn z 2))))
        (t
         nil)))

(defun binary-star-leaves (x)
  (declare (xargs :guard t))
  (cond ((eq (fn-symb x) 'BINARY-*)
         (cons (fargn x 1) (binary-star-leaves (fargn x 2))))
        (t
         (list x))))

(defun binary-star-tree (leaves)
  (declare (xargs :guard t))
  (cond ((null leaves)
         ''1)
        ((null (cdr leaves))
         (car leaves))
        ((null (cddr leaves))
         (list 'BINARY-* (car leaves) (cadr leaves)))
        (t
         (list 'BINARY (car leaves)
               (binary-star-tree (cdr leaves))))))

(defun bail-out-1 (denominator z number)
  (declare (xargs :guard t))
  (cond ((equal number 1)
         nil)
        ((or (variablep z)
             (fquotep z))
         t)
        ((eq (ffn-symb z) 'BINARY-+)
         (if (denominator-matches denominator (fargn z 1))
             (bail-out-1 denominator (fargn z 2) (- number 1))
           (bail-out-1 denominator (fargn z 2) number)))
        (t
         (or (< 2 number)
             (not (denominator-matches denominator z))))))

(defun bail-out-2 (denominator leaves2---leaves1)
  (declare (xargs :guard t))
  (cond ((eq (fn-symb denominator) 'BINARY-+)
         (or (bail-out-2 (fargn denominator 1) leaves2---leaves1)
             (bail-out-2 (fargn denominator 2) leaves2---leaves1)))
        (t
         (subsetp-equal (binary-star-leaves denominator) leaves2---leaves1))))

(defun number-of-addends (denominator)
  (declare (xargs :guard t))
  (cond ((or (variablep denominator)
             (fquotep denominator))
         1)
        ((eq (ffn-symb denominator) 'BINARY-+)
         (+ 1 (number-of-addends (fargn denominator 2))))
        (t
         1)))

(defun find-rest-of-ratio-helper1 (denominator leaves1---leaves2 leaves2---leaves1)
  (declare (xargs :guard t))
  (cond ((eq (fn-symb denominator) 'BINARY-+)
         (cons (find-rest-of-ratio-helper1 (fargn denominator 1)
                                           leaves1---leaves2
                                           leaves2---leaves1)
               (find-rest-of-ratio-helper1 (fargn denominator 2)
                                           leaves1---leaves2
                                           leaves2---leaves1)))
        (t
         (list (union-equal leaves1---leaves2
                            (set-difference-equal (binary-star-leaves denominator)
                                                  leaves2---leaves1))))))

(defun find-rest-of-ratio-helper (numerator denominator z)
  (declare (xargs :guard t))
  (cond ((not (eq (fn-symb denominator) 'BINARY-+))
         (mv nil nil))
        ((bail-out-1 denominator z (number-of-addends denominator))
         (mv nil nil))
        (t
         (let ((leaves1 (binary-star-leaves numerator))
               (leaves2 (binary-star-leaves (fargn denominator 1))))
           (if (intersectp-equal leaves1 leaves2)
               (let ((leaves1---leaves2 (set-difference-equal leaves1 leaves2))
                     (leaves2---leaves1 (set-difference-equal leaves2 leaves1)))
                 (if (bail-out-2 (fargn denominator 2) leaves2---leaves1)
                     (mv nil nil)
                   (let ((to-be-found (find-rest-of-ratio-helper1 (fargn denominator 2)
                                                                  leaves1---leaves2
                                                                  leaves2---leaves1))
                         (factor (list 'BINARY-* (binary-star-tree leaves1---leaves2)
                                       (list 'UNARY-/ (binary-star-tree
                                                       leaves2---leaves1)))))
                     (mv to-be-found factor))))
             (mv nil nil))))))

(defun find-rest-of-ratio2 (to-be-found denominator z d)
  (declare (xargs :guard t))
  (if (denominator-matches denominator z)
      ()
    (let ((d (if d
                 (list 'BINARY-+ z d)
               z)))
      (mv to-be-found d))))

(defun find-rest-of-ratio1 (to-be-found denominator z factor d)
  (declare (xargs :guard t))
  (cond ((null to-be-found)
         (list (cons 'c factor)
               (cons 'd d)))
        ((or (fquotep z)
             (variablep z))
         nil)
        ((eq (ffn-symb z) 'BINARY-+)
         (mv-let (to-be-found d)
           (find-rest-of-ratio2 to-be-found denominator (fargn z 1) d)
           (find-rest-of-ratio1 to-be-found denominator (fargn z 2) factor d)))
        (t
         (if (< 1 (length to-be-found))
             nil
           (mv-let (to-be-found d)
             (find-rest-of-ratio2 to-be-found denominator z d)
             (if (null to-be-found)
                 (list (cons 'c factor)
                       (cons 'd d))
               nil))))))


(defthm find-rest-of-ratio (numerator denominator z)
  (mv-let (to-be-found factor)
    (find-rest-of-ratio-helper numerator denominator)
    (if to-be-found
        (find-rest-of-ratio1 to-be-found denominator z factor nil)
      nil)))

(defthm normalize-terms-such-as-a/a+b-+-b/a+b
    (implies (and (bind-free
                   (find-rest-of-ratio numerator denominator z)
                   (factor remainder))
                  (equal (+ (* factor denominator (/ denominator)) remainder)
                         (+ (* numerator (/ denominator)) z)))
             (equal (+ (* numerator (/ denominator)) z)
                    (if (equal denominator 0)
                        remainder
                      (+ factor remainder)))))
|#

