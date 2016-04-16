#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t :ttags :all);$ACL2s-Preamble$|#

#|
cgen-rules for ACL2 base
author: harshrc
file name: base-defdata::cgen-rules.lisp
date created: [2016-04-14 Thu]
|#

(in-package "ACL2")

(include-book "../defdata/cgen-rules")
(include-book "top" :ttags :all)

;;; LISTS -- most common data-structure in Lisp

;; TODO -- polymorphism


;; MEMBER-EQUAL

(defun member-fixer1 (x L)
  (declare (xargs :verify-guards nil
                  :guard (and (true-listp L)
                              (consp L))))
  (if (member-equal x L)
      x
    (b* ((n (len L))
         (elem (car L))
         (i (acl2-count elem))
         (i (mod i n)))
      (nth i L))))

(defdata::cgen-rule member-equal-fixer1
           :hyp (and (true-listp L)
                     (consp L))
           :rule (let ((x (member-fixer1 x L)))
                   (member-equal x L))
           :rule-classes :fixer
           :verbose t)

(defun member-fixer2 (a L)
  (declare (xargs :guard (and (true-listp L))))
  (if (member-equal a L)
      L
    (cons a L)))
      
(defdata::cgen-rule member-equal-fixer2
           :hyp (true-listp L)
           :rule (let ((L (member-fixer2 a L)))
                   (member-equal a L))
           :rule-classes :fixer)


;; LEN
(defun len-fixer1 (n L)
  (if (zp n)
      '()
    (if (endp L)
        (make-list n :initial-element 0)
      (if (>= (len L) n)
          (take n L)
        ;; add repetitions
        (append L (len-fixer1 (- n (len L)) L))))))
       
(defdata::cgen-rule len-fixer1
           :hyp (and (true-listp L)
                     (natp n))
           :rule (let ((L (len-fixer1 n L)))
                   (equal n (len L)))
           :rule-classes :fixer)



;; APPEND

(defun append-fixer1 (Z X1)
  (b* ((n (len X1))
       (X1 (take n Z))
       (X2 (nthcdr n Z)))
    (mv X1 X2)))
    
(defdata::cgen-rule append-fixer1
           :hyp (and (true-listp X1)
                     (true-listp X2)
                     (true-listp X3)
                     (>= (len X3) (len X1))
                     )
           :rule (mv-let (X1 X2) (append-fixer1 X3 X1)
                         (equal X3 (binary-append X1 X2)))
           :rule-classes :fixer)

(defun append-fixer2 (Z X2)
  (b* ((n (- (len Z) (len X2)))
       (X1 (take n Z))
       (X2 (nthcdr n Z)))
    (mv X1 X2)))

(defdata::cgen-rule append-fixer2
           :hyp (and (true-listp X1)
                     (true-listp X2)
                     (true-listp X3)
                     (>= (len X3) (len X2))
                     )
           :rule (mv-let (X1 X2) (append-fixer2 X3 X2)
                         (equal X3 (binary-append X1 X2)))
           :rule-classes :fixer)

;; COUNT

;; INTERSECTP

;; NO-DUPLICATESP, REMOVE-DUPLICATES-EQUAL

(defdata::cgen-rule no-dups-fixer
           :hyp (true-listp X1)
           :rule (let ((X1 (remove-duplicates-equal X1)))
                   (no-duplicatesp-equal X1))
           :rule-classes :fixer)

;; NTH, UPDATE-NTH
(defdata::cgen-rule nth-fixer2
           :hyp (and (true-listp L)
                     (natp n)
                     (< n (len L)))
           :rule (let ((L (update-nth n v L)))
                   (equal v (nth n L)))
           :rule-classes :fixer)

;; POSITION-EQUAL-AC

;; REMOVE-EQUAL
(defun rem-eql-fixer2 (a L L1)
  (if (endp L1)
      '()
    (if (endp L)
        L1
    (b* ((x (car L))
         (x1 (car L1))
         (rest (rem-eql-fixer2 a (cdr L) (cdr L1))))
      (if (equal a x)
          (cons a (cons x1 rest))
        (cons x1 rest))))))

(defdata::cgen-rule remove-equal-fixer2
           :hyp (and (true-listp L)
                     (true-listp L1)
                     (not (member-equal a L1))
                     )
           :rule (let ((L (rem-eql-fixer2 a L L1)))
                   (equal L1 (remove-equal a L)))
           :rule-classes :fixer)

;; REMOVE1-EQUAL
(defun remove1-equal-fixer2 (a L1)
  (cons a L1)) ;check later TODO
  
(defdata::cgen-rule remove1-equal-fixer2
           :hyp (and (true-listp L)
                     (true-listp L1)
                     )
           :rule (let ((L (remove1-equal-fixer2 a L1)))
                   (equal L1 (remove1-equal a L)))
           :rule-classes :fixer)
;; REVAPPEND

;; SET-DIFFERENCE-EQUAL

;; SUBSETP-EQUAL

(defun subsetp-equal-fixer1 (X1 X2)
  (if (endp X1)
      '()
    (if (member-equal (car X1) X2)
        (cons (car X1) (subsetp-equal-fixer1 (cdr X1) X2))
      (subsetp-equal-fixer1 (cdr X1) X2))))


(defdata::cgen-rule subsetp-equal-fixer1
           :hyp (and (true-listp X1)
                     (true-listp X2)
                     )
           :rule (let ((X1 (subsetp-equal-fixer1 X1 X2)))
                   (subsetp-equal X1 X2))
           :rule-classes :fixer)

(defdata::cgen-rule subsetp-equal-fixer2
           :hyp (and (true-listp X1)
                     (true-listp X2)
                     )
           :rule (let ((X2 (union-equal X1 X2)))
                   (subsetp-equal X1 X2))
           :rule-classes :fixer)

;; UNION-EQUAL



;;; ALISTS -- Association List

;; ASSOC-EQUAL



; Two choices.
; 1. Use free variable v
; 2. Use degrees of freedom in A itself to find the v
(defdata::cgen-rule assoc-equal-fixer2
           :hyp (and (alistp A)
                     (allp v))
           :rule (let ((A (put-assoc-equal x v A)))
                   (assoc-equal x A))
           :rule-classes :fixer)

(defun acl2::assoc-equal-fixer3 (x A)
  (declare (xargs :guard (alistp A)))
  (if (assoc-equal x A)
      A
    (if (endp A)
        (put-assoc-equal x 0 A)
      (put-assoc-equal x (cdr (car A)) A) ;reuse first entry's value
      )))

(defdata::cgen-rule assoc-equal-fixer3
  :hyp (alistp A)
  :rule (let ((A (acl2::assoc-equal-fixer3 x A)))
          (assoc-equal x A))
  :rule-classes :fixer)

(defdata::cgen-rule assoc-equal-fixer1
           :hyp (and (alistp A)
                     (consp A))
           :rule (let ((x (member-fixer1 x (strip-cars A))))
                   (assoc-equal x A))
           :rule-classes :fixer)

;; PAIRLIS$, STRIP-CARS, STRIP-CDRS


;;; NUMBERS
