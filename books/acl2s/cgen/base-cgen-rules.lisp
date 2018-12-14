#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t :ttags :all);$ACL2s-Preamble$|#

#|
cgen-rules for ACL2 base
author: harshrc
file name: base-cgen-rules.lisp
date created: [2016-04-14 Thu]
|#

(in-package "ACL2")

(include-book "cgen-rules")
(include-book "top" :ttags :all)
(local (acl2s-defaults :set :use-fixers nil))

; [2016-04-25 Mon] NOTE -- Most of these list functions are missing the
; true-listp hypothesis and this rules out many of the fixer rules. So I am
; also adding a type-hyp-free rule version, but these must later mechanically
; generated.

;; EQUAL and MEMBER-EQUAL are built into CGEN, but EQUAL is especially
;; taken care of in the fixers middle end. MEMBER-EQUAL is treated
;; uniformly below like other fixer rules.


;; (cgen::define-rule equal-meta1
;;   :meta-precondition (variablep x)
;;   :hyp t
;;   :rule (let ((x (identity term)))
;;           (equal x term))
;;   :rule-classes :fixer)

;; (cgen::define-rule equal-meta2
;;   :meta-precondition (variablep x)
;;   :hyp t
;;   :rule (let ((x (identity term)))
;;           (equal term x))
;;   :rule-classes :fixer)

(defun tlp-fxr (L)
  (declare (xargs :guard t))
  (if (atom L)
      nil ;(acl2s::nth-true-list (acl2-count L))
    (cons (car L) (tlp-fxr (cdr L)))))
          
(defthm tlp-fxr-type
  (true-listp (tlp-fxr L))
  :rule-classes (:rewrite :type-prescription))

(defthm tlp-fxr-type2
  (implies (consp L)
           (consp (tlp-fxr L)))
  :rule-classes (:rewrite :type-prescription))

(defthm tlp-fxr-type3
  (equal (len (tlp-fxr L))
         (len L)))

(in-theory (disable tlp-fxr))

(defun member-fixer1 (x L)
  (declare (xargs :verify-guards t
                  :guard (consp L)
                  :guard-hints (("Goal" :in-theory (disable mod)))
                  ))
  (let ((L (tlp-fxr L)))
    (if (member-equal x L)
        x
      (b* ((n (len L))
           (elem (car L))
           (i (nfix (acl2-count elem))) ; alternatively use x
           (i (mod i n)))
        (nth i L)))))

(cgen::define-rule member-equal-fixer1
  :hyp (consp L)
  :rule (let ((x (member-fixer1 x L)))
          (member-equal x L))
  :rule-classes :fixer
  )


;;; LISTS -- most common data-structure in Lisp

;; TODO -- polymorphism


;; MEMBER-EQUAL

(defun member-fixer2 (a L)
  (declare (xargs :guard t))
  (let ((L (tlp-fxr L)))
    (if (member-equal a L)
        L
      (cons a L))))
      
(cgen::define-rule member-equal-fixer2-type-fixed
  :rule (let ((L (member-fixer2 a L)))
          (member-equal a L))
  :rule-classes :fixer)


;; LEN
(defun len-fixer/repeat (n L)
  (if (zp n)
      '()
    (if (endp L)
        (make-list n :initial-element 0)
        (if (>= (len L) n)
            (take n L)
          ;; add repetitions
          (append L (len-fixer/repeat (- n (len L)) L))))))

       
(cgen::define-rule len-fixer1-with-repetitions
           :hyp (natp n)
           :rule (let ((L (len-fixer/repeat n L)))
                   (equal n (len L)))
           :rule-classes :fixer)

(cgen::define-rule len-fixer1-with-repetitions-symm
           :hyp (natp n)
           :rule (let ((L (len-fixer/repeat n L)))
                   (equal (len L) n))
           :rule-classes :fixer)

;; APPEND

(defun append-fixer1 (Z X1)
  (b* ((n (len X1))
       ((when (> n (len Z))) (mv Z '()))
       (X1 (take n Z))
       (X2 (nthcdr n Z)))
    (mv X1 X2)))
    
(cgen::define-rule append-fixer1
  :hyp (true-listp X3) ;dont worry about this, it will backchain!
  :rule (mv-let (X1 X2) (append-fixer1 X3 X1)
                (equal X3 (binary-append X1 X2)))
  :rule-classes :fixer)


(defun append-fixer2 (Z X2)
  (b* ((n (- (len Z) (len X2)))
       (X1 (take n Z))
       (X2 (nthcdr n Z)))
    (mv X1 X2)))

(cgen::define-rule append-fixer2
  :hyp (true-listp X3)
  :rule (mv-let (X1 X2) (append-fixer2 X3 X2)
                (equal X3 (binary-append X1 X2)))
  :rule-classes :fixer)

;; COUNT

;; INTERSECTP

(defun intersectp-fix1 (X1 X2)
  (declare (xargs :guard (consp X2)))
  (if (intersectp-equal (tlp-fxr X1) (tlp-fxr X2))
      (tlp-fxr X1)
    (b* ((a (member-fixer1 1 X2)))
      (add-to-set-equal a (tlp-fxr X1)))))
         
(cgen::define-rule intersectp-fixer1
  :hyp (consp X2)
  :rule (let ((X1 (intersectp-fix1 X1 X2)))
          (intersectp-equal X1 X2))
  :rule-classes :fixer)

(cgen::define-rule intersectp-fixer2
  :hyp (consp X1)
  :rule (let ((X2 (intersectp-fix1 X2 X1)))
          (intersectp-equal X1 X2))
  :rule-classes :fixer)


(defun _max-lst1 (xs ans)
  (declare (xargs :guard (real/rationalp ans)))
  (if (atom xs)
      ans
    (_max-lst1 (cdr xs) (max (rfix (car xs)) ans))))

(defun _max-lst (xs)
  (_max-lst1 xs 0))

; nat * nat -> (listof nat)
(defun _make-numlist (curr size)
;make a list of size natural numbers starting from curr
  (declare (xargs :guard (and (real/rationalp curr) (natp size))))
  (if (zp size)
      '()
    (cons curr (_make-numlist (1+ curr) (1- size)))))


(defun not-intersectp-fix2 (X1 X2)
  "fixer for (not (intersectp X1 X2)). preserves the length of X1"
  (if (not (intersectp-equal (tlp-fxr X1) (tlp-fxr X2)))
      (tlp-fxr X1)
    (b* ((common-elements (intersection-equal X1 X2))
         (n (len common-elements))
         (m (_max-lst X2))
         (new (_make-numlist (1+ m) n)))
      (append new (set-difference-equal X1 common-elements)))))

(cgen::define-rule not-intersectp-fixer1
  :rule (let ((X1 (not-intersectp-fix2 X1 X2)))
          (not (intersectp-equal X1 X2)))
  :rule-classes :fixer)

(cgen::define-rule not-intersectp-fixer2
  :rule (let ((X2 (not-intersectp-fix2 X2 X1)))
          (not (intersectp-equal X1 X2)))
  :rule-classes :fixer)




;; NO-DUPLICATESP, REMOVE-DUPLICATES-EQUAL

(defun no-dups-fix (x)
  (declare (xargs :guard t))
  (remove-duplicates-equal (tlp-fxr x)))

(cgen::define-rule no-dups-fixer-type-fixed
           :rule (let ((X1 (no-dups-fix X1)))
                   (no-duplicatesp-equal X1))
           :rule-classes :fixer)

;; NTH, UPDATE-NTH
(cgen::define-rule nth-fixer2
  :hyp (and (natp n)
            (< n (len L)))
           :rule (let ((L (update-nth n v (tlp-fxr L))))
                   (equal v (nth n L))) ;TODO orient equalities in preprocessing
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

(cgen::define-rule remove-equal-fixer2
  :hyp (and (not (member-equal a L1))
            (true-listp L1)
            )
           :rule (let ((L (rem-eql-fixer2 a (tlp-fxr L) L1)))
                   (equal L1 (remove-equal a L)))
           :rule-classes :fixer)

;; REMOVE1-EQUAL
(defun remove1-equal-fixer2 (a L1)
  (cons a L1)) ;check later TODO
  
(cgen::define-rule remove1-equal-fixer2
  :hyp (true-listp L1)
  :rule (let ((L (remove1-equal-fixer2 a (tlp-fxr L1))))
          (equal L1 (remove1-equal a L)))
  :rule-classes :fixer)

;; REVAPPEND

;; SET-DIFFERENCE-EQUAL

;; SUBSETP-EQUAL

(defun subsetp-fixer1 (X1 X2)
  (if (atom X1)
      '()
    (if (member-equal (car X1) X2)
        (cons (car X1) (subsetp-fixer1 (cdr X1) X2))
      (subsetp-fixer1 (cdr X1) X2))))

(cgen::define-rule subsetp-equal-fixer1-type-fixed
  :rule (let ((X1 (subsetp-fixer1 X1 X2)))
          (subsetp-equal X1 X2))
  :rule-classes :fixer)

(cgen::define-rule subsetp-equal-fixer2-type-fixed
  :rule (let ((X2 (union-equal (tlp-fxr X1) (tlp-fxr X2))))
          (subsetp-equal X1 X2))
  :rule-classes :fixer)

;; UNION-EQUAL



;;; ALISTS -- Association List

;; ASSOC-EQUAL

; Two choices.
; 1. Use free variable v
; 2. Use degrees of freedom in A itself to find the v
(defun consp-fixer/for-alist-fixer (p)
  (if (consp p)
      p
    (cons p nil)))

(defun alist-fixer (A)
  (if (atom A)
      nil ;(acl2s::nth-alist (acl2-count A))
    (cons (consp-fixer/for-alist-fixer (car A))
          (alist-fixer (cdr A)))))

(defthm alist-fixer-type
  (alistp (alist-fixer L))
  :rule-classes (:rewrite :type-prescription))

(defthm alist-fixer-type2
  (implies (consp L)
           (consp (alist-fixer L)))
  :rule-classes (:rewrite :type-prescription))

(defthm alist-fixer-type3
  (equal (len (alist-fixer L))
         (len L)))

(in-theory (disable alist-fixer))


(cgen::define-rule assoc-equal-fixer2
           :hyp (acl2s::allp v) ;technical reason for putting this! TODO make polymorphic
           :rule (let ((A (put-assoc-equal x v (alist-fixer A))))
                   (assoc-equal x A))
           :rule-classes :fixer)

(defun assoc-fxr3 (x A)
  (let ((A (alist-fixer A)))
    (if (assoc-equal x A)
        A
      (if (endp A)
          (put-assoc-equal x 0 A)
        (put-assoc-equal x (cdr (car A)) A) ;reuse first entry's value
        ))))

(cgen::define-rule assoc-equal-fixer3
  :rule (let ((A (acl2::assoc-fxr3 x A)))
          (assoc-equal x A))
  :rule-classes :fixer)

(cgen::define-rule assoc-equal-fixer1
  :hyp (and (consp A) (alistp A))
  :rule (let ((x (member-fixer1 x (strip-cars A))))
          (assoc-equal x A))
  :rule-classes :fixer)

(cgen::define-rule assoc-eq-equation-fixer
  :rule (let ((A (put-assoc-equal x v (alist-fixer A))))
          (equal v (cdr (assoc-equal x A))))
  :rule-classes :fixer)

;; PAIRLIS$, STRIP-CARS, STRIP-CDRS


;;; NUMBERS
