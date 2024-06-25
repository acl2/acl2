; A book about logic-termp and related functions
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "logic-fnsp"))

;; This book is about these functions:
(in-theory (disable logic-termp
                    logic-term-listp
                    logic-term-list-listp))

(local (in-theory (disable ;member-equal
                           arglistp
                           all-vars
                           ;true-listp
                           )))

(defthm logic-termp-when-quotep
  (implies (quotep term)
           (equal (logic-termp term w)
                  (and (consp (cdr term))
                       (null (cddr term)))))
  :hints (("Goal" :in-theory (enable logic-termp))))

(defthm logic-termp-of-car-when-logic-term-listp
  (implies (logic-term-listp terms w)
           (equal (logic-termp (car terms) w)
                  (consp terms)))
  :hints (("Goal" :in-theory (enable logic-term-listp
                                     logic-termp))))

(defthm logic-term-listp-of-cdr
  (implies (logic-term-listp terms w)
           (logic-term-listp (cdr terms) w))
  :hints (("Goal" :in-theory (enable logic-term-listp))))

(defthm logic-termp-when-consp
  (implies (and (not (consp (car term))) ;exclude lambda (for now)
                (consp term))
           (equal (logic-termp term w)
                  (if (eq 'quote (car term))
                      (and (eq 'quote (car term))
                           (consp (cdr term))
                           (null (cddr term)))
                    (and (symbolp (car term))
                         (logicp (car term) w)
                         (equal (arity (car term) w)
                                (len (cdr term)))
                         (logic-term-listp (cdr term) w)))))
  :hints (("Goal" :expand (termp term w)
           :in-theory (enable logic-termp
                              logic-term-listp))))

;move
(defthm LOGIC-TERMP-of-cadr-when-LOGIC-TERMP
  (IMPLIES (AND (LOGIC-TERMP TERM W)
                (symbolp (car term))
                (consp term)
                (not (eq 'quote (car term)))
                (< 0 (ARITY (CAR TERM) W))
                )
           (LOGIC-TERMP (CADR TERM) W))
;  :hints (("Goal" :expand ((LOGIC-TERMP TERM W))))
  )

(defthm logic-term-list-listp-of-cons
  (equal (logic-term-list-listp (cons x y) w)
         (and (logic-term-listp x w)
              (logic-term-list-listp y w)))
  :hints (("Goal" :in-theory (enable logic-term-list-listp
                                     logic-fns-list-listp
                                     logic-term-listp))))

(defthm logic-term-listp-of-nil
  (logic-term-listp nil w)
  :hints (("Goal" :in-theory (enable logic-term-listp))))

(defthm logic-term-listp-of-cons
  (equal (logic-term-listp (cons x y) w)
         (and (logic-termp x w)
              (logic-term-listp y w)))
  :hints (("Goal" :in-theory (enable logic-termp
                                     logic-term-list-listp
                                     logic-fns-list-listp
                                     logic-term-listp))))

(defthm logic-term-listp-of-union-equal
  (equal (logic-term-listp (union-equal x y) w)
         (and (logic-term-listp (true-list-fix x) w)
              (logic-term-listp y w)))
  :hints (("Goal" :in-theory (enable logic-termp
                                     logic-term-list-listp
                                     logic-fns-list-listp
                                     logic-term-listp))))

(defthm logic-term-list-listp-of-nil
  (logic-term-list-listp nil w)
  :hints (("Goal" :in-theory (enable logic-term-list-listp
                                     logic-fns-list-listp
                                     logic-term-listp))))

(defthm logic-term-listp-forward-to-true-listp
  (implies (logic-term-listp terms w)
           (true-listp terms))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable logic-term-listp))))

;; Note sure if we want this
(defthmd logic-term-listp-forward-to-term-listp
  (implies (logic-term-listp terms w)
           (term-listp terms w))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable logic-term-listp))))

;move
(local
  (defthm arglistp-forward-to-true-listp
    (implies (arglistp x)
             (true-listp x))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable arglistp)))))

(defthm logic-termp-of-cons
  (equal (logic-termp (cons a x) wrld)
         (cond ((equal a 'quote) (and (consp x) (null (cdr x))))
               ((symbolp a)
                (and (not (programp a wrld))
                     (let ((arity (arity a wrld)))
                       (and arity
                            (logic-term-listp x wrld)
                            (equal (len x) ; was length
                                   arity)))))
               (t (and (consp a)
                       (true-listp a)
                       (equal (car a) 'lambda)
                       (equal 3 (len a)) ; was length
                       (arglistp (cadr a)) ; todo: call this legal-variable-listp?
                       (logic-termp (caddr a) wrld)
                       (null (set-difference-eq (all-vars (caddr a))
                                                (cadr a)))
                       (logic-term-listp x wrld)
                       ;; the calls of len here were calls of length
                       (eql (len (cadr a))
                            (len x))))))
  :hints (("Goal" :in-theory (enable logic-termp logic-term-listp))))
