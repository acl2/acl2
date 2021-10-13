; A book about logic-termp and related functions
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable logic-termp
                    logic-term-listp
                    logic-term-list-listp))

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

(defthm logic-termp-when-regular-function-call
  (implies (and (symbolp (car term))
                (car term)
                ;(consp term)
                (not (eq 'quote (car term))))
           (equal (logic-termp term w)
                  (and (LOGICP (CAR TERM) W)
                       (equal (ARITY (CAR TERM) W)
                              (len (cdr term)))
                       (logic-term-listp (cdr term) w))))
  :hints (("Goal" :in-theory (enable logic-termp
                                     logic-term-listp))))

;move
(defthm LOGIC-TERMP-of-cadr-when-LOGIC-TERMP
  (IMPLIES (AND (LOGIC-TERMP TERM W)
                (symbolp (car term))
                (car term) ; implies (consp term)
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
