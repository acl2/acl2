;Added guards March 25, 2004

;This file throws together a function order that orders the
; symbols in a list
; uses quicksort algorithm.
; call with something like: (order '(a h f d k))
;does not do much(any) error checking.. assumes good input

(in-package "ACL2")

;gonna use symbol< to order the elements of the list
(defun separate (pivot list less more)
  (declare (xargs :guard (and (symbol-listp list)
                              (symbolp pivot))))
  (if (consp list)
      (if (symbol< pivot (car list))
          (separate pivot (cdr list) less (cons (car list) more))
        (separate pivot (cdr list) (cons (car list) less) more))
    (mv less more)))
;(separate 'c '(f b d a) nil nil)


;-------------------------------------------------------------------
;ADMITTANCE LEMMAS

(defthm to-admit-less-gen
  (mv-let (less more) (separate pivot list a b)
          (declare (ignore more))
          (<= (acl2-count less)
              (+ (acl2-count list) (acl2-count a))))
  :rule-classes nil)

(defthm to-admit-more-gen
  (mv-let (less more) (separate pivot list a b)
          (declare (ignore less))
          (<= (acl2-count more)
              (+ (acl2-count list) (acl2-count b))))
  :rule-classes nil)

(defthm to-admit-less
  (mv-let (less more) (separate pivot list nil nil)
          (declare (ignore more))
          (<= (acl2-count less)
              (acl2-count list)))
  :hints (("Goal" :use (:instance to-admit-less-gen
                                  (pivot pivot)
                                  (list list)
                                  (a nil)
                                  (b nil))))
  :rule-classes :linear)

(defthm to-admit-more
  (mv-let (less more) (separate pivot list nil nil)
          (declare (ignore less))
          (<= (acl2-count more)
              (acl2-count list)))
  :hints (("Goal" :use (:instance to-admit-more-gen
                                  (pivot pivot)
                                  (list list)
                                  (a nil)
                                  (b nil))))
  :rule-classes :linear)

(defthm simple-cancellation
  (implies (and (<= (acl2-count x)
                    (acl2-count list))
                (consp list))
           (< (acl2-count (cdr x))
              (acl2-count list))))

(defthm simple-cancellation2
  (implies (and (<= (acl2-count x)
                    (acl2-count list))
                (consp list))
           (< (acl2-count (cdar x))
              (acl2-count list))))

(defthm cdr-more-decreases
  (implies (consp list)
           (< (acl2-count (cdr (mv-nth 1 (separate pivot list nil nil))))
              (acl2-count list)))
  :hints (("goal" :use to-admit-more)))

(defthm cdr-less-decreases
  (implies (consp list)
           (< (acl2-count (cdar (separate pivot list nil nil)))
              (acl2-count list)))
  :hints (("goal" :use to-admit-less)))

;END OF ADMITTANCE LEMMAS
;-------------------------------------------------------------------
(defun quick-order (pivot list)
  (declare (xargs :guard (and (symbol-listp list)
                              (symbolp pivot))
                  :verify-guards nil))
  (if (consp list)
      (mv-let (less more) (separate pivot list nil nil)
              (let ((new-less (if (consp less)
                                  (if (consp (cdr less))
                                      (quick-order (car less)
                                                   (cdr less))
                                    (list (car less)))
                                nil))
                    (new-more (if (consp more)
                                  (if (consp (cdr more))
                                      (cons pivot (quick-order
                                                   (car more)
                                                   (cdr more)))
                                    (cons pivot (list (car more))))
                                (list pivot))))
                (append new-less new-more)))
    nil))

;-------------------------------------------------------------------
; LEMMAS FOR THE GUARD VERIFICATIION

(defthm separate-symbol-listp
  (implies (and (symbol-listp list)
                (symbolp pivot)
                (symbol-listp less)
                (symbol-listp more))
           (mv-let (newless newmore)
                   (separate pivot list less more)
                   (and (symbol-listp newless)
                        (symbol-listp newmore)))))

(defthm symbol-listp-forward
  (implies (and (consp x)
                (symbol-listp x))
           (symbol-listp (cdr x))))

(defthm true-listp-quick-order
  (true-listp (quick-order pivot list)))

(defthm symbol-listp-cdar
  (implies (and (symbolp pivot)
                (symbol-listp list)
                (consp list)
                (consp (car (separate pivot list less more)))
                (symbol-listp less)
                (symbol-listp more))
           (symbol-listp (cdar (separate pivot list less more)))))

(defthm symbol-listp-car
  (implies (and (symbolp pivot)
                (symbol-listp list)
                (consp list)
                (consp (car (separate pivot list less more)))
                (symbol-listp less)
                (symbol-listp more))
           (symbol-listp (car (separate pivot list less more)))))


(defthm symbolp-first-first
  (implies (and (consp x)
                (symbol-listp x))
           (symbolp (car x))))

(defthm symbol-listp-append
  (implies (and (symbol-listp x)
                (symbol-listp y))
           (symbol-listp (append x y))))

;Needed for guard verification of common-parts2
(defthm symbol-listp-quick-order-of-symbol-lists
  (implies (and (symbolp x)
                (symbol-listp y))
           (symbol-listp (quick-order x y)))
)

;END OF LEMMAS FOR THE GUARD VERIFICATIION
;-------------------------------------------------------------------
(verify-guards quick-order
               :hints (("Subgoal 4" :use
                        (:instance symbolp-first-first
                                   (x (car (separate pivot list less more)))))))

;The final function
(defun order (list)
  (declare (xargs :guard (symbol-listp list)))
  (if (consp list)
      (if (consp (cdr list))
          (quick-order (car list) (cdr list))
        list)
    list))


