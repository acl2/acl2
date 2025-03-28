; A stronger version of quotep
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: What is a good name for this?

;quotep by itself is not a sufficient guard for doing unquote!
(defun myquotep (item)
  (declare (xargs :guard t))
  (and (quotep item)
       (consp (cdr item))
       (null (cdr (cdr item)))))

(defthm myquotep-forward
  (implies (myquotep item)
           (equal (car item) 'quote))
  :rule-classes :forward-chaining)

;; ;; In case we are turning car into nth:
;; (defthm myquotep-forward-to-equal-of-nth-0-and-quotge
;;   (implies (myquotep item)
;;            (equal (nth 0 item) 'quote))
;;   :rule-classes :forward-chaining)

;fix name
(defthm myquotep-forward-to-consp
  (implies (myquotep item)
           (and (consp item)
                (true-listp item)))
  :rule-classes :forward-chaining)

(defthm myquotep-forward-to-quotep
  (implies (myquotep item)
           (quotep item))
  :rule-classes :forward-chaining)

(defthm myquotep-forward-to-equal-of-len
  (implies (myquotep x)
           (equal 2 (len x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable myquotep))))

;; (defthm myquotep-forward-to-not-cddr
;;   (implies (myquotep x)
;;            (not (cdr (cdr x))))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable myquotep))))

(defthm myquotep-of-list-of-quote
  (myquotep (list 'quote x))
  :hints (("Goal" :in-theory (enable myquotep))))
