; Rules about the built-in function pseudo-termp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider having this book disable pseudo-termp

(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(defthm pseudo-termp-of-nth-alt
  (implies (and (pseudo-termp term)
                ;; (consp term)
                (posp n)
                (not (equal (car term) 'quote)))
           (pseudo-termp (nth n term)))
  :hints (("Goal" :expand (pseudo-termp term)
           :cases ((< n (len term)))
           :in-theory (enable pseudo-termp nth))))

(defthm pseudo-term-listp-of-cdr-when-pseudo-termp
  (implies (and (pseudo-termp term)
                (not (equal (car term) 'quote)))
           (pseudo-term-listp (cdr term)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-term-listp-of-cdr-when-pseudo-termp-cheap
  (implies (and (pseudo-termp term)
                (not (equal (car term) 'quote)))
           (pseudo-term-listp (cdr term)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

;; In case length is called
(defthm not-stringp-of-cdr-when-pseudo-termp
  (implies (pseudo-termp term)
           (not (stringp (cdr term))))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthmd pseudo-termp-when-not-consp
  (implies (not (consp term))
           (equal (pseudo-termp term)
                  (symbolp term))))

(defthmd symbolp-when-pseudo-termp
  (implies (pseudo-termp term)
           (equal (symbolp term)
                  (not (consp term)))))

;maybe we should use consp as the normal form instead
(defthmd pseudo-termp-when-not-consp-cheap
  (implies (not (consp term))
           (equal (pseudo-termp term)
                  (symbolp term)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm symbolp-of-nth-0-when-pseudo-termp-cheap
  (implies (pseudo-termp term)
           (equal (symbolp (nth 0 term))
                  (not (consp (nth 0 term)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm pseudo-termp-of-nth-2-of-nth-0-when-pseudo-termp-cheap
  (implies (pseudo-termp term)
           (pseudo-termp (nth 2 (nth 0 term))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm symbol-listp-of-nth-1-of-nth-0-when-pseudo-termp-cheap
  (implies (pseudo-termp term)
           (symbol-listp (nth 1 (nth 0 term))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm len-of-nth-1-of-nth-0-when-pseudo-termp-cheap
  (implies (and (pseudo-termp term)
                (consp (car term)))
           (equal (len (nth 1 (nth 0 term)))
                  (len (fargs term))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm consp-of-cddr-of-nth-0-when-pseudo-termp-cheap
  (implies (pseudo-termp term)
           (equal (consp (cddr (nth 0 term)))
                  (consp (nth 0 term))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm cddr-of-nth-0-when-pseudo-termp-cheap-iff
  (implies (pseudo-termp term)
           (iff (cddr (nth 0 term))
                (consp (nth 0 term))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm cdr-of-nth-0-when-pseudo-termp-cheap-iff
  (implies (pseudo-termp term)
           (iff (cdr (nth 0 term))
                (consp (nth 0 term))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm len-of-nth-0-when-pseudo-termp-cheap
  (implies (pseudo-termp term)
           (equal (len (nth 0 term))
                  (if (consp (nth 0 term))
                      3
                    0)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm len-of-car-when-pseudo-termp-cheap
  (implies (pseudo-termp term)
           (equal (len (car term))
                  (if (consp (car term))
                      3
                    0)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm true-listp-of-car-when-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp (car term)))
           (true-listp (car term)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm car-of-car-when-pseudo-termp
  (implies (pseudo-termp term)
           (equal (car (car term))
                  (if (consp (car term))
                      'lambda
                    nil)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

;; Use (consp (car term)) as the normal form for saying it's a lambda application
(defthm symbolp-of-car-when-pseudo-termp
  (implies (pseudo-termp term)
           (equal (symbolp (car term))
                  (not (consp (car term)))))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm pseudo-termp-forward-to-true-listp
  (implies (and (pseudo-termp x)
                (not (symbolp x)))
           (true-listp x))
  :rule-classes :forward-chaining)

(defthmd len-when-pseudo-termp-and-quotep-cheap
  (implies (and (pseudo-termp term)
                (equal 'quote (nth 0 term)))
           (equal (len term)
                  2))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

;leave disabled since this can introduce pseudo-termp out of nowhere
;gross to use nth (nth 0 term) here?
(defthmd len-when-pseudo-termp-and-quotep
  (implies (and (pseudo-termp term)
                (equal 'quote (nth 0 term)))
           (equal (len term)
                  2))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm len-when-pseudo-termp-and-quotep-alt
  (implies (and (equal 'quote (car term))
                (pseudo-termp term))
           (equal (len term)
                  2))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthm cddr-when-pseudo-termp-and-quotep
  (implies (and (equal 'quote (car term))
                (pseudo-termp term))
           (equal (cddr term)
                  nil))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

;; Kept disabled for speed
(defthmd pseudo-termp-when-symbolp
  (implies (symbolp term)
           (pseudo-termp term)))

(defthm pseudo-termp-of-lambda-body-of-car-when-pseudo-termp
  (implies (and (pseudo-termp term)
                ;; (consp (car term))
                )
           (pseudo-termp (lambda-body (car term)))))

(defthm symbol-listp-of-lambda-formals-of-car-when-pseudo-termp
  (implies (and (pseudo-termp term)
                ;; (consp (car term))
                )
           (symbol-listp (lambda-formals (car term)))))

(defthm not-stringp-of-lambda-formals-of-car-when-pseudo-termp
  (implies (and (pseudo-termp term)
                ;; (consp (car term))
                )
           (not (stringp (lambda-formals (car term))))))

;; Which do we prefer as the normal form, len of the formals, or len of the args?
(defthm len-of-lambda-formals-of-car-when-pseudo-termp
  (implies (pseudo-termp term)
           (equal (len (lambda-formals (car term)))
                  (if (consp (car term))
                      (len (cdr term))
                    ;; weird case:
                    0))))
