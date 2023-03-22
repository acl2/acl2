; Recognizer for untranslated terms that are constants
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/quote" :dir :system) ; for myquotep

;; Recognizes an untranslated term that is a constant.
(defund untranslated-constantp (x)
  (declare (xargs :guard t))
  (or (acl2-numberp x) ;unquoted
      (characterp x) ;unquoted
      (stringp x) ;unquoted
      (and (symbolp x)
           (or (keywordp x) ;; unquoted keywords are constants
               ;; t, nil, and symbols that begin and end with * are constants:
               ;; TODO: Consider disallowing the symbol '*'.
               (legal-constantp1 x)))
      (myquotep x)))

;; (defthm car-when-untranslated-constantp
;;   (implies (untranslated-constantp x)
;;            (equal (car x)
;;                   (if (consp x)
;;                       'quote
;;                     nil)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable untranslated-constantp))))

(defthm untranslated-constantp-forward-to-true-listp
  (implies (and (untranslated-constantp term)
                (consp term))
           (true-listp term))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable untranslated-constantp))))

(defthm untranslated-constantp-forward-to-equal-of-car-and-quote
  (implies (and (untranslated-constantp term)
                (consp term))
           (equal (car term) 'quote))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable untranslated-constantp))))

(defthm untranslated-constantp-when-not-quotep-forward
  (implies (and (untranslated-constantp term)
                (not (equal 'quote (car term))))
           (not (consp term)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable untranslated-constantp))))

(defthm untranslated-constantp-of-cons
  (equal (untranslated-constantp (cons x y))
         (and (equal x 'quote)
              (true-listp y)
              (equal 1 (len y))))
  :hints (("Goal" :in-theory (enable untranslated-constantp))))
