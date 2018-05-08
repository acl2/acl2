; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; Parsing of brace expressions such as {3}, {4,}, {2,5} etc


(in-package "ACL2")


(include-book "regex-defs")
(include-book "input-list")
(include-book "tools/mv-nth" :dir :system)

;; Digit parsing, for brace expressions
(defun get-digit-char (c)
  (declare (xargs :guard (characterp c)))
  (let ((n (char-code c)))
    (if (and (<= (char-code #\0) n) (<= n (char-code #\9)))
        (- n (char-code #\0))
    nil)))

(defthm get-digit-nonneg
  (or (not (get-digit-char c))
      (and (integerp (get-digit-char c))
           (<= 0 (get-digit-char c))))
  :rule-classes :type-prescription)

(in-theory (disable get-digit-char))

(defun parse-int (str idx)
  (declare (xargs :guard (and (stringp str)
                              (indexp idx str))
                  :measure (string-index-measure idx str)
                  :verify-guards nil))
  (if (string-index-end idx str)
      (mv nil idx 1)
    (let ((dig (get-digit-char (char str idx))))
      (if dig
          (mv-let (num rest power) (parse-int str (1+ idx))
                  (if num
                      (mv (+ (* power dig) num) rest (* 10 power))
                    (mv dig (1+ idx) 10)))
        (mv nil idx 1)))))


(defthm parse-int-type3
  (and (integerp (mv-nth 2 (parse-int str idx)))
       (<= 0 (mv-nth 2 (parse-int str idx))))
  :rule-classes (:rewrite :type-prescription))

(defthm parse-int-type1
  (or (not (mv-nth 0 (parse-int str idx)))
      (and (integerp (mv-nth 0 (parse-int str idx)))
           (<= 0 (mv-nth 0 (parse-int str idx)))))
  :rule-classes ((:rewrite
                  :corollary (implies (mv-nth 0 (parse-int str idx))
                                      (and (integerp (mv-nth 0 (parse-int str idx)))
                                           (<= 0 (mv-nth 0 (parse-int str idx))))))
                  :type-prescription))

(defthm parse-int-type2-weak
  (implies (natp idx)
           (and (integerp (mv-nth 1 (parse-int str idx)))
                (<= 0 (mv-nth 1 (parse-int str idx)))
                (<= idx (mv-nth 1 (parse-int str idx)))))
  :rule-classes (:rewrite
                 (:type-prescription
                  :corollary
                  (implies (natp idx)
                           (natp (mv-nth 1 (parse-int str idx)))))
                 (:linear
                  :corollary
                  (implies (natp idx)
                           (and (<= 0 (mv-nth 1 (parse-int str idx)))
                                (<= idx (mv-nth 1 (parse-int str idx))))))))

(defthm parse-int-type2-strong
  (implies (indexp idx str)
           (<= (mv-nth 1 (parse-int str idx)) (length str)))
  :rule-classes (:rewrite
                 (:linear
                  :corollary
                  (implies
                   (indexp idx str)
                   (<= (mv-nth 1 (parse-int str idx)) (length str))))))


(verify-guards parse-int)
;; (defthm character-list-cdr-character-list
;;   (implies (character-listp str)
;;            (character-listp (cdr str)))
;;   :rule-classes
;;   (:rewrite
;;    (:forward-chaining
;;     :trigger-terms ((character-listp (cdr str))))))


(defun close-brace-p (str idx opts)
  (declare (xargs :guard (and (stringp str)
                              (indexp idx str)
                              (parse-options-p opts))))
  (if (not (string-index-end idx str))
      (if (eq 'ere (parse-options-type opts))
          (if (equal (char str idx) #\})
              (mv t (1+ idx))
            (mv nil idx))
        (if (and (equal (char str idx) #\\)
                 (not (string-index-end (1+ idx) str))
                 (equal (char str (1+ idx)) #\}))
            (mv t (+ 2 idx))
          (mv nil idx)))
    (mv nil idx)))

(defthm close-brace-p-yes
  (implies (and (integerp idx)
                (mv-nth 0 (close-brace-p str idx opts)))
           (< idx (mv-nth 1 (close-brace-p str idx opts))))
  :rule-classes
  (:rewrite
   (:linear
    :corollary (implies (and (integerp idx)
                             (mv-nth 0 (close-brace-p str idx opts)))
                        (< idx (mv-nth 1 (close-brace-p str idx opts)))))))

(defthm close-brace-p-always
  (implies (integerp idx)
           (and (integerp (mv-nth 1 (close-brace-p str idx opts)))
                (<= idx (mv-nth 1 (close-brace-p str idx opts)))))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary (implies (and (integerp idx)
                             (mv-nth 0 (close-brace-p str idx opts)))
                        (integerp (mv-nth 1 (close-brace-p str idx opts)))))
   (:type-prescription
    :corollary (implies (and (natp idx)
                             (mv-nth 0 (close-brace-p str idx opts)))
                        (natp (mv-nth 1 (close-brace-p str idx opts)))))
   (:linear
    :corollary (implies (integerp idx)
                        (<= idx (mv-nth 1 (close-brace-p str idx opts)))))))

(defthm close-brace-p-len
  (implies (indexp idx str)
           (<= (mv-nth 1 (close-brace-p str idx opts)) (length str)))
  :rule-classes (:rewrite :linear))


(defthm close-brace-p-no
  (implies (not (mv-nth 0 (close-brace-p str idx opts)))
           (= (mv-nth 1 (close-brace-p str idx opts))
              idx)))

(defthm close-brace-parse-int
  (implies (indexp idx str)
           (<= (mv-nth 1 (close-brace-p str
                                        (mv-nth 1 (parse-int str idx))
                                        opts))
               (length str)))
  :rule-classes (:rewrite :linear))

(in-theory (disable close-brace-p))




(defun has-closing-brace (str idx opts)
  (declare (xargs :guard (and (stringp str)
                              (indexp idx str)
                              (parse-options-p opts))
                  :measure (string-index-measure idx str)))
  (if (string-index-end idx str)
      nil
    (mv-let (close rest) (close-brace-p str idx opts)
            (declare (ignore rest))
            (or close
                (has-closing-brace str (1+ idx) opts)))))


;; Parses brace expressions which may look like the following
;; {n}  matches exactly n
;; {n,m} matches between n and m inclusive (m >= n)
;; {,n} matches up to n
;; {n,} matches n or more
(defun parse-brace (str idx reg opts)
  (declare (xargs :guard (and (stringp str)
                              (indexp idx str)
                              (regex-p reg)
                              (parse-options-p opts))))
  (if (has-closing-brace str idx opts)
      ;; Grep doesn't allow opening comma;
      ;; use {0,n} instead
      ;; (if (equal (car str) #\,)
;;           (mv-let
;;            (num rest pow) (parse-int (cdr str))
;;            (declare (ignore pow))
;;            (if num
;;                (mv-let (close rest) (close-brace-p rest opts)
;;                        (if close
;;                            (mv `(repeat ,reg 0 ,num ) rest)
;;                          (mv "Bad character after number in brace" rest)))
;;              (mv "Bad character after comma beginning brace" rest)))
        (mv-let
         (num1 rest pow) (parse-int str idx)
         (declare (ignore pow))
         (if num1
             (if (and (not (string-index-end rest str))
                      (equal (char str rest) #\,)
                      (not (string-index-end (1+ rest) str)))
                 (mv-let
                  (close rest) (close-brace-p str (1+ rest) opts)
                  (if close
                      (mv (r-repeat reg num1 -1) rest)
                    (mv-let
                     (num2 rest pow) (parse-int str rest)
                     (declare (ignore pow))
                     (mv-let (close rest) (close-brace-p str rest opts)
                             (if (and num2
                                      (<= num1 num2)
                                      close)
                                 (mv (r-repeat reg num1 num2)
                                     rest)
                               (mv "Bad figure after comma in brace" rest))))))
               (mv-let (close rest) (close-brace-p str rest opts)
                       (if close
                           (mv (r-repeat reg num1 num1) rest)
                         (mv "Bad character after number in brace" rest))))
           (mv "Bad character begins brace" rest)))
    (mv "No closing brace" idx)))


(defthm parse-brace-index-weak
  (implies (natp idx)
           (and (integerp (mv-nth 1 (parse-brace str idx reg opts)))
                (<= 0  (mv-nth 1 (parse-brace str idx reg opts)))
                (<= idx (mv-nth 1 (parse-brace str idx reg opts)))))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary (implies (natp idx)
                        (natp (mv-nth 1 (parse-brace str idx reg opts)))))
   (:linear
    :corollary
    (implies (natp idx)
             (and (<= 0  (mv-nth 1 (parse-brace str idx reg opts)))
                  (<= idx (mv-nth 1 (parse-brace str idx reg opts))))))))

(defthm parse-brace-index-strong
  (implies (indexp idx str)
           (<= (mv-nth 1 (parse-brace str idx reg opts)) (length str)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (disable length))))

(defthm parse-brace-regexp
  (implies (and (regex-p reg)
                (not (stringp (mv-nth 0 (parse-brace str idx reg opts)))))
           (regex-p (mv-nth 0 (parse-brace str idx reg opts))))
  :rule-classes
  (:rewrite
   (:forward-chaining
    :trigger-terms ((mv-nth 0 (parse-brace str idx reg opts))))))

(defthm parse-brace-nonnil
  (mv-nth 0 (parse-brace str idx reg opts)))

(in-theory (disable parse-brace))
