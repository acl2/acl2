; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


;; Parsing of bracket expressions such as [a-z], [a-z3-9], [^bcd], etc



(in-package "ACL2")

(include-book "regex-defs")
(include-book "input-list")
(include-book "tools/mv-nth" :dir :system)

;; Parsing inside bracket expressions
(defun parse-bracket-inner (str idx last charset)
  (declare (xargs :guard (and (stringp str)
                              (natp idx)
                              (or (not last)
                                  (charset-memberp last))
                              (charsetp charset))
                  :measure (string-index-measure idx str)))

  (if (string-index-end idx str)
      ;; no closing bracket found
      (mv "Mismatched brackets" idx)

    ;; Binding of allprev to a couple cases where we just want
    ;; all previous stuff grouped together
    (let ((allprev
           (if last
               (cons last charset)
             (if charset
                 ;;this should never happen: last is nil but charset is nonnil
                 charset
               nil))))
      (case (char str idx)
        (#\]
         ;; Reached the end of the bracket expression
         (mv allprev (1+ idx)))
        (#\-
         ;; Unless last is nil or (cadr str) is ],
         (if (or (not last)
                 (string-index-end (1+ idx) str)
                 (equal (char str (1+ idx)) #\]))
             (parse-bracket-inner str (1+ idx) #\- allprev)
           (if (characterp last)
               (parse-bracket-inner str (+ 2 idx)
                                    `(range ,last ,(char str (1+ idx)))
                                    charset)
             (mv "Expression before dash was not a simple character" idx))))
        (otherwise
         ;; just a normal character, for our purposes
         (parse-bracket-inner str (1+ idx) (char str idx) allprev))))))

;; If parse-bracket-inner doesn't return an (error) string,|#
;; it returns a valid charset
(defthm parse-bracket-inner-charset
  (implies (and (stringp str)
                (natp idx)
                (or (not last)
                    (charset-memberp last))
                (charsetp charset)
                (not (stringp
                      (mv-nth 0 (parse-bracket-inner str idx last charset)))))
           (charsetp
            (mv-nth 0 (parse-bracket-inner str idx last charset)))))
;;   :rule-classes
;;   (:rewrite
;;    (:forward-chaining
;;     :trigger-terms ((charsetp (mv-nth 0 (parse-bracket-inner str idx last
;;                                                         charset)))))))

;; If it's given a charlist, it returns one (the unused part)
(defthm parse-bracket-inner-rest-integer
  (implies (integerp idx)
           (integerp (mv-nth 1 (parse-bracket-inner str idx last
                                                    charset)))))

(defthm parse-bracket-inner-rest-idx
  (implies (and (stringp str)
                (indexp idx str))
           (<= (mv-nth 1 (parse-bracket-inner str idx last charset)) (length str))))


;;Length of the unused part is <= length of the whole
(defthm parse-bracket-inner-rest-len
  (implies (integerp idx)
           (<= idx (mv-nth 1 (parse-bracket-inner str idx last charset))))
  :rule-classes (:rewrite :linear))


;; not sure if this is the best strategy or not
(in-theory (disable parse-bracket-inner))

(defthm parse-bracket-inner-rest-idx-corollary
  (implies (and (stringp str)
                (indexp (1+ idx) str))
           (<= (mv-nth 1 (parse-bracket-inner str (1+ idx) last charset))
               (length str)))
  :hints (("Goal" :use (:instance parse-bracket-inner-rest-idx
                                  (idx (1+ idx))))))

;; Parsing of bracket expressions
;; Pass the exploded string starting directly after the first bracket.
;; This calls the recursive function parse-bracket-inner after checking
;; conditions particular to the first character inside the bracket.
(defun parse-bracket (str idx)
  (declare (xargs :guard (and (stringp str)
                              (natp idx))
; Removed after v7-2 by Matt K. since the definition is non-recursive:
;                 :measure (string-index-measure idx str)
                  ))
  (if (string-index-end idx str)
      ;; No closing bracket found
      (mv "Mismatched brackets" idx)
    ;;Cases for first character
    (case (char str idx)
      (#\^
       ;; Invert the contents of this bracket exprn
       ;; Look for ] as second character and add it as literal character
       ;; if it's there.
       (if (and (not (string-index-end (1+ idx) str))
                (equal (char str (1+ idx)) #\]))
           (mv-let (charset rest) (parse-bracket-inner str (+ 2 idx) nil nil)
                   (if (stringp charset)
                       (mv charset rest)
                     (mv `(not #\] . ,charset) rest)))
         (mv-let (charset rest) (parse-bracket-inner str (1+ idx) nil nil)
                 (if (stringp charset)
                     (mv charset rest)
                   (mv `(not . ,charset) rest)))))
       (#\]
        ;; Return the rest of the bracket with ] consed on -
        ;; ] is only put in the charset if it is first.
        (parse-bracket-inner str (1+ idx) nil (list #\])))
       (otherwise
        ;; Everything else is handled exactly the way it is inside.
        (parse-bracket-inner str idx nil nil)))))

;; Need to experiment with leaving parse-bracket enabled and just using|#
;; the corresponding theorems about parse-bracket-inner.

(defthm parse-bracket-charset
  (implies (and (not (stringp (mv-nth 0 (parse-bracket str idx))))
                (stringp str))
           (charsetp (mv-nth 0 (parse-bracket str idx)))))
;;   :rule-classes
;;   (:rewrite
;;    (:forward-chaining
;;    :trigger-terms ((charsetp (mv-nth 0 (parse-bracket str)))))))


(defthm parse-bracket-integer
  (implies (integerp idx)
           (integerp (mv-nth 1 (parse-bracket str idx))))
  :rule-classes (:rewrite :type-prescription))

(defthm parse-bracket-index
  (implies (and (stringp str)
                (indexp idx str))
           (<= (mv-nth 1 (parse-bracket str idx)) (length str)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (disable length))))
;;   :rule-classes
;;   (:rewrite
;;    (:forward-chaining
;;    :trigger-terms ((character-listp (mv-nth 1 (parse-bracket str)))))))


(defthm parse-bracket-len
  (<= idx
      (mv-nth 1 (parse-bracket str idx)))
  :rule-classes (:rewrite :linear))
;;   :rule-classes
;;   (:rewrite
;;    (:forward-chaining
;;    :trigger-terms ((len (mv-nth 1 (parse-bracket str)))))))

(in-theory (disable parse-bracket))

