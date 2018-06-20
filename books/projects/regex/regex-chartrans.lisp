; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


(in-package "ACL2")


(defun is-uppercase (c)
  (declare (xargs :guard (characterp c)))
  (and (standard-char-p c)
       (upper-case-p c)))

(defun is-lowercase (c)
  (declare (xargs :guard (characterp c)))
  (and (standard-char-p c)
       (lower-case-p c)))



(defun make-case-insens-translation (i)
  (declare (xargs :measure (nfix (- 256 i))
                  :guard (and (natp i)
                              (<= i 256))))
  (if (zp (- 256 i))
      nil
    (let ((char (code-char i)))
      (if (is-lowercase char)
          (cons (cons char (char-upcase char))
                (make-case-insens-translation (1+ i)))
        (make-case-insens-translation (1+ i))))))

(defconst *case-insens-translation*
  (make-case-insens-translation 0))

(in-theory (disable is-uppercase is-lowercase))

(defun translation-table-p (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (consp (car x))
         (characterp (caar x))
         (characterp (cdar x))
         (translation-table-p (cdr x)))))

(defthm translation-table-p-case-insens-trans
  (translation-table-p *case-insens-translation*))

(defthm assoc-translation-table
  (implies (and (translation-table-p trans)
                (assoc ch trans))
           (and (characterp (car (assoc ch trans)))
                (characterp (cdr (assoc ch trans))))))

(defun apply-translation1 (clist trans)
  (declare (xargs :guard (and (character-listp clist)
                              (translation-table-p trans))))
  (if (atom clist)
      nil
    (let* ((ch (car clist))
           (pair (assoc ch trans)))
      (cons (if pair (cdr pair) ch)
            (apply-translation1 (cdr clist) trans)))))

(defthm character-listp-apply-translation1
  (implies (and (character-listp clist)
                (translation-table-p trans))
           (character-listp (apply-translation1 clist trans))))

(defthm apply-translation1-length
  (equal (len (apply-translation1 clist trans))
         (len clist)))


(defun apply-translation (str trans)
  (declare (xargs :guard (and (stringp str)
                              (translation-table-p trans))))
  (coerce (apply-translation1 (coerce str 'list) trans) 'string))

(defthm stringp-apply-translation
  (implies (and (stringp str)
                (translation-table-p trans))
           (stringp (apply-translation str trans))))

(defthm apply-translation-length
  (implies (and (stringp str)
                (translation-table-p trans))
           (equal (length (apply-translation str trans))
                  (length str))))

(in-theory (disable apply-translation))

(defun case-insens-trans (str)
  (declare (xargs :guard (stringp str)))
  (apply-translation str *case-insens-translation*))

(defthm stringp-case-insens-trans
  (implies (stringp str)
           (stringp (case-insens-trans str))))

(defthm case-insens-trans-length
  (implies (stringp str)
           (equal (length (case-insens-trans str))
                  (length str))))

(in-theory (disable case-insens-trans))
