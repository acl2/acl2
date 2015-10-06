;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

;; SMT-names ensures translation of names from LISP to
;; python is sound.

(in-package "ACL2")
(include-book "std/strings/top" :dir :system)

;; special-list
(defun special-list ()
  '((#\_ . (#\_ #\u #\s #\c #\_))
    (#\- . (#\_ #\s #\u #\b #\_))
    (#\+ . (#\_ #\a #\d #\d #\_))
    (#\* . (#\_ #\m #\l #\t #\_))
    (#\/ . (#\_ #\d #\i #\v #\_))
    (#\< . (#\_ #\l #\t #\_))
    (#\> . (#\_ #\g #\t #\_))
    (#\= . (#\_ #\e #\q #\l #\_))
    (#\! . (#\_ #\e #\x #\c #\_))
    (#\@ . (#\_ #\a #\t #\_))
    (#\# . (#\_ #\h #\s #\h #\_))
    (#\$ . (#\_ #\d #\l #\r #\_))
    (#\% . (#\_ #\p #\c #\t #\_))
    (#\^ . (#\_ #\c #\a #\r #\_))
    (#\& . (#\_ #\a #\m #\p #\_))
    )
  )

;; special-char
(defun special-char (char)
  (if (assoc char (special-list))
      t
    nil))

;; transform-special
(defun transform-special (char)
  (cdr (assoc char (special-list))))

;; to-HEX
(defun to-HEX (n)
  (str::natchars16 n))

;; construct-HEX
(defun construct-HEX (char)
  (append '(#\_)
          (to-HEX (char-code char))
          '(#\_)))

;; char-is-number
(defun char-is-number (char)
  (if (and (>= (char-code char) 48)
           (<= (char-code char) 57))
      t
    nil))

;; char-is-leter
(defun char-is-letter (char)
  (if (or (and (>= (char-code char) 65)
               (<= (char-code char) 90))
          (and (>= (char-code char) 97)
               (<= (char-code char) 122)))
      t
    nil))

;; lisp-to-python-names-char
(defun lisp-to-python-names-char (char)
  (cond ((or (char-is-number char) (char-is-letter char)) (list char))
        ((special-char char) (transform-special char))
        (t (construct-HEX char))))

;; lisp-to-python-names-list
(defun lisp-to-python-names-list (var-char)
  (if (endp var-char)
      nil
    (append (lisp-to-python-names-char (car var-char))
            (lisp-to-python-names-list (cdr var-char)))))

;; lisp-to-python-names-list-top
(defun lisp-to-python-names-list-top (var-char)
  (if (char-is-number (car var-char))
      (cons #\_
            (lisp-to-python-names-list var-char))
    (lisp-to-python-names-list var-char)))

;; lisp-to-python-names
(defun lisp-to-python-names (var)
  (let ((var-char (coerce (string var) 'LIST)))
    (intern-in-package-of-symbol
     (coerce
      (lisp-to-python-names-list-top var-char) 'STRING)
     'ACL2)
    ))

