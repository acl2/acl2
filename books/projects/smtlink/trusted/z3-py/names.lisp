;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

;; SMT-names ensures translation of names from LISP to
;; python is sound.

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "std/strings/eqv" :dir :system)

(defsection SMT-names
  :parents (z3-py)
  :short "SMT-names generates SMT solver friendly names."

  (define character-fix (x)
    (declare (xargs :guard (characterp x)))
    (mbe :logic (if (characterp x) x (code-char 0))
         :exec x))

  (defthm character-fix-idempotent-lemma
    (equal (character-fix (character-fix x))
           (character-fix x))
    :hints (("Goal" :in-theory (enable character-fix))))

  (deffixtype character
    :fix character-fix
    :pred characterp
    :equiv character-equiv
    :define t)

  (local (in-theory (enable character-fix)))
  (defalist special-char-alist
    :key-type character
    :val-type character-listp
    :pred special-char-alistp
    :verbosep t)

  ;; special-list
  (define special-list ()
    (declare (xargs :guard t))
    :returns (special-list special-char-alistp)
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
  (define special-char ((char characterp))
    :returns (special-char? booleanp)
    (if (assoc char (special-list))
        t
      nil))

  ;; transform-special
  (define transform-special ((char characterp))
    :returns (special character-listp)
    (cdr (assoc char (special-list))))

  ;; to-HEX
  (define to-HEX ((n natp))
    :returns (hex hex-digit-char-listp)
    (natchars16 n))

  ;; construct-HEX
  (define construct-HEX ((char characterp))
    :returns (hex character-listp)
    (append '(#\_)
            (to-HEX (char-code char))
            '(#\_)))

  ;; char-is-number
  (define char-is-number ((char characterp))
    :returns (is-number? booleanp)
    (cond ((not (characterp char)) nil)
          ((and (>= (char-code char) 48)
                (<= (char-code char) 57)) t)
          (t nil))
    ///
    (more-returns
     (is-number? (implies is-number? (characterp char)) :name characterp-of-char-is-number)))

  ;; char-is-leter
  (define char-is-letter ((char characterp))
    :returns (is-letter? booleanp)
    (cond ((not (characterp char)) nil)
          ((or (and (>= (char-code char) 65)
                    (<= (char-code char) 90))
               (and (>= (char-code char) 97)
                    (<= (char-code char) 122))) t)
          (t nil))
    ///
    (more-returns
     (is-letter? (implies is-letter? (characterp char)) :name characterp-of-char-is-letter)))

  ;; lisp-to-python-names-char
  (define lisp-to-python-names-char ((char characterp))
    :returns (expanded-char character-listp)
    (cond ((or (char-is-number char) (char-is-letter char)) (list char))
          ((special-char char) (transform-special char))
          (t (construct-HEX char))))

  (encapsulate ()
    (local (defthm lemma
             (implies (and (character-listp a) (character-listp b))
                      (character-listp (append a b)))))

    ;; lisp-to-python-names-list
    (define lisp-to-python-names-list ((var-char character-listp))
      :returns (new-name character-listp)
      (if (endp var-char)
          nil
        (append (lisp-to-python-names-char (car var-char))
                (lisp-to-python-names-list (cdr var-char)))))
    )

  ;; lisp-to-python-names-list-top
  (define lisp-to-python-names-list-top ((var-char character-listp))
    :returns (new-name character-listp)
    :guard-debug t
    (cond ((endp var-char) nil)
          ((char-is-number (car var-char))
           (cons #\_ (lisp-to-python-names-list var-char)))
          (t (lisp-to-python-names-list var-char))))


  (define string-or-symbol-p (name)
    :returns (p? booleanp)
    (or (stringp name) (symbolp name)))

  (define string-or-symbol-fix ((x string-or-symbol-p))
    (mbe :logic (if (string-or-symbol-p x) x nil)
         :exec x))

  (local (in-theory (enable string-or-symbol-fix)))
  (deffixtype string-or-symbol
    :fix string-or-symbol-fix
    :pred string-or-symbol-p
    :equiv string-or-symbol-equiv
    :define t)

  (local (in-theory (enable characterp string-or-symbol-p)))
  ;; lisp-to-python-names
  (define lisp-to-python-names ((var string-or-symbol-p))
    :returns (name stringp)
    (b* ((var (string-or-symbol-fix var))
         (var (if (stringp var) var (string var)))
         (var-char (coerce var 'LIST)))
      (coerce (lisp-to-python-names-list-top var-char) 'STRING)))

  )
