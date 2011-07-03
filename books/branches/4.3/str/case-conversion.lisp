
(in-package "STR")

(include-book "unicode/rev" :dir :system)
(include-book "eqv")

(defmacro little-a () (char-code #\a))
(defmacro little-z () (char-code #\z))
(defmacro big-a () (char-code #\A))
(defmacro big-z () (char-code #\Z))
(defmacro case-delta () (- (big-a) (little-a)))


;; Like standard char-upcase, but doesn't require standard-char-p (because it
;; doesn't have to comply with Common Lisp, I guess.)
(defun upcase-char (x)
  (declare (xargs :guard (characterp x)))
  (let ((code (char-code x)))
    (if (and (<= (little-a) code)
             (<= code (little-z)))
        (code-char (+ (case-delta) code))
      (char-fix x))))

(defthm characterp-upcase-char
  (characterp (upcase-char x)))

(defun downcase-char (x)
  (declare (xargs :guard (characterp x)))
  (let ((code (char-code x)))
    (if (and (<= (big-a) code)
             (<= code (big-z)))
        (code-char (- code (case-delta)))
      (char-fix x))))

(defthm characterp-downcase-char
  (characterp (downcase-char x)))


(defun upcase-charlist-aux (x acc)
  (declare (Xargs :guard (and (character-listp x)
                              (character-listp acc))))
  (if (atom x)
      (mbe :logic (acl2::rev acc)
           :exec (reverse acc))
    (upcase-charlist-aux (cdr x) (cons (upcase-char (car x)) acc))))

(defun upcase-charlist (x)
  (declare (Xargs :guard (character-listp x)
                  :verify-guards nil))
  (mbe :logic
       (if (atom x)
           nil
         (cons (upcase-char (car x))
               (upcase-charlist (cdr x))))
       :exec
       (upcase-charlist-aux x nil)))

(defthm upcase-charlist-aux-is-upcase-charlist
  (equal (upcase-charlist-aux x acc)
         (revappend acc (upcase-charlist x))))

(verify-guards upcase-charlist)

(defthm character-listp-upcase-charlist
  (character-listp (upcase-charlist x)))

(in-theory (disable upcase-charlist))



(defun downcase-charlist-aux (x acc)
  (declare (Xargs :guard (and (character-listp x)
                              (character-listp acc))))
  (if (atom x)
      (mbe :logic (acl2::rev acc)
           :exec (reverse acc))
    (downcase-charlist-aux (cdr x) (cons (downcase-char (car x)) acc))))

(defun downcase-charlist (x)
  (declare (Xargs :guard (character-listp x)
                  :verify-guards nil))
  (mbe :logic
       (if (atom x)
           nil
         (cons (downcase-char (car x))
               (downcase-charlist (cdr x))))
       :exec
       (downcase-charlist-aux x nil)))

(defthm downcase-charlist-aux-is-downcase-charlist
  (equal (downcase-charlist-aux x acc)
         (revappend acc (downcase-charlist x))))

(verify-guards downcase-charlist)

(defthm character-listp-downcase-charlist
  (character-listp (downcase-charlist x)))

(in-theory (disable downcase-charlist))



(defun upcase-string (x)
  (declare (xargs :guard (stringp x)))
  (coerce (upcase-charlist (coerce x 'list)) 'string))

(defthm stringp-upcase-string
  (stringp (upcase-string x)))

(in-theory (disable upcase-string))


(defun downcase-string (x)
  (declare (xargs :guard (stringp x)))
  (coerce (downcase-charlist (coerce x 'list)) 'string))

(defthm stringp-downcase-string
  (stringp (downcase-string x)))

(in-theory (disable downcase-string))


(defun upcase-string-list-aux (x acc)
  (declare (xargs :guard (and (string-listp x)
                              (string-listp acc))))
  (if (atom x)
      (mbe :logic (acl2::rev acc)
           :exec (reverse acc))
    (upcase-string-list-aux (cdr x) (cons (upcase-string (car x)) acc))))

(defun upcase-string-list (x)
  (declare (xargs :guard (string-listp x)
                  :verify-guards nil))
  (mbe :logic
       (if (atom x)
           nil
         (cons (upcase-string (car x))
               (upcase-string-list (cdr x))))
       :exec (upcase-string-list-aux x nil)))

(defthm upcase-string-list-aux-is-upcase-string-list
  (equal (upcase-string-list-aux x acc)
         (revappend acc (upcase-string-list x))))

(verify-guards upcase-string-list)

(defthm string-listp-upcase-string-list
  (string-listp (upcase-string-list x)))


(defun downcase-string-list-aux (x acc)
  (declare (xargs :guard (and (string-listp x)
                              (string-listp acc))))
  (if (atom x)
      (mbe :logic (acl2::rev acc)
           :exec (reverse acc))
    (downcase-string-list-aux (cdr x) (cons (downcase-string (car x)) acc))))

(defun downcase-string-list (x)
  (declare (xargs :guard (string-listp x)
                  :verify-guards nil))
  (mbe :logic
       (if (atom x)
           nil
         (cons (downcase-string (car x))
               (downcase-string-list (cdr x))))
       :exec (downcase-string-list-aux x nil)))

(defthm downcase-string-list-aux-is-downcase-string-list
  (equal (downcase-string-list-aux x acc)
         (revappend acc (downcase-string-list x))))

(verify-guards downcase-string-list)

(defthm string-listp-downcase-string-list
  (string-listp (downcase-string-list x)))

