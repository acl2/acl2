#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t);$ACL2s-Preamble$|#

#|           
Sat May 10  EDT 2014
Pete Manolios

A data definition for var, variables. Variables are symbols
comprised of uppercase letters and the digits 0-9. They have to
start with a letter and they cannot be NIL not T.

Vars can be used with defdata, e.g., the following

(defdata m (map var var))

is accepted by ACL2s, but this is not

(defdata m (map symbol symbol))

|#

(in-package "ACL2S")

(include-book "splitnat")
(include-book "switchnat")

(include-book "defdata-core")
(include-book "random-state")
(include-book "enumerators-gen")

(include-book "library-support")

(include-book "register-data-constructor")
(include-book "register-type")

(include-book "register-combinator")
(include-book "listof")

(include-book "tau-characterization")

(include-book "tools/rulesets" :dir :system)

; The characters we allow to in variable names.
(defdata var-char 
  (enum '(#\X #\Y #\L #\N #\Z #\I #\J #\K #\A #\B #\C 
          #\M #\D #\E #\F #\G #\H #\0 #\1  
          #\O #\P #\Q #\R #\S #\T #\U #\V #\W  
          #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))

; What to replace nil and t by
(defconst *non-nil-non-t-fix* '(#\X)) 

; The numeric characters
(defdata var-char-num 
  (enum '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))

; Var-chars are chars
(defthm char-var-char
  (implies (var-charp x)
           (characterp x))
  :rule-classes ((:compound-recognizer) (:forward-chaining)))

(defun non-nil-non-t-char-listp (l)
  (declare (xargs :guard t))
  (and (not (equal l '(#\N #\I #\L)))
       (not (equal l '(#\T)))))

(defun var-char-listp-aux (l)
  (declare (xargs :guard t))
  (if (consp l)
    (and (var-charp (car l))
         (var-char-listp-aux (cdr l)))
    (equal l nil)))

; A var-char-list is a non-empty var-char-listp-aux that does not correspond 
; to nil/t and whose first element is not a number
(defun var-char-listp (l)
  (declare (xargs :guard t))
  (and (consp l)
       (non-nil-non-t-char-listp l)
       (not (var-char-nump (car l)))
       (var-char-listp-aux l)))  

; var-char-listp(-aux) are char lists.
(defthm var-char-listp-aux-char-listp
  (implies (var-char-listp-aux l)
           (character-listp l))
  :rule-classes ((:forward-chaining)))

(defthm var-char-listp-char-listp
  (implies (var-char-listp l)
           (character-listp l))
  :rule-classes ((:forward-chaining)))

(encapsulate 
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))

  (verify-termination nth-var-char))

; generate a char-list-aux from a list of nats
(defun get-var-char-list-aux-from-positions (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
    nil
    (cons (nth-var-char (car l))
          (get-var-char-list-aux-from-positions (cdr l)))))

; fixing a var-char-list-aux so that it is a var-char-list
(defun fix-char-list (l)
  (declare (xargs :guard t))
  (cond ((atom l) '(#\X))
        ((var-char-nump (car l))
         (cons #\X l))
        (t l)))

; geneare a var-char-list from a list of nats
(defun get-var-char-list-from-positions (l)
  (declare (xargs :guard (nat-listp l)))
  (b* ((res (get-var-char-list-aux-from-positions l))
       (res1 (fix-char-list res))
       ((when (non-nil-non-t-char-listp res1)) res1))
      *non-nil-non-t-fix*))

#|
(local
(defthm var-charp-nth-var-char1
  (implies (integerp n)
           (var-charp (nth-var-char n)))
  :hints (("goal" :expand (nth-var-char n)))
  :rule-classes nil))

(local
(defthm var-charp-nth-var-char2
  (implies (not (integerp n))
           (equal (nth-var-char n) #\X))
  :hints (("goal" :expand (nth-var-char n)))
  :rule-classes nil))

(defthm var-charp-nth-var-char
  (var-charp (nth-var-char n))
  :hints (("goal" :use ((:instance var-charp-nth-var-char1)
                        (:instance var-charp-nth-var-char2))))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((nth-var-char n)))))

(defthm charp-nth-var-char
  (characterp (nth-var-char n))
  :rule-classes ((:type-prescription) 
                 (:forward-chaining :trigger-terms ((nth-var-char n)))))

(defthm var-char-listp-get-var-char-list-from-positions
  (implies (nat-listp l)
           (var-char-listp (get-var-char-list-from-positions l)))
  :hints (("goal" :in-theory (disable var-charp))))

(defthm char-listp-get-var-char-list-from-positions
  (implies (nat-listp l)
           (and (character-listp (get-var-char-list-from-positions l))
                (character-listp (get-var-char-list-aux-from-positions l))))
  :hints (("goal" :in-theory (disable var-charp))))
|#

; strings of up to length 6
(defun nth-var-string (n)
;  (declare (xargs :guard (natp n)))
  (b* ((str-len (1+ (mod n 5)))
       (char-pos-list (defdata::split-nat str-len n))
       (charlist (get-var-char-list-from-positions char-pos-list))
       (clist (fix-char-list charlist)))
      (coerce clist 'string)))

(defun nth-var (n)
;  (declare (xargs :guard (natp n)))
  (intern-in-package-of-symbol (nth-var-string n) 'acl2::acl2-pkg-witness))

(defun varp (x)
  (declare (xargs :guard t))
  (b* (((unless (symbolp x)) nil)
       ((when (keywordp x)) nil)
       ((unless (acl2::legal-variablep x)) nil)
       (name (symbol-name x))
       (clist (coerce name 'list)))
      (var-char-listp clist)))
        
(register-type var :predicate varp :enumerator nth-var) 

(defthm var-symbolp
  (implies (varp x)
           (symbolp x))
  :rule-classes ((:compound-recognizer) (:forward-chaining)))
