#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

;; [Jared] Marking this book as non-acl2(r) because it attempts to prove:
;;
;; (DEFTHM COMMON-LISP::COMPLEX-CONSTRUCTOR-DESTRUCTORS
;;          (IMPLIES (ACL2-NUMBERP X)
;;                   (AND (RATIONALP (REALPART X))
;;                        (RATIONALP (IMAGPART X))))
;;          :HINTS NIL
;;          :RULE-CLASSES NIL)
;;
;; which, I think, is not a theorem in ACL2(r).

; cert_param: (non-acl2r)

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
(include-book "alistof")
(include-book "tau-characterization")

(include-book "tools/rulesets" :dir :system)

(include-book "var-book")

;; (make-event ;TODO make sure to get this working
;;  (er-progn
;;   (defdata::set-acl2s-defdata-verbose t)
;;   (value '(value-triple :invisible)))
;;  :check-expansion t)

(defun allp (x)
  (declare (xargs :mode :logic
                  :guard t)
           (ignore x))
  t)

;; (defthm allp-is-tau-predicate
;;   (booleanp (allp x))
;;   :rule-classes :tau-system)

;; (defthm allp-is-t
;;   (equal (allp x) t)
;;   :rule-classes (:rewrite))

(in-theory (disable allp))

; 18 Aug 2014.
; ALLP aliases TAU explicitly disallows predicates that hide equality to a
; constant. In particular it does not like the everywhere-true and
; everywhere-false predicates. So we built special support for these. We will
; store all aliases of allp in a table. This will be used by subtype-p and
; disjoint-p functions. Recall that we have given up homebrew datatype
; relationship graphs in favor of its implicit coding in TAU-DATABASE.
(table allp-aliases nil)
(table allp-aliases 'allp 'all :put) ;all will be registered as a defdata type below.




;; NOTE: ALL should not be used in subtype/disjoint relations
;; because of a caveat in tau

;;type constructors == product types
;;rational number constructor
;;pair constructor
(register-data-constructor (consp cons)
                           ((allp car) (allp cdr))
                           :rule-classes nil
                           :verbose t)
                

;;jared's oset implementation
;; (defun set::non-empty-setp (x)
;;   (declare (xargs :guard t))
;;   (and (set::setp x)
;;        (not (set::empty x))))

;; (register-data-constructor (SET::non-empty-setp SET::insert)
;;                            ((allp SET::head) (set::setp SET::tail))
;;                            :proper nil)


;;symbols
(register-data-constructor (symbolp intern$)
                           ((stringp symbol-name) (stringp symbol-package-name))
                           :rule-classes nil
                           :proper nil) ;package name destructor fails



(register-data-constructor (rationalp /)
                           ((integerp numerator) (posp denominator))
                           :rule-classes nil
                           :proper nil)


 

;;complex number type
(register-data-constructor (acl2-numberp complex)
                           ((rationalp realpart) (rationalp imagpart))
                           :rule-classes nil
                           )


#||
;;natural numbers
(defexec succ (x)
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (if (natp x)
         (1+ x)
         1)
       :exec (1+ x)))

(defun pred (x)
  (declare (xargs :guard (natp x)))
  (if (zp x)
    0
    (1- x)))

(defthm succ-pred
  (implies (posp x)
           (equal (succ (pred x)) x)))

(register-data-constructor (posp succ)
                           (pred))
||#


;;characters

(defconst *character-values* *standard-chars*)

(defconst *len-character-values* (len *character-values*))

(defconst *alpha-chars*
  '(#\A #\B #\C #\D #\E #\F #\G
    #\H #\I #\J #\K #\L #\M #\N #\O #\P #\Q
    #\R #\S #\T #\U #\V #\W #\X #\Y #\Z
    #\a #\b #\c
    #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m
    #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w
    #\x #\y #\z     ))

(defconst *len-alpha-chars* (len *alpha-chars*))

(defconst *alpha-low-chars*
  '(#\a #\b #\c
    #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m
    #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w
    #\x #\y #\z 
    ))

(defconst *len-alpha-low-chars* (len *alpha-low-chars*))

(defconst *alpha-up-chars*
  '(#\A #\B #\C #\D #\E #\F #\G
    #\H #\I #\J #\K #\L #\M #\N #\O #\P #\Q
    #\R #\S #\T #\U #\V #\W #\X #\Y #\Z
    ))

(defconst *len-alpha-up-chars* (len *alpha-up-chars*))

(defconst *alpha-num-chars*
  '(#\A #\B #\C #\D #\E #\F #\G
    #\H #\I #\J #\K #\L #\M #\N #\O #\P #\Q
    #\R #\S #\T #\U #\V #\W #\X #\Y #\Z
    #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
    #\a #\b #\c
    #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m
    #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w
    #\x #\y #\z
    ))

(defconst *len-alpha-num-chars* (len *alpha-num-chars*))


(defthm integerp-mod
    (implies (and (integerp m)
                  (integerp n))
	     (integerp (mod m n)))
  :rule-classes (:rewrite :type-prescription))

(encapsulate 
 nil
 (local (include-book "arithmetic-5/top" :dir :system))
 
 (defthm mod-nonnegative-integer-args
   (implies (and (integerp x)
                 (integerp y)
                 (< 0 y))
            (<= 0 (mod x y)))
   :rule-classes ((:rewrite :backchain-limit-lst 1)
                  (:type-prescription)))
 

(defun get-character-list-from-positions (l)
  (declare (xargs :guard (nat-listp l)))
                  ;:verify-guards nil))
  (if (endp l)
    nil
    (let* ((pos (mod (car l) (len *alpha-num-chars*)))
           (char (nth pos *alpha-num-chars*)))
      (cons char (get-character-list-from-positions (cdr l))))))

(defun get-standard-char-list-from-positions (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
    nil
    (let* ((pos (mod (car l) (len *standard-chars*)))
           (char (nth pos *standard-chars*)))
      (cons char (get-standard-char-list-from-positions (cdr l))))))

(defthm get-character-list-from-positions--character-listp
  (implies (nat-listp l)
           (and (character-listp (get-character-list-from-positions l))
                (character-listp (get-standard-char-list-from-positions l))))
  :hints (("goal" :in-theory (enable standard-char-listp))))

)
(in-theory (disable mod))
;;booleans

(defconst *boolean-values* '(t nil))
(defun nth-boolean (n) (nth (mod n 2) *boolean-values*))
;(define-enumeration-type boolean '(t nil))



;-------- define some enumerators --------;

(defun nth-nat (n)
  (declare (xargs :guard (natp n)))
  n)

(defun nat-index (n)
  (declare (xargs :guard (natp n)))
  n)

(defthm nth-nat-index
  (equal (nat-index (nth-nat n))
         n))

(defthm nat-index-nth
  (equal (nth-nat (nat-index n))
         n))


(defexec nth-pos (n)
  (declare (xargs :guard (natp n)))
  (mbe :logic
       (if (natp n)
         (1+ n)
         n)
       :exec (1+ n)))

(defthm nth-pos-is-posp
  (implies (natp x)
           (posp (nth-pos x)))
  :hints (("goal" :in-theory (enable nth-pos)))
  :rule-classes (:rewrite :type-prescription))

(defexec pos-index (i)
  (declare (xargs :guard (posp i)))
  (mbe :logic
       (if (posp i)
         (1- i)
         i)
       :exec (1- i)))

(defthm nth-pos-index
  (equal (pos-index (nth-pos n))
         n))

(defthm pos-index-nth
  (implies (and (integerp i)
                (>= i 1))
           (equal (nth-pos (pos-index i))
                  i)))


(defun pos-multiple-of-threep (v)
  (if (posp v)
    (equal 0 (mod v 3))
    nil)) 
(defun nth-pos-multiple-of-three (n)
 (if (natp n) 
   (* 3 (1+ n))
   3))

(defun pos-multiple-of-three-index (i)
  (if (pos-multiple-of-threep i)
         (1- (floor i 3))
         i))

;;integers
(defun nth-integer (n)
  (declare (xargs :guard (natp n)))
  (let* (;(n (mod n 1000))
         (mag (floor n 2))
        (sign (rem n 2)))
    (if (= sign 0)
      mag
      (- -1 mag))))

(defun nth-integer-between (n lo hi)
  (declare (xargs :guard (and (natp n)
                              (integerp lo)
                              (integerp hi))))
  (let ((range (nfix (- hi lo))))
    (+ lo (mod n (1+ range)))))

(defun integer-index (i)
  (declare (xargs :guard (integerp i)))
  (if (< i 0)
    (1+ (* (- (1+ i)) 2))
    (* i 2)))
#||
(encapsulate nil
  (local 
   (include-book "arithmetic-5/top" :dir :system))

  (defthm nth-pos-multiple-three-type
    (pos-multiple-of-threep (nth-pos-multiple-of-three n)))
  
  
  (defthm nth-pos-multiple-of-three-index
    (implies (natp n)
             (equal (pos-multiple-of-three-index (nth-pos-multiple-of-three n))
                    n)))
  
  (defthm pos-multiple-of-three-index-nth
    (implies (pos-multiple-of-threep i)
             (equal (nth-pos-multiple-of-three (pos-multiple-of-three-index i))
                    i)))    

  
  (defthm nth-integer-index
    (implies 
     (and (integerp n)
          (>= n 0))
     (equal (integer-index (nth-integer n))
            n)))
  (defthm integer-index-nth
    (implies 
     (integerp i)
     (equal (nth-integer (integer-index i))
            i))))
||#

;;only strings upto len 1 to 8
(defun nth-string (n)
  (declare (xargs :guard (natp n)))
                  ;:verify-guards nil))
  (let* ((str-len (1+ (mod n 7)))
         (char-pos-list (defdata::split-nat str-len n))
         (charlist (get-character-list-from-positions char-pos-list)))
    (coerce charlist 'string)))

(defun standard-stringp (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (standard-char-listp (coerce x 'list))))

(defun nth-standard-string (n)
  (declare (xargs :guard (natp n)))
                  ;:verify-guards nil))
  (let* ((str-len (1+ (mod n 7)))
         (char-pos-list (defdata::split-nat str-len n))
         (charlist (get-standard-char-list-from-positions char-pos-list)))
    (coerce charlist 'string)))

(encapsulate 
 ((nth-symbol (n) t :guard (natp n)))
 (local (defun nth-symbol (n)
          (declare (xargs :guard (natp n)))
          (declare (ignore n))
          'a)))

(defun nth-symbol-builtin (n)
  (declare (xargs :guard (natp n)))
                 ;:verify-guards nil)) 
  (intern$ (nth-string n) "ACL2"))

(defattach nth-symbol nth-symbol-builtin)

(encapsulate 
 ((nth-character (n) t :guard (natp n)))
 (local (defun nth-character (n)
          (declare (xargs :guard (natp n)))
          (declare (ignore n))
          '#\A)))

(defun nth-character-builtin (n)
  (declare (xargs :guard (natp n)))
  (nth (mod n *len-character-values*) *character-values*))

(defattach nth-character nth-character-builtin)

(defun nth-alpha-num-character (n)
  (declare (xargs :guard (natp n)))
  (nth (mod n *len-alpha-num-chars*) *alpha-num-chars*))


(defun positive-ratiop (x)
  (declare (xargs :guard t))
  (and (rationalp x)
       (not (integerp x))
       (> x 0)
       ))

(defun nth-positive-ratio (n)
  (declare (xargs :guard (natp n)))
  (mbe :logic (if (natp n)
                 (let* ((two-n-list (defdata::split-nat 2 n))
                        (alpha  (car two-n-list))
                        (beta (cadr two-n-list))
                        (den (+ 2 alpha))
                        (num (+ (floor beta den) beta)))
                   (/ num den))
                 (/ 1 2))
       :exec (let* ((two-n-list (defdata::split-nat 2 n))
                    (alpha  (car two-n-list))
                    (beta (cadr two-n-list))
                    (den (+ 2 alpha))
                    (num (+ (floor beta den) beta)))
               (/ num den))))



(defun negative-ratiop (x)
  (declare (xargs :guard t))
  (and (rationalp x)
       (not (integerp x))
       (< x 0)
       ))


(defun nth-negative-ratio (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (alpha  (car two-n-list))
         (beta (cadr two-n-list))
         (den (+ 2 alpha))
         (num (+ (floor beta den) beta)))
    (- 0 (/ num den))))


;(defdata rat (oneof 0 positive-ratio negative-ratio))
;DOESNT WORK so positive/negative ratio are not consistent types ;TODO
;(local (include-book "arithmetic-5/top" :dir :system))
;(thm (nat-listp (defdata::split-nat 2 n)))
;(thm (positive-ratiop (nth-positive-ratio n)))


(defun negp (x)
  (declare (xargs :guard t))
  (and (integerp x) 
       (< x 0)
       ))
(defun nth-neg (n)
  (declare (xargs :guard (natp n)))
  (- -1 n))
 
#|
(defdata int (oneof 0 pos neg))
(thm (iff (integerp x) (intp x)))
|#

(defun nth-positive-rational (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-pos (car two-n-list)))
         (den (nth-pos (cadr two-n-list))))
    (/ num den)))

(defun nth-negative-rational (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-neg (car two-n-list)))
         (den (nth-pos (cadr two-n-list))))
    (/ num den)))
(defun positive-rationalp (x)
  (declare (xargs :guard t))
  (and (rationalp x) 
       (> x 0)
       ))
(defun negative-rationalp (x)
  (declare (xargs :guard t))
  (and (rationalp x) 
       (< x 0)
       ))

;(defdata rational (oneof 0 positive-rational negative-rational))
(defun nth-rational (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-integer (car two-n-list)))
         (den (nth-pos (cadr two-n-list))))
    (/ num den)))



(defthm nth-rat-is-ratp
  (implies (natp x)
           (rationalp (nth-rational x)))
  :rule-classes (:rewrite :type-prescription))

 ;lo included, hi included
    
  
(defun nth-rational-between (n lo hi);inclusive
  (declare (xargs :guard (and (natp n)
                              (rationalp lo)
                              (rationalp hi))))

  (let* ((two-n-list (defdata::split-nat 2 n))
         (den (nth-pos (car two-n-list)))
         (num (nth-integer-between (cadr two-n-list) 0 (1+ den)))
         (range (- hi lo)))
    (+ lo (* (/ num den) range))))       


(defun nth-complex-rational (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (rpart (nth-rational (defdata::nfixg (car two-n-list))))
         (ipart (nth-rational (defdata::nfixg (cadr two-n-list)))))
    (complex rpart ipart)))

(encapsulate 
 ((nth-acl2-number (n) t :guard (natp n)))
 (local (defun nth-acl2-number (n)
          (declare (xargs :guard (natp n)))
          (declare (ignore n))
          0)))

(defun nth-acl2-number-builtin (n)
  (declare (xargs :guard (natp n)))
  (b* (((mv choice seed)
        (defdata::switch-nat 4 n)))
    (case choice
          (0 (nth-nat seed))
          (1 (nth-integer seed))
          (2 (nth-rational seed))
          (t (nth-complex-rational seed)))))

(defattach nth-acl2-number nth-acl2-number-builtin)

;(defdata character-list (listof character))
;;only strings upto len 1 to 8
(defun nth-character-list (n)
  (declare (xargs :guard (natp n)))
                  ;:verify-guards nil))
  (let* ((str-len (1+ (mod n 7)))
         (char-pos-list (defdata::split-nat str-len n))
         (charlist (get-character-list-from-positions char-pos-list)))
    charlist))

(defun nth-standard-char-list (n)
  (declare (xargs :guard (natp n)))
                  ;:verify-guards nil))
  (let* ((str-len (1+ (mod n 7)))
         (char-pos-list (defdata::split-nat str-len n))
         (charlist (get-standard-char-list-from-positions char-pos-list)))
    charlist))

#||
(defconst *base-types* '((BOOLEAN 2 *BOOLEAN-VALUES* . BOOLEANP)
                         (CHARACTER-LIST T NTH-CHARACTER-LIST . CHARACTER-LISTP)
                         (SYMBOL T NTH-SYMBOL . SYMBOLP)
                         (STRING T NTH-STRING . STRINGP)
                         (CHARACTER 62 *CHARACTER-VALUES* . CHARACTERP)
                         (ACL2-NUMBER T NTH-ACL2-NUMBER . ACL2-NUMBERP)
                         (COMPLEX-RATIONAL T NTH-COMPLEX-RATIONAL . COMPLEX-RATIONALP)
                         (RATIONAL T NTH-RATIONAL . RATIONALP)
                         (POS T NTH-POS . POSP)
                         (NAT T NTH-NAT . NATP)
                         (INTEGER T NTH-INTEGER . INTEGERP)))
(defun nth-all (n)
  (declare (xargs :guard (natp n))
                  :verify-guards nil)
  (let* ((num-types (len *base-types*))
         (two-n-list (defdata::split-nat 2 n))
         (choice (mod (car two-n-list) num-types))
         (seed (cadr two-n-list))
         (type-info (cdr (nth choice *base-types*)))
         (type-size (car type-info))
         (type-enum (cadr type-info)))
    (if (eq type-size 't) ;inf
      `(,type-enum ,seed)
      `(nth ,(mod seed type-size) ,type-enum))))||#


(defconst *number-testing-limit* 1000)

;ADDED restricted testing enumerators for all number types
(defun nth-nat-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-nat n-small)))
(defun nth-pos-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-pos n-small)))
(defun nth-neg-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-neg n-small)))

(defun nth-integer-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-integer n-small)))

(defun nth-positive-ratio-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-positive-ratio n-small)))
(defun nth-negative-ratio-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-negative-ratio n-small)))
(defun nth-rational-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-rational n-small)))
(defun nth-positive-rational-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-positive-rational n-small)))
(defun nth-negative-rational-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-negative-rational n-small)))
(defun nth-acl2-number-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-acl2-number n-small)))
(defun nth-complex-rational-testing (n)
  (declare (xargs :guard (natp n)))
  (let ((n-small (mod n *number-testing-limit*)))
    (nth-complex-rational n-small)))


;; (defun atomp (v)
;;   (declare (xargs :guard t))
;;   (atom v))

(defun nth-atom (n)
  (declare (xargs :guard (natp n)))
  (b* (((mv choice seed) 
        (defdata::weighted-switch-nat 
          '(1  ;nil
            1  ;t
            3  ;nat
            1  ;sym
            1  ;string
            2  ;char
            2  ;acl2-num
            10 ;rational
            10 ;pos
            20 ;0
            30 ;integer
            ) n)))
        
    (case choice
          (0 'nil)
          (1 't)
          (2 (nth-nat-testing seed));smaller numbers
          (3 (nth-symbol seed))
          (4 (nth-string seed))
          (5 (nth-alpha-num-character seed)) ;(nth-character seed))
          (6 (nth-acl2-number seed))
          (7 (nth-rational seed))
          (8 (nth-pos-testing seed))
          (9 0)
          (t (nth-integer-testing seed)))))

;(defdata atom (oneof acl2-number character symbol string))


;atoms

; register-type ought to also test if not prove the following:
; TODO:Note it does not prove that type is sound neither that is is complete
; By Type Soundness i mean (thm (implies (natp n) (Tp (nth-T n)))
; By Type Completeness i mean (thm (implies (Tp x)
;                                          (equal x (nth-T (T-index x)))) 
;                                   where (nth-T (T-index x)) = x

(defmacro register-custom-type  (typename typesize enum pred &key verbose)
  `(defdata::register-type ,typename :size ,typesize :predicate ,pred :enumerator ,enum :verbose ,verbose))

(register-custom-type nat t nth-nat natp)

(register-custom-type pos t nth-pos posp)

(register-custom-type neg t nth-neg negp )
(register-custom-type integer t nth-integer integerp )
(register-custom-type positive-ratio t nth-positive-ratio  positive-ratiop)
(register-custom-type negative-ratio t nth-negative-ratio  negative-ratiop )
(register-custom-type positive-rational t nth-positive-rational  positive-rationalp )
(register-custom-type negative-rational t nth-negative-rational  negative-rationalp )
(register-custom-type rational t nth-rational  rationalp )
(register-custom-type complex-rational t nth-complex-rational  complex-rationalp )
(register-custom-type acl2-number t nth-acl2-number  acl2-numberp )
(register-custom-type boolean 2 nth-boolean  booleanp );taken care of by define-enumeration-type
(register-custom-type symbol t nth-symbol  symbolp)

(verify-termination acl2::legal-constantp)
(verify-guards acl2::legal-constantp)
(defun proper-symbolp (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (or (keywordp x);a keyword
                (booleanp x);t or nil
                (acl2::legal-constantp x)))))

(in-theory (disable acl2::legal-constantp))

(defconst *nice-symbol-names*
  '(x y z a b c i j k p q r s u v w l d e f g h m n))

(defun nth-proper-symbol (n)
  (declare (xargs :guard (natp n)))
  (let ((psym (nth-symbol n)))
    (if (proper-symbolp psym)
        psym
      (nth (mod n (len *nice-symbol-names*)) *nice-symbol-names*))))

(register-custom-type proper-symbol t nth-proper-symbol proper-symbolp)

(defun nth-character-uniform (m seed)
    (declare (ignorable m))
     (declare (type (unsigned-byte 31) seed))
     (declare (xargs :guard (and (natp m)
                                 (unsigned-byte-p 31 seed))))
     (mv-let (n seed)
             (defdata::random-natural-seed seed)
             (mv (nth-character n) (the (unsigned-byte 31) seed))))
   
(defdata::register-type character :size 62 :enumerator nth-character :predicate characterp :enum/acc nth-character-uniform)




;(define-enumeration-type standard-char *standard-chars*)
(defun nth-standard-char (n)
  (declare (xargs :guard (natp n)))
  (nth (mod n 96) *standard-chars*))
(register-custom-type standard-char 96 nth-standard-char standard-char-p)
(register-custom-type string t nth-string stringp)
(register-custom-type standard-string t nth-standard-string standard-stringp)
(register-custom-type atom t nth-atom atom);instead of atomp Exception

;added the above atom primitive types in the data-type graph using register-custom-type

;custom type
(defconst *z-values* '(0 -1 "a" 1/3 :a)) ;for zp
(defun nth-z (n)
  (declare (xargs :guard (natp n)))
  (nth (mod n 5) *z-values*))
(defun nth-z-uniform (m seed)
    (declare (ignorable m))
     (declare (type (unsigned-byte 31) seed))
     (declare (xargs :guard (and (natp m)
                                 (unsigned-byte-p 31 seed))))
     (mv-let (n seed)
             (defdata::random-natural-seed seed)
             (mv (nth-z n) (the (unsigned-byte 31) seed))))
(defdata::register-type z :size t :enumerator nth-z :predicate zp :enum/acc nth-z-uniform)


;Subtype relations betweem the above
;pos is a subtype of nat (Note the direction)
(defdata-subtype pos nat)

;nat is a subtype of integer
(defdata-subtype nat integer)
(defdata-subtype neg integer)
(defdata-subtype integer rational)
(defdata-subtype positive-ratio rational)
(defdata-subtype positive-rational rational) ;Aug 18 2011
(defdata-subtype negative-ratio rational)
(defdata-subtype negative-rational rational) ;Aug 18 2011
(defdata-subtype complex-rational acl2-number)
(defdata-subtype rational acl2-number)
(defdata-subtype acl2-number atom)
(defdata-subtype boolean symbol)
(defdata-subtype proper-symbol symbol)

(defdata-subtype standard-char character :hints (("Goal" :in-theory (enable standard-char-p))))
(defdata-subtype character atom)
(defdata-subtype string atom)
(defdata-subtype symbol atom)

(defdata ratio (oneof positive-ratio negative-ratio)) 


(defdata-subtype ratio rational) 

;added 26th Sep '13
(defdata-subtype neg negative-rational)
(defdata-subtype pos positive-rational) 
(defdata-subtype negative-rational z)
(defdata-subtype ratio z)
(defdata-subtype complex-rational z)
(defdata-subtype symbol z)
(defdata-subtype character z)
(defdata-subtype string z)
(defdata-disjoint pos z)

(defdata-subtype standard-string string)


;Disjoint relations between the above types
(defdata-disjoint acl2-number character)
(defdata-disjoint acl2-number symbol)
(defdata-disjoint character string)
(defdata-disjoint character symbol)
(defdata-disjoint string symbol)
(defdata-disjoint boolean proper-symbol)

;lists of atoms
(defthm termination-tree-enum-cdr
  (implies (consp x)
           (and (< (acl2-count (cdr x))
                   (acl2-count x))
                (< (acl2-count (car x))
                   (acl2-count x)))))
(defthm termination-tree-enum-dec
  (implies (< (acl2-count x1) (acl2-count x2))
           (and (< (acl2-count (car x1)) (acl2-count x2))
                (< (acl2-count (cdr x1)) (acl2-count x2)))))
(defthm terminination-tree-enum-nth
  (<= (acl2-count (nth i x))
              (acl2-count x))
  :rule-classes (:rewrite :linear))

(defthm termination-tree-enum-dec2
  (implies (< (acl2-count x1) (acl2-count x2))
           (< (acl2-count (nth i x1)) (acl2-count x2)))
  :hints (("Goal" :in-theory (disable nth))))



; IMPORTANT: PROPER-CONS is put ahead of all lists, so that in the
; event of intersecting it with lists, the lists are given preference,
; by the virtue of appearing earlier in the reverse chronological
; order of type-metadata table. Lists of various types are certainly
; more amenable to Cgen/Enumeration than proper-conses.

;; (defdata list-a (list atom))
;; (defdata list-aa (list atom atom))
;; (defdata list-aaa (list atom atom atom))

;cons
(defdata cons-atom (cons atom atom))

(defdata-disjoint cons-atom atom)


(defdata cons-ca-ca (cons cons-atom cons-atom))         
(defdata cons-cca-cca (cons cons-ca-ca cons-ca-ca) )

;; (defdata list-a-ca (list atom cons-atom) )
;; (defdata list-aa-ca (list atom atom atom cons-atom) )
;; (defdata list-aa-cca (list atom atom cons-ca-ca) )
;; (defdata list-aaaa-cccca (list cons-atom cons-cca-cca) )
;; (defdata list-ca-cca (list cons-atom cons-ca-ca) )
;; (defdata list-la-la (list list-aa list-aa) )


;MAJOR CHANGE June 6th 2010, now we have no guards in any enumerators
(defun nth-proper-cons (n)
;  (declare (xargs :guard (natp n)))
  (declare (xargs :mode :program))
  (b* (((mv choice seed)
        (defdata::weighted-switch-nat 
          '(
            1  ;list-a
            1  ;list-aa
            1  ;list-aaa
            1  ;list-a-ca
            1  ;list-aa-ca 
            1  ;list-aa-cca
            1  ;list-aaaa-cccca
            1  ;list-ca-cca
            1  ;list-ca-cccca
            ) n)))

       

    (case choice
      (0 (list (nth-atom seed)))
      (1 (b* (((list i1 i2) (defdata::split-nat 2 seed))) (list (nth-atom i1) (nth-atom i2))))
      (2 (b* (((list i1 i2 i3) (defdata::split-nat 3 seed))) (list (nth-atom i1) (nth-atom i2) (nth-atom i3))))
      (3 (b* (((list i1 i2 i3) (defdata::split-nat 3 seed))) (list (nth-atom i1) (cons (nth-atom i2) (nth-atom i3))))) ;(nth-list-a-ca seed))
      (4 (b* (((list i1 i2 i3 i4 i5) (defdata::split-nat 5 seed)))
           (list (nth-atom i1) (nth-atom i2) (nth-atom i3) (cons (nth-atom i4) (nth-atom i5))))) ;(nth-list-aa-ca  seed))
      (5 (b* (((list i1 i2 i3 i4 i5 i6) (defdata::split-nat 6 seed)))
           (list (nth-atom i1) (nth-atom i2) (cons (cons (nth-atom i3) (nth-atom i4)) 
                                                   (cons (nth-atom i5) (nth-atom i6)))))) ;(list-aa-cca seed))
      (6 (b* (((list i1 i2 i3 i4 i5) (defdata::split-nat 5 seed)));(list-aaaa-cccca seed)) 
           (list (nth-cons-atom i1) (cons (cons (nth-cons-atom i2) (nth-cons-atom i3)) 
                                          (cons (nth-cons-atom i4) (nth-cons-atom i5)))))) 
      (7 (b* (((list i1 i2 i3 i4 i5) (defdata::split-nat 5 seed)))  ;(list-ca-cca seed))
           (list (nth-cons-atom i1) (cons (cons (nth-atom i2) (nth-atom i3)) 
                                          (cons (nth-atom i4) (nth-atom i5))))))
      (8 (b* (((list i1 i2 i3 i4 i5) (defdata::split-nat 5 seed)))
           (list (nth-atom i1) (nth-atom i2) (nth-atom i3) (nth-atom i4) (nth-atom i5))))
      (t '(1  2)))))

(register-custom-type proper-cons t nth-proper-cons  proper-consp)




(defdata nat-list (listof nat))

;; (verify-termination pos-listp) ; pos-listp is in program mode, so we need this.
;; (verify-guards pos-listp)

(defdata    pos-list (listof pos))

(defdata    integer-list (listof integer) )
(defdata    rational-list (listof rational) )
(defdata    complex-rational-list (listof complex-rational) )

(defdata acl2-number-list (listof acl2-number) )
(defdata boolean-list (listof boolean) )
(defdata symbol-list    (listof symbol) )
(defdata::register-type character-list 
               :size t 
               :predicate character-listp
               :enumerator nth-character-list  
               :prettyified-def (listof character))
               
(defdata::register-type standard-char-list 
               :size t 
               :predicate  standard-char-listp
               :enumerator nth-standard-char-list 
               :prettyified-def (listof standard-char))

; TAU characterization of standard-char-list (copied and string/replaced from def=>String-list)
(defthm
  def=>standard-char-list
  (and (implies (and (equal v1 'nil))
                (standard-char-listp v1))
       (implies (and (standard-char-p v11)
                     (standard-char-listp v12))
                (standard-char-listp (cons v11 v12))))
  :hints (("goal" :in-theory (e/d (standard-char-listp) (standard-char-p))))
  :rule-classes (:tau-system :rewrite))
(defthm
  standard-char-list=>def
  (and (implies (and (standard-char-listp v1)
                     (endp v1))
                (equal v1 'nil))
       (implies
        (and (standard-char-listp v1)
             (consp v1))
        (and (standard-char-p (car v1))
             (standard-char-listp (cdr v1)))))
  :hints (("goal" :in-theory (e/d (standard-char-listp) (standard-char-p))))
:rule-classes (:tau-system (:forward-chaining :trigger-terms ((standard-char-listp v1)))))


(defdata string-list (listof string))
(defdata atom-list (listof atom))
(defdata-subtype pos-list nat-list)
(defdata-subtype nat-list integer-list)
(defdata-subtype integer-list rational-list)
(defdata-subtype complex-rational-list acl2-number-list)
(defdata-subtype rational-list acl2-number-list )
(defdata-subtype acl2-number-list atom-list)
(defdata-subtype boolean-list symbol-list)
(defdata-subtype standard-char-list character-list)
(defdata-subtype character-list atom-list)
(defdata-subtype string-list atom-list)

(defdata-subtype symbol-list atom-list)



;TODO.NOTE: Note that all the enumerators defined below are purely heuristic and 
;are not consistent/complete with their respective predicates.


;; (verify-guards NTH-NAT-LIST) 
;; (verify-guards NTH-RATIONAL-LIST)
;; (verify-guards NTH-SYMBOL-LIST)
;; (verify-guards  NTH-CONS-ATOM)
;; (verify-guards NTH-CONS-CA-CA)
;; (verify-guards  NTH-STRING-LIST)
;; (verify-guards NTH-ATOM-LIST)

(defun nth-all (n)
  (declare (xargs :mode :program))
  (declare (xargs :guard (natp n)))
 
           
                  ;;:verify-guards nil))
  (b* (((mv choice seed)
        (defdata::weighted-switch-nat 
          '(1  ;nil
            1  ;0
            1 ;t
            1 ;integer
            1 ;rational
            1  ;nat-list
            1  ;sym
            1  ;string
            2  ;char
            1  ;acl2-num
            1  ;bool
            5 ;nat
            5 ;pos
            5  ;rational-list
            2  ;sym-list
            20 ;cons-atom
            5  ;charlist
            10  ;cons-cons-atom
            1  ;stringlist
            10  ;atom-list
            ) n)))
      
    (case choice
          (0 'nil)
          (1 0)
          (2 't)
          (3 (nth-integer-testing seed))
          (4 (nth-rational seed))
          (5 (nth-nat-list seed))
          (6 (nth-symbol seed))
          (7 (nth-string seed))
          (8 (nth-alpha-num-character seed)) ;(nth-character seed))
          (9 (nth-acl2-number seed))
          (10 (nth (mod seed 2) *boolean-values*))
          (11 (nth-nat-testing seed))
          (12 (nth-pos-testing seed))
          (13 (nth-rational-list seed))
          (14 (nth-symbol-list seed))
          (15 (nth-cons-atom seed))
          (16 (nth-character-list seed))
          (17 (b* (((list i1 i2) (defdata::split-nat 2 seed))) 
                (cons (nth-cons-atom i1) (nth-cons-atom i2)))) ;(cons-ca-ca seed))
          (18 (nth-string-list seed))
          (19 (nth-atom-list seed))
          (t 'nil)))) ;this case should not come up


(register-custom-type all t nth-all  allp)


;We will also name a special type, the empty type, which has no elements in its typeset.
(defconst *empty-values* '())
(defun nth-empty (x)
  (declare (ignore x) (xargs :guard (natp x)))
  (er hard? 'nth-empty "~| Empty enumerator~%"))
;TODO - if type is already registered, then we should be able to pick the predicate
;from the table instead of syntactically from the type.
(defun emptyp (x)
  (declare (ignore x) (xargs :guard t))
  nil)

(defthm emptyp-is-tau-predicate 
    (booleanp (emptyp x))
  :rule-classes :tau-system)

(register-custom-type empty 0 nth-empty emptyp)
;NOTE: empty is a special type, so we treat it specially and seperately, rather than the
;usual way of going through the data type graph, and it might lead to inconsistency
;with the ACL2 axioms about datatypes.

(defdata cons (cons all all))


;Alist/acons theory
(defdata acons (cons (cons all all) all))

;;associated key-value pairs
;; (defun aconsp (x)
;;   (declare (xargs :guard t))
;;   (and (consp x) (consp (car x))))
(defun acons-caar (x) (declare (xargs :guard (aconsp x))) (caar x))
(defun acons-cdar (x) (declare (xargs :guard (aconsp x))) (cdar x))
(defun acons-cdr (x) (declare (xargs :guard (aconsp x))) (cdr x))

(defthm acons-acl2-count-lemma
  (equal (acl2-count (acons x1 x2 x3))
         (+ 2 (acl2-count x1) (acl2-count x2) (acl2-count x3))))

(in-theory (enable aconsp))
(register-data-constructor (aconsp acons)
                           ((allp acons-caar) (allp acons-cdar) (allp acons-cdr))
                           :rule-classes (:rewrite)
                           :verbose t)

(defthm acons-alist-lemma
  (implies (alistp x)
           (alistp (acons x1 x2 x)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))
  
; (in-theory (disable acons aconsp acons-caar acons-cdar acons-cdr)) TODO --
; Whats the point of acons as a constructor if these functions are not disabled
; -- Ohh well, lets ride on cons for now. [2014-09-24 Wed]




(defdata list (oneof cons nil))

(DEFUNS (NTH-TRUE-LIST
               (X)
               (declare (xargs :mode :program))
               (DECLARE (XARGS :guard (natp x) :verify-guards nil
                               :MEASURE (NFIX X)))
               (IF (OR (NOT (INTEGERP X)) (< X 1))
                   'NIL
                   (LET ((X (- X 1)))
                        (LET ((INFXLST (DEFDATA::SPLIT-NAT 2 X)))
                             (CONS (LET ((X (NTH 0 INFXLST))) (NTH-ALL X))
                                   (LET ((X (NTH 1 INFXLST)))
                                        (NTH-TRUE-LIST X))))))))

(defdata::register-type true-list 
               :size t 
               :predicate true-listp
               :enumerator nth-true-list 
               :prettyified-def (listof all))

;some alists

(defdata alist (listof (cons all all)))
(defdata symbol-alist (alistof symbol all))
(verify-termination character-alistp)
(defdata character-alist (alistof character all))
(defdata r-symbol-alist (alistof all symbol))
(defdata-subtype symbol-alist alist)
(defdata-subtype character-alist alist)
(defdata-subtype r-symbol-alist alist)

;TODO standard-string-alist has very poor theory support!!
;(defdata standard-string-list (listof standard-string))
;(defdata-subtype standard-string-list string-list)
;(defdata standard-string-alist (alistof standard-string all)) 
;(defdata-subtype standard-string-alist alist)

;(verify-guards nth-true-list)
(defdata true-list-list (listof true-list))
(defdata-subtype true-list-list true-list)



;added 26th Sep '13
(defdata-subtype cons z)
(defdata-subtype list z)


(defun all-but-zero-nil-tp (x)
  (declare (xargs :guard t))
  (and (not (equal x 0))
       (not (equal x 't))
       (not (equal x 'nil))))
            
(defun nth-all-but-zero-nil-t (n)
  (declare (xargs :mode :program))
  (declare (xargs :guard (natp n)))

  (b* (((mv choice seed)
          (defdata::weighted-switch-nat 
            '(1 ;integer
              1  ;charlist
              1  ;sym
              1  ;string
              2  ;char
              1  ;pos
              5 ;positive-ratio
              5 ;negative-ratio
              5 ;complex-rational
              5  ;rational-list
              2  ;sym-list
              20 ;cons-atom
              5  ;nat-list
              10  ;cons-cons-atom
              1  ;stringlist
              10  ;atom-list
              ) n)))
    
    (case choice
          (0 (nth-integer-testing seed))
          (1 (nth-character-list seed))
          (2 (nth-symbol seed))
          (3 (nth-string seed))
          (4 (nth-character seed))
          (5 (nth-pos-testing seed))
          (6 (nth-positive-ratio seed))
          (7 (nth-negative-ratio seed))
          (8 (nth-complex-rational seed))
          (9 (nth-rational-list seed))
          (10 (nth-symbol-list seed))
          (11 (nth-cons-atom seed))
          (12 (nth-nat-list seed))
          (13 (b* (((list i1 i2) (defdata::split-nat 2 seed))) 
                (cons (nth-cons-atom i1) (nth-cons-atom i2)))) ;(cons-ca-ca seed))
          (14 (nth-string-list seed))
          (15 (nth-atom-list seed))
          (t 1))))

(register-custom-type all-but-zero-nil-t t nth-all-but-zero-nil-t  all-but-zero-nil-tp)

            
(defun nth-wf-key (n) ;;since nth-all-but-zero-nil-t has strings of length less than 8, it cannot include the ill-formed-key
  (declare (xargs :guard (natp n)))
  (declare (xargs :mode :program))
  (nth-all-but-zero-nil-t n))

(register-custom-type wf-key t nth-wf-key wf-keyp)

;; Same problem as in sets. A nil is also a good-map!
;; 3 April 2014
;; (defun non-empty-good-map (x)
;;   (declare (xargs :guard t))
;;   (and (consp x)
;;        (good-map x)))


(defun all-but-nilp (x)
  (declare (xargs :guard t))
  (not (equal x 'nil)))

; TODO: this is a major hiccup of our map and record implementation, disallowing nil explicitly!!
;; (register-data-constructor (non-empty-good-map mset)
;;                            ((wf-keyp caar) (all-but-nilp cdar) (good-map cdr))
;;                            :proper nil)


(register-data-constructor (good-map mset)
                           ((wf-keyp caar) (allp cdar) (good-map cdr))
                           :hints (("Goal" :in-theory (enable good-map)))
                           :proper nil)

(defun nth-all-but-nil (n)
  (declare (xargs :mode :program))
  (declare (xargs :guard (natp n)))
  (cond ((eql n 0) 0)
        ((eql n 12) t)
        (t (nth-all-but-zero-nil-t n))))

(register-custom-type all-but-nil t nth-all-but-nil  all-but-nilp)

(defdata-subtype all-but-zero-nil-t all)
(defdata-subtype all-but-nil all) ;make this the pseudo top type!

(defdata-subtype acons cons :hints (("Goal" :in-theory (enable aconsp))))
(defdata-subtype cons all-but-nil)
(defdata-subtype atom all)
(defdata-subtype atom-list true-list)
(defdata-subtype alist true-list)
(defdata-subtype list all)
(defdata-subtype true-list list)




(defdata cons-cccca-cccca (cons cons-cca-cca cons-cca-cca) )
(defdata cons-a-ca (cons atom cons-atom) )
(defdata cons-a-cca (cons atom cons-ca-ca) )
(defdata cons-a-cccca (cons atom cons-cca-cca))
(defdata cons-ca-cca (cons cons-atom cons-ca-ca))

(defdata cons-ca-cccca (cons cons-atom cons-cca-cca) )
;(verify-guards allp)
(defdata cons-all-all-but-zero-nil-t (cons all all-but-zero-nil-t) )

(defun nth-improper-cons (n)
;  (declare (xargs :guard (natp n)))
  (declare (xargs  :mode :program))
  (b* (((mv choice seed)
        (defdata::weighted-switch-nat 
          '(
            1  ;cons-all-all-but-zero-nil-t
            1  ;cons-ca-ca
            1  ;cons-a-ca
            1  ;cons-a-cca
            1  ;cons-a-cccca
            1  ;cons-cccca-cccca
            1  ;cons-ca-cca
            1  ;cons-ca-cccca
            ) n)))
    
    (case choice
      (0 (nth-cons-all-all-but-zero-nil-t seed))
      (1 (nth-cons-ca-ca seed))
      (2 (nth-cons-a-ca seed))
      (3 (nth-cons-a-cca seed))
      (4 (nth-cons-a-cccca seed))
      (5 (nth-cons-cccca-cccca seed))
      (6 (nth-cons-ca-cca seed))
      (7 (nth-cons-ca-cccca seed))
      (t '(1 . 2)))))

(register-custom-type improper-cons t nth-improper-cons  improper-consp)

(defdata-subtype improper-cons cons)


(defdata-subtype proper-cons cons)

;this was missing before and so we werent inferring proper-consp when
;type-alist knew both true-listp and proper-consp, and this is common in ACL2
(defdata-subtype proper-cons  true-list)

(defdata-disjoint proper-cons improper-cons)
(defdata-disjoint atom cons)



;new exports
;; (defmacro disjoint-p (T1 T2)
;;    ":Doc-Section DATA-DEFINITIONS
;;   top-level query wether two types are disjoint~/
;;   ~c[(disjoint-p T1 T2)] asks the question
;;   are T1, T2 disjoint? This call makes a quick
;;   lookup into the internal data type graph where
;;   disjoint relation information provided by the user
;;   in the past is stored and used to compute the
;;   disjoint relation closure. If they are pairwise
;;   disjoint (according to the computed information)
;;   then we get back an affirmative , i.e ~c[t]. otherwise
;;   it returns ~c[nil].
  
;;   ~bv[]
;;   Examples:
;;   (disjoint-p cons list)
;;   (disjoint-p pos acl2-number)
;;   (disjoint-p integer complex)
;;   ~ev[]                      
;;   ~bv[]
;;   Usage:
;;   (disjoint-p <Type-name1> <Type-name2>)
;;   ~ev[]~/
;;   "
;;    `(trans-eval '(defdata::is-disjoint$$ ',t1 ',t2 defdata::R$ defdata::types-ht$) 'disjoint-p state nil))
;  `(is-disjoint ',T1 ',T2 R$ types-ht$))


;; (defmacro show-all-defdata-types ()
;;   `(table-alist 'defdata::types-info-table (w state)))

;; (defmacro subtype-p (T1 T2)
;;    ":Doc-Section DATA-DEFINITIONS
;;   top-level query wether two types are disjoint~/
;;   ~c[(subtype-p T1 T2)] asks the question
;;   is T1 a subtype of T2? This call makes a quick
;;   lookup into the internal data type graph where
;;   subtype relation information provided by the user
;;   in the past is stored and used to compute the
;;   subtype relation closure. If T1 is indeed a subtype
;;   of T2 (according to the computed information)
;;   then we get back an affirmative , i.e ~c[t]. otherwise
;;   it returns ~c[nil].
  
;;   ~bv[]
;;   Examples:
;;   (subtype-p boolean atom)
;;   (subtype-p character string)
;;   (subtype-p list cons)
;;   ~ev[]                      
;;   ~bv[]
;;   Usage:
;;   (subtype-p <Type-name1> <Type-name2>)
;;   ~ev[]~/
;;   "
;;    `(trans-eval '(defdata::is-subtype$$ ',t1 ',t2 defdata::R$ defdata::types-ht$) 'subtype-p state nil))
  ;`(is-subtype$$ ',T1 ',T2 R$ types-ht$))




; TODO 29 March 2014
; - add oddp and evenp (but do this consistently, these definitions are only valid when we additionally know that v is a integer.
(defun nth-even (n) 
  (declare (xargs :guard (natp n)))
  (* 2 (nth-integer n)))

(defdata::register-type even 
               :predicate evenp 
               :enumerator nth-even)

(defun nth-odd (n) 
  (declare (xargs :guard (natp n)))
  (if (evenp n)
      (1+ n)
    (- n)))

;(defun nth-odd (n) (1+ (* 2 (nth-integer))))
(defdata::register-type odd 
               :predicate oddp 
               :enumerator nth-odd)

(defdata-subtype var symbol)

(in-theory (disable varp))
