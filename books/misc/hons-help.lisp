;   hons-help.lisp                                Boyer & Hunt

(in-package "ACL2")

; In this file one may find some helpful functions and lemmas in the
; "HONS School", but none of them require "under the hood"
; definitions.  That is, the "user" could do all this by himself.

(defmacro ansfl (x y)
  
  "(ANSFL x y) returns the single value X after first flushing
  the fast hash table backing for Y, if Y is a fast alist.  Thus

     (ANSFL X Y) = X

  X must be a form that returns a single value."

  `((lambda (ansfl-do-not-use-elsewhere1 ansfl-do-not-use-elsewhere2)
      (declare (ignore ansfl-do-not-use-elsewhere2))
      ansfl-do-not-use-elsewhere1)
    ,x
    (flush-hons-get-hash-table-link ,y)))

(defmacro ansfl1 (x)
  `((lambda (ansfl1-do-not-use-elsewhere1)
      ((lambda (ansfl1-do-not-use-elsewhere1
                ansfl1-do-not-use-elsewhere2)
         (declare (ignore ansfl1-do-not-use-elsewhere2))
        ansfl1-do-not-use-elsewhere1)))
    ,x))

(defabbrev gentle-car    (x) (if (consp x) (car x) nil))
(defabbrev gentle-cdr    (x) (if (consp x) (cdr x) nil))
(defabbrev gentle-caar   (x) (gentle-car (gentle-car x)))
(defabbrev gentle-cadr   (x) (gentle-car (gentle-cdr x)))
(defabbrev gentle-cdar   (x) (gentle-cdr (gentle-car x)))
(defabbrev gentle-cddr   (x) (gentle-cdr (gentle-cdr x)))
(defabbrev gentle-caaar  (x) (gentle-car (gentle-caar x)))
(defabbrev gentle-cadar  (x) (gentle-car (gentle-cdar x)))
(defabbrev gentle-cdaar  (x) (gentle-cdr (gentle-caar x)))
(defabbrev gentle-cddar  (x) (gentle-cdr (gentle-cdar x)))
(defabbrev gentle-caadr  (x) (gentle-car (gentle-cadr x)))
(defabbrev gentle-caddr  (x) (gentle-car (gentle-cddr x)))
(defabbrev gentle-cdadr  (x) (gentle-cdr (gentle-cadr x)))
(defabbrev gentle-cdddr  (x) (gentle-cdr (gentle-cddr x)))
(defabbrev gentle-caaaar (x) (gentle-car (gentle-caaar x)))
(defabbrev gentle-cadaar (x) (gentle-car (gentle-cdaar x)))
(defabbrev gentle-cdaaar (x) (gentle-cdr (gentle-caaar x)))
(defabbrev gentle-cddaar (x) (gentle-cdr (gentle-cdaar x)))
(defabbrev gentle-caadar (x) (gentle-car (gentle-cadar x)))
(defabbrev gentle-caddar (x) (gentle-car (gentle-cddar x)))
(defabbrev gentle-cdadar (x) (gentle-cdr (gentle-cadar x)))
(defabbrev gentle-cdddar (x) (gentle-cdr (gentle-cddar x)))
(defabbrev gentle-caaadr (x) (gentle-car (gentle-caadr x)))
(defabbrev gentle-cadadr (x) (gentle-car (gentle-cdadr x)))
(defabbrev gentle-cdaadr (x) (gentle-cdr (gentle-caadr x)))
(defabbrev gentle-cddadr (x) (gentle-cdr (gentle-cdadr x)))
(defabbrev gentle-caaddr (x) (gentle-car (gentle-caddr x)))
(defabbrev gentle-cadddr (x) (gentle-car (gentle-cdddr x)))
(defabbrev gentle-cdaddr (x) (gentle-cdr (gentle-caddr x)))
(defabbrev gentle-cddddr (x) (gentle-cdr (gentle-cdddr x)))

(defn gentle-binary-+ (x y)
  (if (acl2-numberp x)
      (if (acl2-numberp y)
          (+ x y)
        x)
    (if (acl2-numberp y)
        y
      0)))

(defmacro gentle-+ (&rest r)
  (cond ((atom r) 0)
        ((atom (cdr r)) `(gentle-binary-+ 0 ,(car r)))
        ((atom (cddr r)) `(gentle-binary-+ ,(car r) ,(cadr r)))
        (t `(gentle-binary-+ ,(car r) (gentle-+ ,@(cdr r))))))

(defn gentle-revappend (x y)
  (if (atom x) y
    (gentle-revappend (cdr x) (cons (car x) y))))

(defn gentle-reverse (x)
  (if (stringp x)
      (reverse x)
    (gentle-revappend x nil)))

(defn gentle-strip-cars (l)
  (if (atom l)
      nil
    (cons (if (atom (car l))
               (car l)
             (car (car l)))
          (gentle-strip-cars (cdr l)))))

(defn gentle-strip-cdrs (l)
  (if (atom l)
      nil
    (cons (if (atom (car l))
              (car l)
            (cdr (car l)))
          (gentle-strip-cdrs (cdr l)))))

(defn gentle-length (l)
  (if (stringp l)
      (length l)
    (len l)))

(defn gentle-member-eq (x y)
  (declare (xargs :guard (symbolp x)))
  (cond ((atom y) nil)
        ((eq x (car y)) y)
        (t (gentle-member-eq x (cdr y)))))

(defn gentle-member-eql (x y)
  (declare (xargs :guard (eqlablep x)))
  (cond ((atom y) nil)
        ((eql x (car y)) y)
        (t (gentle-member-eql x (cdr y)))))

(defn gentle-member-equal (x y)
  (cond ((atom y) nil)
        ((equal x (car y)) y)
        (t (gentle-member-equal x (cdr y)))))
    
(defn gentle-member (x y)
  (cond ((symbolp x) (gentle-member-eq x y))
        ((or (characterp x) (acl2-numberp x))
         (gentle-member-eql x y))
        (t (gentle-member-equal x y))))

(defn gentle-binary-- (x y)
  (if (and (acl2-numberp x)
           (acl2-numberp y))
      (- x y)
    0))

(defmacro gentle-- (x &optional y)
  (cond ((null y) `(gentle-unary-- ,x))
        (t `(gentle-binary-- ,x (gentle-+ ,y)))))

(defn const-list-acc (n const acc)
  (cond ((not (posp n)) acc)
        (t (const-list-acc (1- n) const (hons const acc)))))

(defn nil-list (n)
  (const-list-acc n nil nil))

(defn t-list (n)
  (const-list-acc n t nil))

(defn gentle-take (n l)

 "Unlike TAKE, GENTLE-TAKE fills at the end with NILs, if necessary, to
 always return a list n long."

 (cond ((not (posp n)) nil)
       ((atom l) (nil-list n))
       (t (cons (car l)
                (gentle-take (1- n) (cdr l))))))

(defn make-same-length (v1 v2)
  (let ((l1 (len v1))
        (l2 (len v2)))
    (cond ((eql l1 l2) (mv v1 v2))
          ((< l1 l2)   (mv (gentle-take l2 v1) v2))
          (t           (mv v1 (gentle-take l1 v2))))))

(defn gentle-last (l)
  (if (or (atom l) (atom (cdr l)))
      l
    (gentle-last (cdr l))))

(defn gentle-butlast (l n)
  (gentle-take (gentle-- (gentle-length l) n)
               l))

(defmacro ansfl-list (l x)
  (if (atom l)
      x
    `(ansfl (ansfl-list ,(cdr l) ,x)
            ,(car l))))

(defn ansfl-last-list (r bindings)
  (if (atom bindings)
      r
    `(ansfl ,(ansfl-last-list r (gentle-cdr bindings))
            ,(gentle-caar bindings))))

(defmacro het* (bindings &rest r)
  
; This implementation of het* is somewhat defective in that it is
; incapable of returning multiple values.  We cannot see how to fix
; it.

  `(let* ,bindings
     ,@(gentle-butlast r 1)
     ,(ansfl-last-list (car (gentle-last r)) bindings)))

(defmacro with-fast-list (var term name form)
  `(let ((,var (hons-put-list
                ,term
                t
                ,name)))
     (ansfl ,form ,var)))

(defmacro with-fast-alist (var l1 l2 name form)
  `(let ((,var (hons-put-list ,l1 ,l2 ,name)))
     (ansfl ,form ,var)))

; A new kind of association list.

(defmacro hons-list (&rest x)
  (if (atom x) nil
    (list 'hons (car x) (cons 'hons-list (cdr x)))))

(defmacro hons-list* (&rest x)
  (cond ((atom x) x)
        ((atom (cdr x)) (car x))
        (t (list 'hons (car x) (cons 'hons-list* (cdr x))))))

(defn defnp (x)
  (and (consp x)
       (symbolp (car x))
       (eq (car x) 'defn)
       (consp (cdr x))
       (symbolp (cadr x))
       (consp (cddr x))
       (symbol-listp (caddr x))
       (consp (cdddr x))
       (true-listp (cdddr x))))

(defn defn-listp (x)
  (if (atom x)
      (null x)
    (and (defnp (car x))
         (defn-listp (cdr x)))))

(defun mu-defn-fn (l)
  (declare (xargs :guard (defn-listp l)))
  (if (atom l) nil
    (cons `(defun
             ,(cadr (car l))
             ,(caddr (car l))
             (declare (xargs :guard t))
             ,@(cdddr (car l)))
          (mu-defn-fn (cdr l)))))

(defmacro mu-defn (&rest l)
  `(mutual-recursion ,@(mu-defn-fn l)))


; HONS-LEN1 and HONS-LEN defined to make a tail-recursive version of
; LEN.

(defun hons-len1 (x acc)
  (declare (xargs :guard (and (integerp acc) (<= 0 acc))))
  (if (atom x)
      acc
    (hons-len1 (cdr x) (+ 1 acc))))

(defn hons-len (x)
  (hons-len1 x 0))

(defthm natp-hons-len
  (implies (integerp n)
           (and (integerp (hons-len1 x n))
                (>= (hons-len1 x n) n))))

(defn hons-member-equal (x y)
  (cond ((atom y) nil)
        ((hons-equal x (car y)) y)
        (t (hons-member-equal x (cdr y)))))

(defn hons-copy-list-cons (x)
  (cond ((atom x) x)
        (t (cons (hons-copy (car x))
                 (hons-copy-list-cons (cdr x))))))

(defn hons-remove-equal-cons (x y)
  (cond ((atom y) y)
        ((hons-equal x (car y))
         (hons-remove-equal-cons x (cdr y)))
        (t (cons (car y) (hons-remove-equal-cons x (cdr y))))))

(defn hons-binary-append (x y)
  (if (atom x)
      y
    (hons (car x) (hons-binary-append (cdr x) y))))

(defmacro hons-append (x y &rest rst)
  "APPEND using HONS instead of CONS"
  (xxxjoin 'hons-binary-append
           (cons x (cons y rst))))

(defn hons-revappend (x y)
  (if (atom x) y
    (hons-revappend (cdr x) (hons (car x) y))))

(defn hons-reverse (x)
  (if (stringp x) (reverse x)
    (hons-revappend x nil)))

(defthm alistp-hons-revappend
  (implies (and (alistp x)
                (alistp y))
           (alistp (hons-revappend x y))))

; The functions HONS-GETPROP and HONS-PUTPROP support fast property
; lists for any type of keys, not just symbols.  With HONS-PUTPROP you
; can cause X to have the value VAL under the key Y, and with
; HONS-GETPROP you can later ask for the value of X under the key Y
; and get back VAL.  As usual in Lisp, there is potential confusion
; over whether NIL is a value of an indication of no value.

(defn hons-getprop (x y al)
  (cdr (hons-get (hons x y) al)))

(defn hons-putprop (x y val al)
  (hons-acons (hons x y) val al))

(defthm key-theorem-about-hons-getprop-and-hons-putprop
  (equal (hons-getprop x1 y1 (hons-putprop x2 y2 val al))
	 (if (and (equal x1 x2)
		  (equal y1 y2))
	     val
	   (hons-getprop x1 y1 al))))


; Some "fast" operations for "set" intersection, union, and set-diff
; intended for use on lists of ACL2 objects without duplications.

(defn hons-put-list (keys values l)

; If there are not enough values, the last atom of values is used for
; the remaining values.  If there are not as many keys as values, the
; extra values are ignored.

; Warnings: The pairs are consed onto l in what might seem to be the
; reverse order.  And redundant pairs are not even consed on to l at
; all.  Unless the old value of (hons-get key l) is nil, in which case
; we do cons, even if the new val is nil.

; So if you need to control the order and/or presence of the added
; pairs, write another function.

  (if (atom keys)
      l
    (let* ((cp (consp values))
           (val (if cp (car values) values))
           (next-values (if cp (cdr values) values))
           (old-pair (hons-get (car keys) l))
           (redundant (and old-pair (hons-equal val (cdr old-pair))))
           (next-l (if redundant l (hons-acons (car keys) val l))))
      (hons-put-list (cdr keys) next-values next-l))))

(defun worth-hashing1 (l n)
  (declare (type (integer 0 18) n)
           (xargs :guard t))
  (cond ((eql n 0) t)
        ((atom l) nil)
        (t (worth-hashing1 (cdr l) (the (integer 0 18)
                                     ;; 18 is a *magic-number*
                                     (1- n))))))

(defconst *magic-number-for-hashing* 

  18

  ":Doc-Section Hons-and-Memoization

  Assoc is sometimes faster than gethash.~/

  Lisp folklore says it is faster to use ASSOC than GETHASH on a list
  if the list has length 18 or less.~/~/")

(defn worth-hashing (l)
  (worth-hashing1 l *magic-number-for-hashing*))

(defn hons-int1 (l1 al2)
  (cond ((atom l1) nil)
        ((hons-get (car l1) al2)
         (cons (car l1) (hons-int1 (cdr l1) al2)))
        (t (hons-int1 (cdr l1) al2))))

(defn hons-intersection2 (l1 l2)
  (cond ((atom l1) nil)
        ((hons-member-equal (car l1) l2)
         (cons (car l1) (hons-intersection2 (cdr l1) l2)))
        (t (hons-intersection2 (cdr l1) l2))))

(defn hons-intersection (l1 l2)  ; preserves order of members in l1
  (cond ((worth-hashing l2)
         (with-fast-list fl2 l2 '*hons-intersection-alist*
                         (hons-int1 l1 fl2)))
        (t (hons-intersection2 l1 l2))))

(defn hons-intersect-p1 (l1 al2)
  (cond ((atom l1) nil)
        ((hons-get (car l1) al2)
         t)
        (t (hons-intersect-p1 (cdr l1) al2))))

(defn hons-intersect-p2 (l1 l2)
  (cond ((atom l1) nil)
        ((hons-member-equal (car l1) l2)
         t)
        (t (hons-intersect-p2 (cdr l1) l2))))

(defn hons-intersect-p (l1 l2) ; returns T or NIL
  (cond ((and (worth-hashing l1)
              (worth-hashing l2))
         (with-fast-list fl2 l2 '*hons-intersect-p-alist*
                         (hons-intersect-p1 l1 fl2)))
        (t (hons-intersect-p2 l1 l2))))

(defn hons-sd1 (l1 al2)
  (cond ((atom l1) nil)
        ((hons-get (car l1) al2)
         (hons-sd1 (cdr l1) al2))
        (t (cons (car l1) (hons-sd1 (cdr l1) al2)))))

(defn hons-set-diff2 (l1 l2)
  (cond ((atom l1) nil)
        ((hons-member-equal (car l1) l2)
         (hons-set-diff2 (cdr l1) l2))
        (t (cons (car l1) (hons-set-diff2 (cdr l1) l2)))))

(defn hons-set-diff (l1 l2) ; preserves order of members in l1
  (cond ((worth-hashing l2)
         (with-fast-list fl2 l2 '*hons-set-diff-alist*
                         (hons-sd1 l1 fl2)))
        (t (hons-set-diff2 l1 l2))))

(defn hons-union1 (l1 al2 acc)
  (cond ((atom l1) acc)
        ((hons-get (car l1) al2)
         (hons-union1 (cdr l1) al2 acc))
        (t (hons-union1 (cdr l1) al2 (cons (car l1) acc)))))

(defn hons-union2 (l1 l2 acc)
  (cond ((atom l1) acc)
        ((hons-member-equal (car l1) l2)
         (hons-union2 (cdr l1) l2 acc))
        (t (hons-union2 (cdr l1) l2 (cons (car l1) acc)))))

(defn hons-union (l1 l2)

; HONS-UNION may run faster if L1 and L2 are lists of atoms or honsps,
; since HONS-MEMBER-EQUAL and HONS-GET may be used.

; To prove someday:
; (defthm hons-union-thm
;  (equal (gentle-member x (hons-union l1 l2))
;         (or (gentle-member x l1)
;             (gentle-member x l2))))

  (cond ((atom l1) l2)
        ((atom l2) l1)
        ((atom (cdr l1))
         (if (hons-member-equal (car l1) l2)
             l2
           (cons (car l1) l2)))
        ((atom (cdr l2))
         (if (hons-member-equal (car l2) l1)
             l1
           (cons (car l2) l1)))
        (t (let ((len1 (len l1))
                 (len2 (len l2)))
             (cond ((and (>= len2 len1)
                         (>= len2 *magic-number-for-hashing*))
                    (with-fast-list
                     fl2 l2 '*hons-union*
                     (hons-union1 l1 fl2 l2)))
                   ((and (>= len1 len2)
                         (>= len1 *magic-number-for-hashing*))
                    (with-fast-list
                     fl1 l1 '*hons-union*
                     (hons-union1 l2 fl1 l1)))
                   (t (hons-union2 l1 l2 l2)))))))

(defn hons-union-list (l)
  (if (atom l) nil (hons-union (car l) (hons-union-list (cdr l)))))

(defn hons-dups-p1 (l tab)
  (cond ((atom l) (ansfl nil tab))
        ((hons-get (car l) tab)
         (ansfl l tab))
        (t (hons-dups-p1 (cdr l) (hons-acons (car l) t tab)))))

(defn hons-dups-p (l)

; If L has no duplicate members, then (HONS-DUPS-P L) is NIL.  If L
; has equal members, then (HONS-DUPS-P l) returns the second tail of L
; whose CAR is the first member of L that occurs twice in L.

  (hons-dups-p1 l '*hons-dups-p*))

(defn hons-remove-duplicates1 (l tab)
  (cond ((atom l) (ansfl nil tab))
        ((hons-get (car l) tab)
         (hons-remove-duplicates1 (cdr l) tab))
        (t (cons (car l)
                 (hons-remove-duplicates1
                  (cdr l)
                  (hons-acons (car l) t tab))))))

(defn hons-remove-duplicates (l)

; preserves order, deleting later occurrences

  (hons-remove-duplicates1 l '*hons-remove-duplicates*))

(defn hons-subset1 (l al)
  (or (atom l)
      (and (hons-get (car l) al)
           (hons-subset1 (cdr l) al))))

(defn hons-subset2 (l1 l2)
  (cond ((atom l1) t)
        ((hons-member-equal (car l1) l2)
         (hons-subset2 (cdr l1) l2))))

(defn hons-subset (l1 l2)
  (cond ((worth-hashing l2)
         (with-fast-list fl2 l2 '*hons-subset-alist*
                         (hons-subset1 l1 fl2)))
        (t (hons-subset2 l1 l2))))

(defn hons-set-equal (l1 l2)
  (and (hons-subset l1 l2)
       (hons-subset l2 l1)))

(defn odds1 (x ans)
  (cond ((atom x) ans)
        ((atom (cdr x)) (cons (car x) ans))
        (t (odds1 (cddr x) (cons (car x) ans)))))

(defn evens1 (x ans)
  (cond ((atom x) ans)
        ((atom (cdr x)) ans)
        (t (evens1 (cddr x) (cons (cadr x) ans)))))

(defthm odds1-length
  (implies (and (not (atom x))
                (not (atom (cdr x))))
           (< (len (odds1 x ans))
              (+ (len x)
                 (len ans))))
  :rule-classes :linear)

(defthm evens1-length
  (implies (and (not (atom x))
                (not (atom (cdr x))))
           (< (len (evens1 x ans))
              (+ (len x)
                 (len ans))))
  :rule-classes :linear)

(defun ms-merge (l1 l2 h)

; If (1) both L1 and and L2 are alists,
;    (2) H is an alist that maps the car of each member of L1 and L2
;        to an ACL2 ordinal, cf. O-P, and
;    (3) both L1 and L2 are weakly O-P increasing with respect
;        to the H values of their cars,
; then (MS-MERGE L1 L2 H) is a permutation of (APPEND L1 L2)
; that is weakly increasing with respect to the H value
; of the cars of its members.

  (declare (xargs :guard t
                  :measure (+ (len l1) (len l2))))
  (cond ((atom l1) l2)
        ((atom l2) l1)
        ((atom (car l1)) nil) ; to help with guards
        ((atom (car l2)) nil)
        (t (let ((m1 (cdr (hons-get (caar l1) h)))
                 (m2 (cdr (hons-get (caar l2) h))))
             (cond ((and (o-p m1)
                         (o-p m2)
                         (o< m1 m2))
                    (cons (car l1) (ms-merge (cdr l1) l2 h)))
                   (t (cons (car l2) (ms-merge l1 (cdr l2) h))))))))

(defun merge-sort (a h)

; If both A and H are alists and H maps the car of each member of A to
;    an ACL2 ordinal, cf. O-P,
; then (MERGE-SORT A H) is a permutation of A whose cars are
;    weakly O-<-increasing under H.

; For efficiency, H should be a fast alist, but there is no reason for
; A to be.

  (declare (xargs :guard t
                  :verify-guards nil
                  :measure (len a)))
  (if (or (atom a) (atom (cdr a))) a
    (ms-merge (merge-sort (odds1 a nil) h)
              (merge-sort (evens1 a nil) h)
              h)))

(verify-guards merge-sort)

(defn hons-merge-sort (a h)
  (hons-copy (merge-sort a h)))

; This is an "under the hood" remark.  If the system is built with
; *break-honsp* non-NIL, then one will be rudely interrupted whenever
; HONSP returns NIL.  So if you wish to copy a CONS structure into a
; HONS structure, use HONS-COPY-R instead of HONS-COPY.

(defn hons-copy-r (x)
  ;; r stands for recursive
  (if (atom x) x
    (hons (hons-copy-r (car x))
          (hons-copy-r (cdr x)))))

(defn hons-copy-list-r (x)
  ;; r stands for recursive
  (if (atom x) x
    (hons (car x)
          (hons-copy-list-r (cdr x)))))

; There are probably many such lemmas that we could prove...

(defthm symbol-listp-hons-copy-list-r
  (implies (symbol-listp x)
           (symbol-listp (hons-copy-list-r x))))

;;; Defhonst

;; Defhonst is like defconst.

;; The record for all defhonst values is kept in the ACL2 global
;; 'defhonst.  To flush all defhonst records manually, one may:
;; (f-put-global 'defhonst nil state).

(defmacro update-defhonst (f r)
  `(let ((f ,f) (r ,r))
     (pprogn
      (f-put-global
       'defhonst
       (hons (hons (cadr r)
                   (concatenate 'string "," (symbol-name f)))
             (if (boundp-global 'defhonst state)
                 (get-global 'defhonst state)
               nil))
       state)
      (value f))))

(defmacro defhonst (name form &key (evisc 'nil eviscp) check doc)

; From Matt Mon Sep 29 09:53:49 CDT 2008

  `(with-output
    :off summary
    (progn
      (defconst ,name (hons-copy ,form) ,doc)
      (table evisc-table
             ,name
             ,(if eviscp
                  evisc
                (let ((str (symbol-name name)))
                  (if (may-need-slashes str)
                      (concatenate 'string "#.|" str "|")
                    (concatenate 'string "#." str)))))
      (table persistent-hons-table
             (let ((x ,name))
               (if (or (consp x) (stringp x))

; honsp-check without check

                   x
                 nil))
             t)
      ,@(and check
             `((assert-event ,check)))
      (value-triple ',name))))

(defmacro all-memoized-fns (&optional show-conditions)
  (if show-conditions
      '(table-alist 'memoize-table (w state))
    '(strip-cars (table-alist 'memoize-table (w state)))))

(defstub fail (x y) t :doc

  ":Doc-Section Miscellaneous
     There are no axioms about FAIL except the equality axioms.~/~/

   One can prove:

          (thm (implies (and (equal x1 x2) (equal y1 y2))
                        (equal (fail x1 y1) (fail x2 y2))))

   However, if FAIL is called at run-time, an error occurs.

   FAIL can perhaps be understood in analogy with the notion of a
   'resource error'.  Though one can prove:

      (thm (implies (posp n) (consp (make-list n))))

   what will happen if one invokes (make-list (expt 2 2000))?  It is
   hard to predict, but eventually, something like an error will
   occur.~/"

)

(set-state-ok t)

; MattK: Using make-event for now so that plev-fn can be defined suitably for
; Version 3.4 and also for the pre-v-3.5 development version.
(make-event
 (if (getprop 'set-evisc-tuple 'macro-args nil 'current-acl2-world (w state))
     '(defn plev-fn (length level lines circle pretty readably state)
        (declare (xargs :mode :program))
        (let* ((old-tuple (default-evisc-tuple state))
               (new-tuple (list (car old-tuple) level length 
                                (cadddr old-tuple))))
          (mv-let (flg val state)
                  (set-evisc-tuple new-tuple
                                   :iprint :same
                                   :sites '(:TERM :LD
                                                  ;; :TRACE
                                                  :ABBREV))
                  (declare (ignore val))
                  (mv flg
                      (list :length
                            length
                            :level
                            level
                            :lines
                            lines
                            :circle
                            circle
                            :readably
                            readably
                            :pretty
                            pretty)
                      state))))
   '(defn plev-fn (length level lines circle pretty readably state)
      (declare (xargs :mode :program))
      (let* ((old-tuple (default-evisc-tuple state))
             (new-tuple (list (car old-tuple) level length 
                              (cadddr old-tuple))))
        (let ((state (set-brr-term-evisc-tuple new-tuple)))
          (let ((state
                 (f-put-global 'user-default-evisc-tuple
                               new-tuple state)))
            (let ((state
                   (f-put-global 'user-term-evisc-tuple
                                 new-tuple state)))
              (mv-let (flg ans state)
                      (set-ld-evisc-tuple new-tuple state)
                      (declare (ignore ans))
                      (mv flg
                          (list :length
                                length
                                :level
                                level
                                :lines
                                lines
                                :circle
                                circle
                                :readably
                                readably
                                :pretty
                                pretty)
                          state)))))))))

(defmacro plev (&key (length '16)
                     (level '3)
                     (lines 'nil)
                     (circle 't)
                     (pretty 't)
                     (readably 'nil))

  ":Doc-Section Hons-and-Memoization

  Sets some print control variables.~/

    PLEV sets variables that control printing via the keywords
    :LENGTH :LEVEL :LINES :CIRCLE :PRETTY and :READABLY.
    with defaults:
    16       3     NIL     T       T           NIL.~/~/"


  `(plev-fn ,length ,level ,lines ,circle ,pretty ,readably state))

(defn make-list-of-numbers (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (list n)
    (hons n (make-list-of-numbers (1- n)))))

(defmacro plev-max (&key (length 'nil)
                         (level 'nil)
                         (lines 'nil)
                         (circle 'nil)
                         (pretty 't)
                         (readably 'nil))

  ":Doc-Section Hons-and-Memoization

  (PLEV-MAX) sets some print control variables to maximal values.~/
  ~/~/"  

  `(plev-fn ,length ,level ,lines ,circle ,pretty ,readably state))


(defmacro plev-min (&key (length '3)
                         (level '3)
                         (lines '60)
                         (circle 't)
                         (pretty 'nil)
                         (readably 'nil))

  ":Doc-Section Hons-and-Memoization

  (PLEV-MIN) sets some print control variables to minimal values.~/
  ~/~/"

  `(plev-fn ,length ,level ,lines ,circle ,pretty ,readably state))

(defn make-fal (al name)
  ":Doc-Section Hons-and-Memoization

  Make a fast alist out of an alist~/

  (MAKE-FAL al name) copies the alist AL with hons-acons
  to make a fast alist that ends with NAME.~/~/"

  
  (cond ((atom al) name)
        (t (hons-acons (gentle-caar al)
                       (gentle-cdar al)
                       (make-fal (cdr al) name)))))

(defn make-fal! (al name)
  (cond ((atom al) name)
        (t (hons-acons! (gentle-caar al)
                        (gentle-cdar al)
                        (make-fal (cdr al) name)))))

(defn hons-make-list (n a e)
  ":Doc-Section Hons-and-Memoization

  Honses A onto E N times.~/
  (HONS-MAKE-LIST n a e) is the result of N times honsing A onto E.
  Equal to (hons-append (make-list n :initial-element n) e).~/~/"

  (if (not (posp n))
      e
    (hons-make-list (1- n) a (hons a e))))

(defn hons-take (n l)
  ":Doc-Section Hons-and-Memoization

 First n elements of l~/

 (HONS-TAKE n l) returns a honsed list of the first N elements of L.
 To always return a list of n elements, HONS-TAKE fills at the end
 with NIL, if necessary.~/~/"

 (cond ((not (posp n)) nil)
       ((atom l) (nil-list n))
       (t (hons (car l)
                (hons-take (1- n) (cdr l))))))

(defn alist-subsetp1 (l1 l2 el)
  (cond ((atom el) t)
        (t (and (equal (hons-get (car el) l1)
                       (hons-get (car el) l2))
                (alist-subsetp1 l1 l2 (cdr el))))))

(defn alist-subsetp (al1 al2)
  (alist-subsetp1 al1 al2 al1))

(defn alist-equal (al1 al2)
  ":Doc-Section Hons-and-Memoization

  (ALIST-EQUAL al1 al2) returns T or NIL according to whether for all
  x, (equal (hons-get x AL1) (hons-get x AL2)).~/

  ALIST-EQUAL sometimes runs rather fast on fast alists. ~/~/"

  (and (equal (fast-alist-len al1)
              (fast-alist-len al2))
       (alist-subsetp al1 al2)))

(defn gentle-assoc-eq (x y)
  (declare (xargs :guard (symbolp x)))
  (if (atom y)
      nil
    (if (and (consp (car y))
             (eq x (caar y)))
        (car y)
      (gentle-assoc-eq x (cdr y)))))

(defn gentle-assoc-eql (x y)
  (declare (xargs :guard (eqlablep x)))
  (if (atom y)
      nil
    (if (and (consp (car y))
             (eql x (caar y)))
        (car y)
      (gentle-assoc-eql x (cdr y)))))

(defn gentle-assoc-equal-help (x y)
  (if (atom y)
      nil
    (if (and (consp (car y))
             (hons-equal x (caar y)))
        (car y)
      (gentle-assoc-equal-help x (cdr y)))))

(defn gentle-assoc-equal (x y)
  (cond ((symbolp x) (gentle-assoc-eq x y))
        ((or (acl2-numberp x)
             (characterp x))
         (gentle-assoc-eql x y))
        (t (gentle-assoc-equal-help x y))))

(defn gentle-g (x l)
  (cdr (gentle-assoc-equal x l)))

(defn gentle-s-help (a v l)
  (cond ((atom l) (cons (cons a v) nil))
        ((and (consp (car l))
              (equal a (caar l)))
         (cons (cons a v) (cdr l)))
        (t (cons (car l)
                 (gentle-s-help a v (cdr l))))))

(defn gentle-s (a v l)

  "The key theorem about GENTLE-S is
   (equal (gentle-g a (gentle-s b v l))
          (if (equal a b)
              v
            (gentle-g a l)))."

  (let ((pair (gentle-assoc-equal a l)))
    (cond ((null pair) (cons (cons a v) l))
          ((equal v (cdr pair)) l)
          (t (gentle-s-help a v l)))))

(defthm gentle-s-a-thm0
  (equal (gentle-assoc-eq a (gentle-s-help b v l))
         (if (equal a b)
             (cons a v)
           (gentle-assoc-eq a l))))

(defthm gentle-s-a-thm1
  (equal (gentle-assoc-eql a (gentle-s-help b v l))
         (if (equal a b)
             (cons a v)
           (gentle-assoc-eql a l))))

(defthm gentle-s-a-thm2
  (equal (gentle-assoc-equal-help a (gentle-s-help b v l))
         (if (equal a b)
             (cons a v)
           (gentle-assoc-equal-help a l))))

(defthm gentle-s-a-thm3
  (equal (gentle-g a (gentle-s b v l))
         (if (equal a b)
             v
           (gentle-g a l))))
