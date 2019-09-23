(in-package "ACL2")

;; Some lemmas below are taken from other books with credit; in most cases they
;; replaced a theorem developed for this project which either had the same name
;; (causing a name conflict), or which rewrote the same target (causing :use
;; hints to become :useless even if the project-specific lemma was disabled for
;; the goal in question.)

(defthm make-character-list-makes-character-list
  (character-listp (make-character-list x)))

(defthm len-of-binary-append
  (equal (len (binary-append x y)) (+ (len x) (len y))))

(defthm len-of-make-character-list
  (equal (len (make-character-list x)) (len x)))

(defthm len-of-revappend
  (equal (len (revappend x y)) (+ (len x) (len y))))

(defthm len-of-take (equal (len (take n xs)) (nfix n)))

;; The following is redundant with the definition in
;; books/coi/lists/basic.lisp, from where it was taken with thanks.
(defthm nthcdr-of-append
  (equal (nthcdr n (append a b))
         (if (<= (nfix n) (len a))
             (append (nthcdr n a) b)
           (nthcdr (- n (len a)) b)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm take-of-binary-append-1
  (implies (and (natp i) (<= i (len x)))
           (equal (take i (binary-append x y))
                  (take i x))))

(defthm
  by-slice-you-mean-the-whole-cake-1
  (equal (first-n-ac (len l) l ac)
         (revappend ac (true-list-fix l)))
  :hints (("goal" :induct (revappend l ac)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (equal i (len l))
             (equal (first-n-ac i l ac)
                    (revappend ac (true-list-fix l)))))))

;; The following is redundant with the definition in
;; books/std/lists/take.lisp, from where it was taken with thanks.
(defthm take-of-len-free
  (implies (equal len (len x)) (equal (take len x) (true-list-fix x))))

(defthm assoc-after-remove1-assoc
  (implies (not (equal name1 name2))
           (equal (assoc-equal name1 (remove1-assoc name2 alist))
                  (assoc-equal name1 alist))))

(defthm assoc-after-remove-assoc
  (equal (assoc-equal name1 (remove-assoc name2 alist))
         (if (not (equal name1 name2))
             (assoc-equal name1 alist)
           nil)))

(defthm character-listp-of-revappend
  (equal (character-listp (revappend x y))
         (and (character-listp (true-list-fix x))
              (character-listp y))))

(defthm character-listp-of-take
  (implies (character-listp l)
           (equal (character-listp (take n l))
                  (<= (nfix n) (len l)))))

(defthm character-listp-of-nthcdr
  (implies (and (character-listp l))
           (character-listp (nthcdr n l))))

;; The following is redundant with the definition in
;; books/std/strings/make-character-list.lisp, from where it was taken with
;; thanks.
(defthm str::make-character-list-when-character-listp
  (implies (character-listp x)
           (equal (make-character-list x) x)))

(defthm make-character-list-of-binary-append
  (equal (make-character-list (binary-append x y))
         (binary-append (make-character-list x) (make-character-list y))))

;; The following is redundant with the definition in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks.
(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (nfix (- (len l) (nfix n))))
  :hints (("Goal" :induct (nthcdr n l))))

;; The following is redundant with the definition in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks.
(defthm consp-of-nthcdr
  (equal (consp (nthcdr n x))
         (< (nfix n) (len x)))
  :hints (("Goal" :in-theory (disable len-of-nthcdr)
           :use ((:instance len-of-nthcdr (l x)))
           :expand (len (nthcdr n x)))))

(defthm revappend-of-binary-append-1
  (equal (binary-append (revappend x y) z)
         (revappend x (binary-append y z))))

(defthm
  binary-append-first-n-ac-nthcdr
  (implies (<= i (len l))
           (equal (binary-append (first-n-ac i l ac)
                                 (nthcdr i l))
                  (revappend ac l)))
  :hints (("goal" :induct (first-n-ac i l ac))))

;; The following is redundant with the definition in books/std/lists/nth.lisp,
;; from where it was taken with thanks.
(defthm nth-of-append
  (equal (nth n (append x y))
         (if (< (nfix n) (len x))
             (nth n x)
           (nth (- n (len x)) y))))

;; The following is redundant with the definition in
;; books/std/lists/append.lisp, from where it was taken with thanks.
(defthm associativity-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm member-of-a-nat-list
  (implies (and (nat-listp lst)
                (member-equal x lst))
           (and (integerp x) (<= 0 x)))
  :rule-classes ((:rewrite :corollary (implies (and (nat-listp lst)
                                                    (member-equal x lst))
                                               (<= 0 x)))
                 (:forward-chaining :corollary (implies (and (member-equal x lst)
                                                             (nat-listp lst))
                                                        (integerp x)))))

(defthm update-nth-of-boolean-list
  (implies (boolean-listp l)
           (equal (boolean-listp (update-nth key val l))
                  (booleanp val))))

(defthm nat-listp-of-binary-append
  (equal (nat-listp (binary-append x y))
         (and (nat-listp (true-list-fix x)) (nat-listp y))))

(defthm eqlable-listp-if-nat-listp (implies (nat-listp l) (eqlable-listp l)))

(defthm member-of-binary-append
  (iff (member-equal x (binary-append lst1 lst2))
       (or (member-equal x lst1)
           (member-equal x lst2))))

(defthm no-duplicatesp-of-append
  (equal (no-duplicatesp-equal (binary-append x y))
         (and (no-duplicatesp x)
              (no-duplicatesp y)
              (not (intersectp-equal x y)))))

(defthm intersectp-of-append-1
  (equal (intersectp-equal z (binary-append x y))
         (or (intersectp-equal z x)
             (intersectp-equal z y))))

(defthm intersectp-of-append-2
  (equal (intersectp-equal (binary-append x y) z)
         (or (intersectp-equal x z)
             (intersectp-equal y z))))

(defthm intersectp-is-commutative
  (equal (intersectp-equal x y)
         (intersectp-equal y x)))

(defthm subsetp-of-binary-append-1
  (subsetp-equal y (binary-append x y)))

(defthm subsetp-of-binary-append-2
  (subsetp-equal x (binary-append x y)))

(defthm subsetp-of-binary-append-3
  (equal (subsetp-equal (binary-append x y) z)
         (and (subsetp-equal x z) (subsetp-equal y z))))

(defthm subsetp-is-transitive
  (implies (and (subsetp-equal x y) (subsetp-equal y z))
           (subsetp-equal x z)))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/sets.lisp, from where it was taken with thanks.
(defthm
  subsetp-member
  (implies (and (member a x) (subsetp x y))
           (member a y))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary (implies (and (subsetp x y) (member a x))
                                 (member a y)))
   (:rewrite
    :corollary (implies (and (not (member a y)) (subsetp x y))
                        (not (member a x))))
   (:rewrite
    :corollary (implies (and (subsetp x y) (not (member a y)))
                        (not (member a x))))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-revappend
  (equal (nth n (revappend x y))
         (if (< (nfix n) (len x))
             (nth (- (len x) (+ 1 (nfix n))) x)
           (nth (- n (len x)) y))))

;; The following is redundant with the eponymous theorem in
;; books/misc/gentle.lisp, from where it was taken with thanks to
;; Messrs. Boyer, Hunt and Davis.
(defthm true-listp-of-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (true-listp ac)
                           (true-listp (make-list-ac n val ac))))))

;; The following is redundant with the eponymous theorem in
;; books/centaur/ubdds/param.lisp, from where it was taken with thanks to
;; Messrs. Boyer and Hunt.
(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc))))

(defthm consp-of-make-list-ac
  (iff (consp (make-list-ac n val ac))
       (or (not (zp n)) (consp ac))))

(defthm boolean-listp-of-make-list-ac
  (implies (booleanp val)
           (equal (boolean-listp (make-list-ac n val ac))
                  (boolean-listp ac))))

(defthm booleanp-of-car-make-list
  (implies (and (booleanp val)
                (boolean-listp ac)
                (> (+ n (len ac)) 0))
           (booleanp (car (make-list-ac n val ac)))))

(defthm car-of-make-list
  (equal (car (make-list-ac n val ac))
         (if (zp n) (car ac) val)))

(defthm cdr-of-make-list
  (equal (cdr (make-list-ac n val ac))
         (if (zp n)
             (cdr ac)
           (make-list-ac (- n 1) val ac))))

;; The following is redundant with the eponymous theorem in
;; books/data-structures/list-defthms.lisp, from where it was taken with thanks.
(defthm member-equal-nth
  (implies (< (nfix n) (len l))
           (member-equal (nth n l) l))
  :hints (("Goal" :in-theory (enable nth))))

(defthm make-character-list-of-revappend
  (equal (make-character-list (revappend x y))
         (revappend (make-character-list x)
                    (make-character-list y))))

(defthm
  take-of-make-character-list
  (implies (<= i (len l))
           (equal (take i (make-character-list l))
                  (make-character-list (take i l)))))

(defthm revappend-of-true-list-fix
  (equal (revappend x (true-list-fix y))
         (true-list-fix (revappend x y))))

(defthm append-of-true-list-fix
  (equal (append (true-list-fix x) y)
         (append x y)))

(defthm boolean-listp-of-revappend
  (equal (boolean-listp (revappend x y))
         (and (boolean-listp (true-list-fix x))
              (boolean-listp y))))

(defthm boolean-listp-of-first-n-ac
  (implies (boolean-listp l)
           (equal (boolean-listp (first-n-ac i l ac))
                  (boolean-listp (true-list-fix ac)))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/take.lisp, from where it was taken with thanks.
(defthm consp-of-take
    (equal (consp (take n xs))
           (not (zp n))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-make-list-ac
  (equal (nth n (make-list-ac m val acc))
         (if (< (nfix n) (nfix m))
             val
           (nth (- n (nfix m)) acc))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-nthcdr
  (equal (nth n (nthcdr m x))
         (nth (+ (nfix n) (nfix m)) x)))

(defthmd intersect-with-subset
  (implies (and (subsetp-equal x y)
                (intersectp-equal x z))
           (intersectp-equal y z)))

(defthm update-nth-of-make-list
  (implies (and (integerp key) (>= key n) (natp n))
           (equal (update-nth key val (make-list-ac n l ac))
                  (make-list-ac n l (update-nth (- key n) val ac)))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/update-nth.lisp, from where it was taken with thanks.
(defthm nthcdr-of-update-nth
  (equal (nthcdr n1 (update-nth n2 val x))
         (if (< (nfix n2) (nfix n1))
             (nthcdr n1 x)
           (update-nth (- (nfix n2) (nfix n1)) val (nthcdr n1 x)))))

(defthmd car-of-assoc-equal
  (let ((sd (assoc-equal x alist)))
    (implies (consp sd) (equal (car sd) x))))

(defthm update-nth-of-update-nth-1
  (implies (not (equal (nfix key1) (nfix key2)))
           (equal (update-nth key1 val1 (update-nth key2 val2 l))
                  (update-nth key2 val2 (update-nth key1 val1 l)))))

(defthm update-nth-of-update-nth-2
  (equal (update-nth key val2 (update-nth key val1 l))
         (update-nth key val2 l)))

;; This can probably be replaced by a functional instantiation.
(defthm nat-listp-of-remove
  (implies (nat-listp l)
           (nat-listp (remove-equal x l))))

;; This should be moved into the community books.
(defthm subsetp-of-remove
  (subsetp-equal (remove-equal x l) l))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/sets.lisp, from where it was taken with thanks.
(defthm member-of-remove
  (iff (member a (remove b x))
       (and (member a x)
            (not (equal a b))))
  :hints(("goal" :induct (len x))))

(defthm
  assoc-after-put-assoc
  (equal (assoc-equal name1 (put-assoc-equal name2 val alist))
         (if (equal name1 name2)
             (cons name1 val)
           (assoc-equal name1 alist))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks.
(defthm nthcdr-of-cdr
  (equal (nthcdr i (cdr x))
         (cdr (nthcdr i x))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/update-nth.lisp, from where it was taken with thanks.
(defthm update-nth-of-nth
  (implies (< (nfix n) (len x))
           (equal (update-nth n (nth n x) x) x)))

(defthm character-listp-of-make-list-ac
  (equal (character-listp (make-list-ac n val ac))
         (and (character-listp ac)
              (or (zp n) (characterp val)))))

(defthm string-listp-of-append
  (equal (string-listp (append x y))
         (and (string-listp (true-list-fix x))
              (string-listp y))))

(defthm true-listp-when-string-list
  (implies (string-listp x)
           (true-listp x)))

(defthm
  binary-append-take-nthcdr
  (implies (<= i (len l))
           (equal (binary-append (take i l)
                                 (nthcdr i l))
                  l)))

(defthm true-list-fix-when-true-listp
  (implies (true-listp x)
           (equal (true-list-fix x) x)))

(defthm true-list-fix-of-coerce
  (equal (true-list-fix (coerce text 'list))
         (coerce text 'list)))

(defthm len-of-true-list-fix
  (equal (len (true-list-fix x)) (len x)))

(defthm nth-of-make-character-list
  (equal (nth n (make-character-list x))
         (cond ((>= (nfix n) (len x)) nil)
               ((characterp (nth n x)) (nth n x))
               (t (code-char 0)))))

(defthm nth-of-first-n-ac
  (equal (nth n (first-n-ac i l ac))
         (cond ((>= (nfix n) (+ (len ac) (nfix i)))
                nil)
               ((< (nfix n) (len ac))
                (nth (- (len ac) (+ (nfix n) 1)) ac))
               (t (nth (- (nfix n) (len ac)) l)))))

;; Contributed to books/std/lists/nth.lisp
(defthm nth-of-take
  (equal (nth i (take n l))
         (if (< (nfix i) (nfix n))
             (nth i l)
           nil)))

(defthm nthcdr-of-nil (equal (nthcdr n nil) nil))

(defthmd nthcdr-when->=-n-len-l
  (implies (and (true-listp l)
                (>= (nfix n) (len l)))
           (equal (nthcdr n l) nil)))

(defthm revappend-of-revappend
  (equal (revappend (revappend x y1) y2)
         (revappend y1 (append x y2)))
  :hints
  (("goal" :in-theory (disable revappend-of-binary-append-1))))

(defthm
  character-listp-of-member-equal
  (implies (character-listp lst)
           (character-listp (member-equal x lst)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (character-listp lst)
                  (consp (member-equal x lst)))
             (character-listp (cdr (member-equal x lst)))))))

(defthm true-listp-of-member-equal
  (implies (true-listp lst)
           (true-listp (member-equal x lst)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (true-listp lst)
                  (consp (member-equal x lst)))
             (true-listp (cdr (member-equal x lst)))))))

(defthm len-of-member-equal
  (<= (len (member-equal x lst))
      (len lst))
  :rule-classes :linear)

(defthm len-of-remove1-assoc-equal
  (implies (consp (assoc-equal key alist))
           (equal (len (remove1-assoc-equal key alist))
                  (- (len alist) 1))))

;; Contributed to books/std/lists/remove1-equal.lisp
(defthm len-of-remove1-equal
  (equal (len (remove1-equal x l))
         (if (member-equal x l)
             (- (len l) 1)
           (len l))))

(defthm
  assoc-equal-of-remove1-assoc-equal
  (implies
   (and (not (equal key1 nil))
        (not (consp (assoc-equal key1 alist))))
   (not (consp (assoc-equal key1
                            (remove1-assoc-equal key2 alist))))))

;; Contributed to books/std/lists/remove1-equal.lisp
(defthm
  assoc-equal-of-remove1-equal
  (implies
   (and (not (equal key1 nil))
        (not (consp (assoc-equal key1 alist))))
   (not (consp (assoc-equal key1 (remove1-equal x alist)))))
  :rule-classes (:rewrite :type-prescription))

(defthm assoc-equal-when-member-equal
  (implies (and (member-equal x lst)
                (consp x)
                (not (equal (car x) nil)))
           (consp (assoc-equal (car x) lst))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks.
(defthm car-of-nthcdr
  (equal (car (nthcdr i x))
         (nth i x)))

(defthm stringp-of-nth
  (implies (string-listp l)
           (iff (stringp (nth n l))
                (< (nfix n) (len l)))))

(defthm string-listp-of-update-nth
  (implies (string-listp l)
           (equal (string-listp (update-nth key val l))
                  (and (<= (nfix key) (len l))
                       (stringp val)))))

(defthm revappend-of-binary-append-2
  (equal (revappend (binary-append x y1) y2)
         (revappend y1 (revappend x y2))))

(defthm add-pair-of-add-pair-1
  (equal (add-pair key value2 (add-pair key value1 l))
         (add-pair key value2 l)))

(defthm princ$-of-princ$
  (implies (and (stringp x) (stringp y))
           (equal (princ$ y channel (princ$ x channel state))
                  (princ$ (string-append x y) channel state))))

(defthmd
  painful-debugging-lemma-1
  (implies (and (integerp x) (integerp y))
           (integerp (+ x y))))

(defthmd
  painful-debugging-lemma-2
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

(defthmd painful-debugging-lemma-3
  (implies (integerp x)
           (integerp (unary-- x))))

(defthmd painful-debugging-lemma-4
  (equal (<= x (+ x y)) (>= y 0))
  :rule-classes
  ((:rewrite :corollary (equal (< (+ x y) x) (< y 0)))))

(defthmd painful-debugging-lemma-5
  (implies (and (>= x 0) (>= y 0))
           (not (< (+ x y) 0))))

(defthmd
  painful-debugging-lemma-6
  (equal (< x (+ x y)) (> y 0))
  :hints
  (("goal"
    :use (:instance painful-debugging-lemma-4 (x (+ x y))
                    (y (- y))))))

(defthm
  painful-debugging-lemma-7
  (equal (- (- x)) (fix x)))

(defthm
  painful-debugging-lemma-8
  (implies (not (zp x))
           (iff (< (binary-* x (len y)) x)
                (atom y))))

(defthmd
  painful-debugging-lemma-9
  (implies (and (integerp x) (integerp y) (< x y))
           (equal (< (+ 1 x) y)
                  (not (equal (+ 1 x) y)))))

(defthmd
  painful-debugging-lemma-10
  (implies (not (zp x1))
           (iff (equal (* x1 (len x2)) 0)
                (atom x2))))

(defthmd
  painful-debugging-lemma-11
  (implies (not (zp x1))
           (equal (< 0 (* x1 (len x2)))
                  (consp x2))))

(defthmd
  painful-debugging-lemma-12
  (implies
   (and (integerp x) (integerp y))
   (iff (equal (+ x (- y)) 0)
        (equal x y))))

(defthmd painful-debugging-lemma-13
  (implies (and (integerp x) (integerp y) (< x y))
           (<= (+ 1 x) y)))

;; The following is redundant with the eponymous theorem in
;; books/std/typed-lists/integer-listp.lisp, from where it was taken with
;; thanks.
(defthm
  integerp-of-nth-when-integer-listp
  (implies (integer-listp x)
           (iff (integerp (nth n x))
                (< (nfix n) (len x)))))

(defthm true-list-listp-of-append
  (equal (true-list-listp (append x y))
         (and (true-list-listp (true-list-fix x)) (true-list-listp y))))

(defthmd rationalp-of-nth-when-rational-listp
  (implies (rational-listp x)
           (iff (rationalp (nth n x))
                (< (nfix n) (len x)))))

(defthm
  member-of-remove1-assoc
  (implies
   (not (member-equal x lst))
   (not (member-equal x (remove1-assoc-equal key lst)))))

(defthm acl2-count-of-true-list-fix
  (<= (acl2-count (true-list-fix x))
      (acl2-count x))
  :rule-classes :linear)

(defthmd
  update-nth-of-revappend
  (equal (update-nth key val (revappend x y))
         (if (< (nfix key) (len x))
             (revappend (update-nth (- (len x) (+ 1 (nfix key)))
                                    val x)
                        y)
           (revappend x
                      (update-nth (- (nfix key) (len x))
                                  val y)))))

(defthm
  true-listp-of-update-nth
  (equal (true-listp (update-nth key val l))
         (or (>= (nfix key) (len l))
             (true-listp l)))
  :hints (("goal" :in-theory (enable update-nth)
           :induct (update-nth key val l)
           :expand ((true-listp l)
                    (:free (x y)
                           (true-listp (cons x y)))))))

(defthm nthcdr-of-nthcdr
  (equal (nthcdr a (nthcdr b x))
         (nthcdr (+ (nfix a) (nfix b)) x))
  :hints(("goal" :induct (nthcdr b x))))

(defthm last-of-member-equal
  (equal (last (member-equal x lst))
         (if (member-equal x lst)
             (last lst)
           nil)))

(defthm acl2-count-of-member-equal
  (<= (acl2-count (member-equal x lst))
      (acl2-count lst))
  :rule-classes :linear)

(defthm
  string-listp-of-resize-list
  (implies (and (string-listp lst)
                (stringp default-value))
           (string-listp (resize-list lst n default-value))))

(encapsulate
  ()

  (local
   (defthm
     update-nth-of-first-n-ac
     (implies
      (< (nfix key) (+ (nfix i) (len ac)))
      (equal
       (update-nth key val (first-n-ac i l ac))
       (if (< (nfix key) (len ac))
           (first-n-ac i l
                       (update-nth (- (len ac) (+ (nfix key) 1))
                                   val ac))
         (first-n-ac i
                     (update-nth (- (nfix key) (len ac))
                                 val l)
                     ac))))
     :hints (("goal" :induct (first-n-ac i l ac)
              :in-theory (enable update-nth-of-revappend)))))

  (defthm
    first-n-ac-of-update-nth
    (equal (first-n-ac i (update-nth key val l) ac)
           (if (< (nfix key) (nfix i))
               (update-nth (+ (nfix key) (len ac))
                           val (first-n-ac i l ac))
             (first-n-ac i l ac)))
    :hints
    (("goal" :induct (mv (first-n-ac i l ac)
                         (update-nth key val l))))))

(defthm take-of-update-nth
  (equal (take n (update-nth key val l))
         (if (< (nfix key) (nfix n))
             (update-nth key val (take n l))
           (take n l))))

(defthmd remember-that-time-with-update-nth-lemma-1
  (implies (and (equal (nfix key) (- (len l) 1))
                (true-listp l))
           (equal (revappend ac (update-nth key val l))
                  (append (first-n-ac key l ac)
                          (list val))))
  :hints (("goal" :induct (mv (first-n-ac key l ac)
                              (update-nth key val l))
           :expand ((len l) (len (cdr l))))))

(defthmd
  remember-that-time-with-update-nth
  (implies (and (equal (nfix key) (- (len l) 1))
                (true-listp l))
           (equal (update-nth key val l)
                  (append (take key l) (list val))))
  :hints
  (("goal"
    :use (:instance remember-that-time-with-update-nth-lemma-1
                    (ac nil)))))

(defthm append-of-take-and-cons
  (implies (and (natp n) (equal x (nth n l)))
           (equal (append (take n l) (cons x y))
                  (append (take (+ n 1) l) y)))
  :hints (("Goal" :induct (take n l)) ))

(defthmd take-of-nthcdr
  (equal (take n1 (nthcdr n2 l))
         (nthcdr n2 (take (+ (nfix n1) (nfix n2)) l))))

(defthm
  put-assoc-equal-without-change
  (implies (consp (assoc-equal x alist))
           (equal (put-assoc-equal x (cdr (assoc-equal x alist))
                                   alist)
                  alist)))

;; Contributed to books/std/lists/remove1-equal.lisp
(defthm member-equal-of-remove1-equal
  (implies (not (equal x1 x2))
           (iff (member-equal x1 (remove1-equal x2 l))
                (member-equal x1 l))))

(defthm
  member-of-intersection$
  (implies (or (not (member-equal x l1)) (not (member-equal x l2)))
           (not (member-equal x (intersection-equal l1 l2))))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (implies (not (member-equal x l1))
             (not (member-equal x (intersection-equal l1 l2)))))
   (:type-prescription
    :corollary
    (implies (not (member-equal x l2))
             (not (member-equal x (intersection-equal l1 l2)))))))

(defthm
  nth-of-intersection$
  (implies (< (nfix n)
              (len (intersection-equal l1 l2)))
           (and
            (member-equal (nth n (intersection-equal l1 l2))
                          l1)
            (member-equal (nth n (intersection-equal l1 l2))
                          l2)))
  :hints
  (("goal"
    :in-theory (disable member-of-intersection$)
    :use (:instance member-of-intersection$
                    (x (nth n (intersection-equal l1 l2)))))))

(defthm
  member-of-strip-cars-of-remove-assoc
  (iff
   (member-equal x1
                 (strip-cars (remove-assoc-equal x2 alist)))
   (and
    (member-equal x1 (strip-cars alist))
    (not (equal x1 x2)))))

(defthm
  no-duplicatesp-of-strip-cars-of-remove-assoc
  (implies (no-duplicatesp-equal (strip-cars alist))
           (no-duplicatesp-equal
            (strip-cars (remove-assoc-equal x alist)))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/take.lisp, from where it was taken with thanks.
(defthm take-fewer-of-take-more
  (implies (<= (nfix a) (nfix b))
           (equal (take a (take b x)) (take a x))))

(defthm len-of-remove-when-no-duplicatesp
  (implies (no-duplicatesp-equal l)
           (equal (len (remove-equal x l))
                  (if (member-equal x l)
                      (- (len l) 1)
                    (len l)))))

(defthm no-duplicatesp-of-remove
  (implies (no-duplicatesp-equal l)
           (no-duplicatesp-equal (remove-equal x l))))

(defthm assoc-of-car-when-member
  (implies (and (member-equal x lst) (alistp lst))
           (consp (assoc-equal (car x) lst))))

(encapsulate
  ()

  ;; The following is redundant with the eponymous function in
  ;; books/std/basic/inductions.lisp, from where it was taken with thanks.
  (local
   (defun dec-dec-induct (n m)
     (if (or (zp n)
             (zp m))
         nil
       (dec-dec-induct (- n 1) (- m 1)))))

  (local
   (defthm take-of-make-list-ac-lemma-1
     (implies (not (zp n1))
              (equal (cons val (make-list-ac (+ -1 n1) val nil))
                     (make-list-ac n1 val nil)))
     :hints (("Goal" :in-theory (disable cons-car-cdr make-list-ac)
              :use ((:instance cons-car-cdr
                               (x (make-list-ac n1 val nil))))))))

  (defthm take-of-make-list-ac
    (implies (<= (nfix n1) (nfix n2))
             (equal (take n1 (make-list-ac n2 val ac))
                    (make-list-ac n1 val nil)))
    :hints (("goal" :induct (dec-dec-induct n1 n2)))))

(defthm
  remove-assoc-when-absent
  (implies (and (alistp alist)
                (atom (assoc-equal x alist)))
           (equal (remove-assoc-equal x alist)
                  alist)))

(defthm stringp-of-append
  (equal (stringp (append x y)) (and (atom x) (stringp y))))

(defthm remove-assoc-equal-of-put-assoc-equal
  (equal (remove-assoc key (put-assoc name val alist))
         (if
             (equal key name)
             (remove-assoc key alist)
           (put-assoc name val (remove-assoc key alist)))))
