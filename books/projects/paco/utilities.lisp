(in-package "PACO")

; Note: Some function definitions in the Paco sources are
; accompanied by guards.  However, I ignore guards for the moment
; and the only reason these functions are guarded is that they
; happened to be guarded in the ACL2 source files and I see no
; reason to throw away the guards.  Guard verification is turned
; off during the processing of Paco sources.

;-----------------------------------------------------------------
; Section:  Basic Lisp Processing Functions and Predicates

(defun rev (x)
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defun alistp (l)
  (declare (xargs :guard t))
  (cond ((atom l) (eq l nil))
        (t (and (consp (car l)) (alistp (cdr l))))))

(defun symbol-alistp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (eq x nil))
        (t (and (consp (car x))
                (symbolp (car (car x)))
                (symbol-alistp (cdr x))))))

(defun assoc-eq (x alist)
  (declare (xargs :guard (if (symbolp x)
                             (alistp alist)
                           (symbol-alistp alist))))
  (cond ((endp alist) nil)
        ((eq x (car (car alist))) (car alist))
        (t (assoc-eq x (cdr alist)))))

(defun assoc-equal (x alist)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) nil)
        ((equal x (car (car alist))) (car alist))
        (t (assoc-equal x (cdr alist)))))

(defun member-equal (x lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((equal x (car lst)) lst)
        (t (member-equal x (cdr lst)))))

(defun keyword-value-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l) (null l))
        (t (and (keywordp (car l))
                (consp (cdr l))
                (keyword-value-listp (cddr l))))))

(defun evens (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) nil)
        (t (cons (car l)
                 (evens (cddr l))))))

(defun odds (l)
  (declare (xargs :guard (true-listp l)))
  (evens (cdr l)))

(defun symbol-listp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (eq lst nil))
        (t (and (symbolp (car lst))
                (symbol-listp (cdr lst))))))

(defun fix (x)
  (declare (xargs :guard t))
  (if (acl2-numberp x)
      x
    0))

(defun character-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l) (equal l nil))
        (t (and (characterp (car l))
                (character-listp (cdr l))))))

(defun make-character-list (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((characterp (car x))
         (cons (car x) (make-character-list (cdr x))))
        (t

; There's nothing special about (code-char 0), but at least it
; will look strange when people come across it.

         (cons (code-char 0) (make-character-list (cdr x))))))

(defun member-eq (x lst)
  (declare (xargs :guard (if (symbolp x)
                             (true-listp lst)
                           (symbol-listp lst))))
  (cond ((endp lst) nil)
        ((eq x (car lst)) lst)
        (t (member-eq x (cdr lst)))))

(defun union-eq (lst1 lst2)
  (declare (xargs :guard (and (symbol-listp lst1)
                              (true-listp lst2))))
  (cond ((endp lst1) lst2)
        ((member-eq (car lst1) lst2)
         (union-eq (cdr lst1) lst2))
        (t (cons (car lst1) (union-eq (cdr lst1) lst2)))))

(defun add-to-set-eq (x lst)
  (declare (xargs :guard (if (symbolp x)
                             (true-listp lst)
                           (symbol-listp lst))))
  (cond ((member-eq x lst) lst)
        (t (cons x lst))))

(defun subst-for-nth (new n lst)

; This substitutes the new for the nth element in lst (0 based).

  (cond ((zp n) (cons new (cdr lst)))
        (t (cons (car lst)
                 (subst-for-nth new (1- n) (cdr lst))))))

(defun no-duplicatesp-equal (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) t)
        ((member-equal (car l) (cdr l)) nil)
        (t (no-duplicatesp-equal (cdr l)))))

(defun set-difference-eq (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2)
                              (or (symbol-listp l1)
                                  (symbol-listp l2)))))
  (cond ((endp l1) nil)
        ((member-eq (car l1) l2)
         (set-difference-eq (cdr l1) l2))
        (t (cons (car l1) (set-difference-eq (cdr l1) l2)))))

(defun subsetp-eq (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y)
                              (or (symbol-listp x)
                                  (symbol-listp y)))))
  (cond ((endp x) t)
        ((member-eq (car x) y)
         (subsetp-eq (cdr x) y))
        (t nil)))

(defun set-difference-equal (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2))))
  (cond ((endp l1) nil)
        ((member-equal (car l1) l2)
         (set-difference-equal (cdr l1) l2))
        (t (cons (car l1) (set-difference-equal (cdr l1) l2)))))

(defun intersectp-eq (x y)
  (declare (xargs :guard (and (symbol-listp x)
                              (symbol-listp y))))
  (cond ((endp x) nil)
        ((member-eq (car x) y) t)
        (t (intersectp-eq (cdr x) y))))

(defun subsetp-equal (x y)
  (declare (xargs :guard (and (true-listp y)
                              (true-listp x))))
  (cond ((endp x) t)
        ((member-equal (car x) y)
         (subsetp-equal (cdr x) y))
        (t nil)))

(defun add-to-set-equal (x l)
  (declare (xargs :guard (true-listp l)))
  (cond ((member-equal x l)
         l)
        (t (cons x l))))

(defun union-equal (x y)
  (declare (xargs :guard (and (true-listp x) (true-listp y))))
  (cond ((endp x) y)
        ((member-equal (car x) y) (union-equal (cdr x) y))
        (t (cons (car x) (union-equal (cdr x) y)))))

(defun intersection-eq (l1 l2)
  (declare (xargs :guard
                  (and (symbol-listp l1)
                       (symbol-listp l2))))
  (cond ((endp l1) nil)
        ((member-eq (car l1) l2)
         (cons (car l1)
               (intersection-eq (cdr l1) l2)))
        (t (intersection-eq (cdr l1) l2))))

(defun remove1-eq (x lst)
  (cond ((endp lst) nil)
        ((eq x (car lst)) (cdr lst))
        (t (cons (car lst) (remove1-eq x (cdr lst))))))

(defun remove1-equal (x lst)
  (cond ((endp lst) nil)
        ((equal x (car lst)) (cdr lst))
        (t (cons (car lst) (remove1-equal x (cdr lst))))))

(defun remove1-assoc-eq (key alist)
  (declare (xargs :guard (if (symbolp key)
                             (alistp alist)
                           (symbol-alistp alist))))
  (cond ((endp alist) nil)
        ((eq key (caar alist)) (cdr alist))
        (t (cons (car alist) (remove1-assoc-eq key (cdr alist))))))

(defun strip-cadrs (x)
  (cond ((endp x) nil)
        (t (cons (cadar x) (strip-cadrs (cdr x))))))

(defun remove-duplicates-equal (x)
  (cond ((endp x) nil)
        ((member-equal (car x) (cdr x))
         (remove-duplicates-equal (cdr x)))
        (t (cons (car x)
                 (remove-duplicates-equal (cdr x))))))

(defun all-but-last (l)
  (cond ((endp l) nil)
        ((endp (cdr l)) nil)
        (t (cons (car l) (all-but-last (cdr l))))))

(defun last (l)
  (declare (xargs :guard (listp l)))
  (if (atom (cdr l))
      l
    (last (cdr l))))

(defun symbol< (x y)
  (declare (xargs :guard (and (symbolp x) (symbolp y))))
  (let ((x1 (symbol-name x))
        (y1 (symbol-name y)))
    (or (string< x1 y1)
        (and (equal x1 y1)
             (string< (symbol-package-name x)
                      (symbol-package-name y))))))

(defun alphorder (x y)
  (declare (xargs :guard t))
  (cond ((rationalp x)
         (cond ((rationalp y)
                (<= x y))
               (t t)))
        ((rationalp y) nil)
        ((complex-rationalp x)
         (cond ((complex-rationalp y)
                (or (< (realpart x) (realpart y))
                    (and (= (realpart x) (realpart y))
                         (<= (imagpart x) (imagpart y)))))
               (t t)))
        ((complex-rationalp y)
         nil)
        ((characterp x)
         (cond ((characterp y)
                (<= (char-code x)
                    (char-code y)))
               (t t)))
        ((characterp y) nil)
        ((stringp x)
         (cond ((stringp y)
                (and (string<= x y) t))
               (t t)))
        ((stringp y) nil)
        (t
         (cond ((symbolp x)
                (cond ((symbolp y)
                       (not (symbol< y x)))
                      (t t)))
               ((symbolp y) nil)
               (t (acl2::bad-atom<= x y))))))

(defun lexorder (x y)
  (declare (xargs :guard t))
  (cond ((atom x)
         (cond ((atom y)
                (alphorder x y))
               (t t)))
        ((atom y) nil)
        ((equal (car x) (car y))
         (lexorder (cdr x) (cdr y)))
        (t (lexorder (car x) (car y)))))

(defun kwote (x)
  (declare (xargs :guard t))
  (list 'quote x))


; We next develop the function that maps a natural number to its
; ``printed'' representation as a list of characters, e.g., 31415
; is mapped to (#\3 #\1 #\4 #\1 #\5).

(defun digit-to-char (n)
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n)
                              (<= n 9))))
  (case n
        (1 #\1)
        (2 #\2)
        (3 #\3)
        (4 #\4)
        (5 #\5)
        (6 #\6)
        (7 #\7)
        (8 #\8)
        (9 #\9)
        (otherwise #\0)))

; We'll need a few facts about floor and mod to admit the function
; that maps from numbers to their printed representation.

(local (include-book "ihs/ihs-lemmas" :dir :system))

(defthm justify-integer-floor-recursion

; To use this, be sure to disable acl2-count and floor.  If you
; leave acl2-count enabled, then prove a version of this
; appropriate to that setting.

  (implies
   (and (integerp i)
        (integerp j)
        (not (equal i 0))
        (not (equal i -1))
        (> j 1))
   (< (acl2-count (floor i j)) (acl2-count i)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable floor))))

; So here is the function we want.

(defun explode-nonnegative-integer (n ans)
  (declare (xargs :guard (and (integerp n)
                              (>= n 0))
                  :hints (("Goal"
                           :in-theory
                           (disable acl2-count floor)))))
  (cond ((zp n)
         (cond ((endp ans) '(#\0))
               (t ans)))
        (t (explode-nonnegative-integer
            (floor n 10)
            (cons (digit-to-char (mod n 10))
                  ans)))))

; We will eventually need to know that the printed
; representations of two numbers are identical iff the numbers
; are the same.  I found it too hard to deal with the accumulator
; above; I could not find a suitably general version of the lemma
; enni-uique, below, when the accumulator was around.  So I have
; decided to map from the efficient function
; explode-nonnegative-integer to a more elegant one.

(defun enni (n)
  (declare (xargs :hints
                  (("Goal"
                    :in-theory (disable acl2-count floor)))))
  (cond ((zp n) nil)
        (t (cons (digit-to-char (mod n 10))
                 (enni (floor n 10))))))

(defun enni-induct (i j)
  (declare (xargs :hints
                  (("Goal"
                    :in-theory (disable acl2-count floor)))))
  (cond ((zp i) nil)
        ((zp j) nil)
        (t (enni-induct (floor i 10) (floor j 10)))))

; Here's the basic uniqueness result vis-a-vis the printed
; representation (even though enni ``prints'' in the reverse
; order and ``prints'' 0 as the empty string of characters).

(defthm enni-unique
  (equal (equal (enni i) (enni j))
         (equal (nfix i) (nfix j)))

  :hints (("Goal" :induct (enni-induct i j))))

; So here is the explanation of the accumulator.

(defthm explode-nonnegative-integer-is-enni
  (equal (explode-nonnegative-integer n a)
         (append (rev (enni n))
                 (if (and (endp a) (zp n)) '(#\0) a)))

  :hints (("Goal" :in-theory (disable digit-to-char floor mod))))

; So now we must prove that explode-nonnegative-integer produces
; unique representations.  That is surprisingly hard, because of
; all the ways the append expression above can seem to identify
; results.  As an indication of how messy it is, consider how
; many lemmas I need about append, reverse, and enni below.  All
; of these are here simply to get the uniqueness result for
; explode-nonnegative-integer.

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm true-listp-append
  (equal (true-listp (append a b))
         (true-listp b)))

(defthm len-append
   (equal (len (append a b))
          (+ (len a) (len b))))

(defthm equal-len-0
   (equal (equal (len x) 0)
          (endp x)))

(defthm append-id-implies-endp
   (equal (equal (append x a) a)
          (endp x))
   :hints (("Goal"
            :use (:instance len-append (a x) (b a))
            :in-theory (disable len-append))))

(defun double-cdr-hint (x y)
   (cond ((endp x) t)
         ((endp y) t)
         (t (double-cdr-hint (cdr x) (cdr y)))))

(defthm equal-append-1
   (implies (and (true-listp a)
                 (true-listp b))
            (equal (equal (append a c)
                          (append b c))
                   (equal a b)))
   :hints (("Goal" :induct (double-cdr-hint a b))))

(defthm equal-append-2
   (equal (equal (append a b)
                 (append a c))
          (equal b c)))

(defthm equal-append-3
   (implies (and (true-listp a)
                 (true-listp b))
            (equal (equal (append a (list e))
                          (append b (list d)))
                   (and (equal a b)
                        (equal e d))))
   :hints (("Goal" :induct (double-cdr-hint a b))))

(defthm equal-append-singleton
   (equal (equal (append a b) (list e))
          (if (consp a)
              (and (equal (car a) e)
                   (endp (cdr a))
                   (null b))
            (equal b (list e)))))

(defthm consp-rev
   (equal (consp (rev x)) (consp x)))

(defthm true-listp-rev
   (true-listp (rev x))
   :rule-classes :type-prescription)

(defthm equal-rev
   (implies (and (true-listp a)
                 (true-listp b))
            (equal (equal (rev a)
                          (rev b))
                   (equal a b)))
   :hints (("Goal" :induct (double-cdr-hint a b))))

(defthm car-append
   (equal (car (append a b))
          (if (consp a) (car a) (car b))))

; Neat fact: The leading digit in the printed representation is
; #\0 only if the number is 0.

(defthm enni-minnie-zero
  (implies (not (zp i))
           (not (equal (car (rev (enni i))) #\0)))
  :hints (("Goal" :in-theory (disable floor mod))))

(defthm consp-enni
  (equal (consp (enni i)) (not (zp i))))

; And here is the uniqueness result we wanted.

(defthm explode-nonnegative-integer-unique
  (equal (equal (explode-nonnegative-integer i a)
                (explode-nonnegative-integer j a))
         (equal (nfix i) (nfix j)))

  :hints (("Goal" :in-theory (disable floor mod digit-to-char))))

(in-theory (disable explode-nonnegative-integer-is-enni))

(defun explode-atom (x)
  (declare (xargs :guard (or (acl2-numberp x)
                             (characterp x)
                             (stringp x)
                             (symbolp x))))
  (cond
   ((rationalp x)
    (cond ((integerp x)
           (cond
            ((< x 0)
             (cons #\- (explode-nonnegative-integer (- x) nil)))
            (t (explode-nonnegative-integer x nil))))
          (t (append
              (explode-atom (numerator x))
              (cons #\/ (explode-nonnegative-integer
                         (denominator x)
                         nil))))))
   ((complex-rationalp x)
    (list* #\# #\C #\(
           (append (explode-atom (realpart x))
                   (cons #\Space
                         (append (explode-atom (imagpart x))
                                 '(#\)))))))
   ((characterp x) (list x))
   ((stringp x) (coerce x 'list))
   (t (coerce (symbol-name x) 'list))))

(defun packn1 (lst)
  (cond ((endp lst) nil)
        (t (append (explode-atom (car lst))
                   (packn1 (cdr lst))))))

(defun packn (lst)
  (intern (coerce (packn1 lst) 'string)
          "ACL2"))

;-----------------------------------------------------------------
; Section: Records

(defun record-maker-function-name (name)
  (intern-in-package-of-symbol
   (coerce (append (coerce "Make " 'list)
                   (coerce (symbol-name name) 'list)
                   (coerce " record" 'list))
           'string)
   name))

(defun record-accessor-function-name (name field)
  (intern-in-package-of-symbol
   (coerce
    (append (coerce "Access " 'list)
            (coerce (symbol-name name) 'list)
            (coerce " record field " 'list)
            (coerce (symbol-name field) 'list))
    'string)
   name))

(defun record-changer-function-name (name)
  (intern-in-package-of-symbol
   (coerce
    (append (coerce "Change " 'list)
            (coerce (symbol-name name) 'list)
            (coerce " record fields" 'list))
    'string)
   name))

(defmacro make (&rest args)
  (cons (record-maker-function-name (car args)) (cdr args)))

(defmacro access (name rec field)
  (list (record-accessor-function-name name field)
        rec))

(defmacro change (&rest args)
  (cons (record-changer-function-name (car args)) (cdr args)))

(defun make-record-car-cdrs1 (lst var)
  (cond ((endp lst) var)
        (t (list (car lst)
                 (make-record-car-cdrs1 (cdr lst) var)))))

(defun make-record-car-cdrs (field-layout car-cdr-lst)
  (cond
   ((atom field-layout)
    (cond ((null field-layout) nil)
          (t (list (make-record-car-cdrs1 car-cdr-lst 'record)))))
   (t (append (make-record-car-cdrs (car field-layout)
                                    (cons 'car car-cdr-lst))
              (make-record-car-cdrs (cdr field-layout)
                                    (cons 'cdr car-cdr-lst))))))

(defun make-record-accessors (name field-lst car-cdrs)
  (cond
   ((endp field-lst) nil)
   (t
    (cons
     (list 'defmacro
           (record-accessor-function-name name (car field-lst))
           '(record)
           `(list 'let
                  (list (list 'record record))
                  ',(car car-cdrs)))
     (make-record-accessors name
                            (cdr field-lst)
                            (cdr car-cdrs))))))

(defun symbol-name-tree-occur (sym sym-tree)

; Sym is a symbol -- in fact, a keyword in proper usage -- and
; sym-tree is a tree of symbols.  We ask whether a symbol with
; the same symbol-name as key occurs in sym-tree.  If so, we
; return that symbol.  Otherwise we return nil.

  (cond ((symbolp sym-tree)
         (cond ((equal (symbol-name sym) (symbol-name sym-tree))
                sym-tree)
               (t nil)))
        ((atom sym-tree)
         nil)
        (t (or (symbol-name-tree-occur sym (car sym-tree))
               (symbol-name-tree-occur sym (cdr sym-tree))))))

(defun some-symbol-name-tree-occur (syms sym-tree)
  (cond ((endp syms) nil)
        ((symbol-name-tree-occur (car syms) sym-tree) t)
        (t (some-symbol-name-tree-occur (cdr syms) sym-tree))))

(defun make-record-changer-cons (fields field-layout x)

; Fields is the list of keyword field specifiers that are being
; changed.  Field-layout is the user's layout of the record.  X
; is the name of the variable holding the instance of the record.

  (cond ((not (some-symbol-name-tree-occur fields field-layout))
         x)
        ((atom field-layout)
         field-layout)
        (t
         (list 'cons
               (make-record-changer-cons fields
                                         (car field-layout)
                                         (list 'car x))
               (make-record-changer-cons fields
                                         (cdr field-layout)
                                         (list 'cdr x))))))

(defun make-record-changer-let-bindings (field-layout lst)

; Field-layout is the symbol tree provided by the user describing
; the layout of the fields.  Lst is the keyword/value list in a
; change form.  We want to bind each field name to the
; corresponding value.  The only reason we take field-layout as
; an argument is that we don't know from :key which package 'key
; is in.

  (cond
   ((endp lst) nil)
   (t (let ((var (symbol-name-tree-occur (car lst) field-layout)))
        (cons (list var (cadr lst))
              (make-record-changer-let-bindings field-layout
                                                (cddr lst)))))))

(defun make-record-changer-let (name field-layout rec lst)
  (declare (ignore name))
  (list 'let
        (cons (list 'record-changer-not-to-be-used-elsewhere rec)
              (make-record-changer-let-bindings field-layout lst))
        (make-record-changer-cons
         (evens lst)
         field-layout
         'record-changer-not-to-be-used-elsewhere)))

(defun make-record-changer (name field-layout)
  (list 'defmacro
        (record-changer-function-name name)
        '(&rest args)
        (list 'make-record-changer-let
              (kwote name)
              (kwote field-layout)
              '(car args)
              '(cdr args))))

(defun make-record-maker-cons (fields field-layout)

; Fields is the list of keyword field specifiers being
; initialized in a record.  Field-layout is the user's
; specification of the layout.  We lay down a cons tree
; isomorphic to field-layout whose tips are either the
; corresponding tip of field-layout or nil according to whether
; the keyword corresponding to the field-layout tip is in fields.

  (cond ((atom field-layout)
         (cond ((some-symbol-name-tree-occur fields field-layout)

; The above call is a little strange isn't it?  Field-layout is
; an atom, a symbol really, and here we are asking whether any
; element of fields symbol-name-tree-occurs in it.  We're really
; just exploiting some-symbol-name-tree-occur to walk down fields
; for us taking the symbol-name of each element and seeing if it
; occurs in (i.e., in this case, is) the symbol name of
; field-layout.

                field-layout)
               (t nil)))
        (t
         (list 'cons
               (make-record-maker-cons fields
                                       (car field-layout))
               (make-record-maker-cons fields
                                       (cdr field-layout))))))

(defun make-record-maker-let (name field-layout lst)
  (declare (ignore name))
  (list 'let (make-record-changer-let-bindings field-layout lst)
        (make-record-maker-cons (evens lst)
                                field-layout)))

(defun make-record-maker (name field-layout)
  (list 'defmacro
        (record-maker-function-name name)
        '(&rest args)
        (list 'make-record-maker-let
              (kwote name)
              (kwote field-layout)
              'args)))

(defun make-record-field-lst (field-layout)
  (cond ((atom field-layout)
         (cond ((null field-layout) nil)
               (t (list field-layout))))
        (t (append (make-record-field-lst (car field-layout))
                   (make-record-field-lst (cdr field-layout))))))

(defun record-macros (name field-layout)
  (cons 'progn
        (append
         (make-record-accessors name
                                (make-record-field-lst field-layout)
                                (make-record-car-cdrs field-layout
                                                      nil))
         (list (make-record-changer name field-layout)
               (make-record-maker name field-layout)))))

; WARNING: If you change the layout of records, you must change
; certain functions that build them in.  Generally, these
; functions are defined before defrec was defined, but need to
; access components.  See the warning associated with defrec
; rewrite-constant for a list of one group of such functions.
; You might also search for occurrences of the word defrec prior
; to this definition of it.

(defmacro defrec (name field-lst)
  (record-macros name field-lst))

; ----------------------------------------------------------------
; Section: Property lists

(defun worldp (alist)
  (declare (xargs :guard t))
  (cond ((atom alist) (eq alist nil))
        (t
         (and (consp (car alist))
              (symbolp (car (car alist)))
              (consp (cdr (car alist)))
              (symbolp (cadr (car alist)))
              (worldp (cdr alist))))))

(defconst *acl2-property-unbound* :acl2-property-unbound)

(defun getprop (symb key default alist)
  (declare (xargs :guard (and (symbolp symb)
                              (symbolp key)
                              (worldp alist))))

; In the PSIM world, we would prefer for this function,
; paco::getprop, to be defined as shown below.  We call this the
; ``slow version.''
#|
  (cond ((endp alist) default)
        ((and (eq symb (caar alist))
              (eq key (cadar alist)))
         (let ((ans (cddar alist)))
           (if (eq ans *acl2-property-unbound*)
               default
               ans)))
        (t (getprop symb key default (cdr alist))))|#

; However, for purposes of testing before PSIM is complete, it is
; nice to assume that the world alist has been installed under
; the name paco::paco.  If that is true, this function is much
; faster but is still equivalent to the slow version above.  We
; arrange for the acl2::db function to install the Paco world it
; creates.  See database.lisp.

  (acl2::getprop symb key default 'paco::paco alist))

(defun global-val (symb alist)
  (getprop symb 'global-value nil alist))

; ----------------------------------------------------------------
; Section Balanced Binary-Trees

; We only need two features of balanced binary trees: how to
; build one from a list of numbers and how to ask whether a
; number is in the resulting tree.  We are content to reconstruct
; the tree from scratch when we need to insert or delete an
; element.  So we don't implement insertion, deletion, or
; dyanamic re-balancing.

(defun in-btreep (n btree)
  (cond ((atom btree) (equal n btree))
        ((< n (car btree)) (in-btreep n (cadr btree)))
        ((> n (car btree)) (in-btreep n (cddr btree)))
        (t t)))

(defun btree-contents (btree)

; Return the list containing the numbers in btree.

  (cond ((atom btree)
         (if (null btree) nil (list btree)))
        (t (append (btree-contents (cadr btree))
                   (cons (car btree)
                         (btree-contents (cddr btree)))))))

; To build a btree, we sort the list of numbers into ascending
; order, split the list into a middle pivot element and two
; almost equal length halves and recursively build the subtrees
; around that pivot.

(defun merge-ascending (l1 l2)
  (declare (xargs :measure (+ (acl2-count l1) (acl2-count l2))))
  (cond ((endp l1) l2)
        ((endp l2) l1)
        ((<= (car l1) (car l2))
         (cons (car l1) (merge-ascending (cdr l1) l2)))
        (t (cons (car l2) (merge-ascending l1 (cdr l2))))))

(defthm acl2-count-evens
  (implies (consp (cdr x))
           (< (acl2-count (evens x)) (acl2-count x))))

; This is the merge sort function.

(defun merge-sort-ascending (l)
  (cond ((endp (cdr l)) l)
        (t (merge-ascending (merge-sort-ascending (evens l))
                            (merge-sort-ascending (odds l))))))

(defun find-pivot1 (lst x)
  (cond ((endp (cdr x)) nil)
        (t (cons (car lst) (find-pivot1 (cdr lst) (cddr x))))))

(defun find-pivot2 (lst x)
  (cond ((endp (cdr x)) lst)
        (t (find-pivot2 (cdr lst) (cddr x)))))

(defun find-pivot (lst)

; Lst is ordered.  We split it into (mv first-part pivot
; last-part).

  (cond ((endp lst) (mv nil nil nil))
        ((endp (cdr lst)) (mv nil (car lst) nil))
        (t (let ((lst1 (find-pivot1 lst lst))
                 (lst2 (find-pivot2 lst lst)))
             (mv lst1 (car lst2) (cdr lst2))))))

(defthm len-find-pivot1
  (implies (and (consp lst)
                (consp x)
                (<= (len x) (len lst)))
           (< (len (find-pivot1 lst x))
              (len lst)))
  :rule-classes :linear)

(defthm len-find-pivot2
  (implies (and (consp lst)
                (consp (cdr x)))
           (< (len (find-pivot2 lst x))
              (len lst)))
  :rule-classes :linear)

(defun make-btree1 (lst)
  (declare (xargs :measure (len lst)
                  :hints (("Subgoal 2"
                           :use (:instance len-find-pivot2
                                           (lst lst)
                                           (x lst))))))
  (cond ((endp lst) nil)
        ((endp (cdr lst)) (car lst))
        (t (mv-let (lst1 n lst2)
                   (find-pivot lst)
                   (cons n
                         (cons (make-btree1 lst1)
                               (make-btree1 lst2)))))))

(defun make-btree (lst)

; It is assumed lst has no duplicates in it.  This function
; actually works if there are duplications, but duplications make
; the search less efficient.

  (make-btree1 (merge-sort-ascending lst)))

