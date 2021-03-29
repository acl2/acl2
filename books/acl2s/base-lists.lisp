#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")

(include-book "defdata/top" :ttags :all)
(include-book "std/lists/top" :dir :system)

; Pete 9/27/2018: Include utilities book
(include-book "definec" :ttags :all)
(include-book "check-equal")

(include-book "acl2s/ccg/ccg" :dir :system 
  :uncertified-okp nil :ttags ((:ccg))
  :load-compiled-file nil)

(set-termination-method :ccg)

(local (set-defunc-timeout 1000))

; Pete 9/14/2018: I am enabling some of the functions that
; std/lists/top disables, since this causes problems where simple
; theorems do not getting proved.

(in-theory (enable
            true-listp
            len
            append
            rev
            revappend
            no-duplicatesp-equal
            make-character-list
            nthcdr
            subseq-list
            resize-list
            last
            butlast
            remove
            member
            subsetp
            intersectp
            union-equal
            set-difference-equal
            intersection-equal))

(add-macro-fn tlp true-listp)

(defmacro tl-fix (x)
  `(acl2::true-list-fix ,x))

(add-macro-fn tl-fix acl2::true-list-fix)

(definec bin-app (x :tl y :tl) :tl
  (append x y))

(make-n-ary-macro app bin-app nil t)

(add-macro-fn app binary-append)
(add-macro-fn app bin-app)

; shorthand for equal
(defmacro == (x y)
  `(equal ,x ,y))

; shorthand for not equal
(defmacro =/= (x y)
  `(not (equal ,x ,y)))

; shorthand for not equal
(defmacro != (x y)
  `(not (equal ,x ,y)))

; shorthand for implies
(defmacro => (x y)
  `(implies ,x ,y))

; shorthand for not
(defmacro ! (x)
  `(not ,x))

; shorthand for and 
(defmacro ^ (&rest args)
  (and-macro args))

; shorthand for or
(defmacro v (&rest args)
  (or-macro args))

#|

Useful for testing defunc/definec errors

:trans1
(definec in (a :all X :tl) :bool
  (and (consp X)
       (or (== a (car X))
           (in a (cdr X)))))

:trans1
(DEFINEC-CORE IN NIL (A :ALL X :TL)
  :BOOL (AND (CONSP X)
             (OR (== A (CAR X)) (IN A (CDR X)))))

(redef+)
(redef-)

|#

(definec in (a :all X :tl) :bool
  (and (consp X)
       (or (== a (car X))
           (in a (cdr X)))))

(definec nin (a :all X :tl) :bool
  (not (in a X)))

(defdata non-empty-true-list (cons all true-list))

(defdata-alias ne-tl non-empty-true-list)

(add-macro-fn ne-tlp non-empty-true-listp)

; left and right are strict versions of car and cdr, i.e., they can
; only be applied to conses.
(definec left (x :cons) :all 
  (car x))

(definec right (x :cons) :all
  (cdr x))

; head and tail are versions of car and cdr that are applied to only
; true-lists and they are also strict, so the true-lists have to be
; conses.
(definec head (x :ne-tl) :all
  (car x))

(definec tail (x :ne-tl) :tl 
  (cdr x))

(definec lcons (x :all y :tl) :ne-tl 
  (cons x y))

; a strict version of nth requiring that the list have at least n+1
; elements (since we use 0 indexing)
(definec lnth (n :nat l :tl) :all
  :pre (< n (len l))
  (nth n l))

(check= (lnth 2 '(0 1 2 3)) 2)

; a strict version of nthcdr, requiring that we have at least n
; elements ((nthcdr 0 l) is the identity)
(definec lnthcdr (n :nat l :tl) :tl
  :pre (<= n (len l))
  (nthcdr n l))

(check= (lnthcdr 2 '(0 1 2 3)) '(2 3))

; The definitions below are used to define gen-car-cdr-macros.
(defdata str-all (list string all))
(defdata l-str-all (listof str-all))

(definec-no-test gen-car-cdr-aux-1
  (car :var cdr :var carstr :string cdrstr :string res :l-str-all) :l-str-all
  (if (endp res)
      res
    (b* ((e (first res))
         (str (first e))
         (exp (second e)))
      (list* `(,(str::cat carstr str)
               `(,',car ,,exp))
             `(,(str::cat cdrstr str)
               `(,',cdr ,,exp))
             (gen-car-cdr-aux-1 car cdr carstr cdrstr (cdr res))))))

(check= (gen-car-cdr-aux-1 'head 'tail "h" "t" '(("" x)))
        `(("h" `(head ,x))
          ("t" `(tail ,x))))

; The termination hint isn't need, but it saves 10 seconds and I
; certify this file enough that it is worth annotating.
(definec-no-test gen-car-cdr-aux
  (car :var cdr :var carstr :string cdrstr :string depth :nat res :l-str-all) :l-str-all
  (declare (xargs :consider-only-ccms (depth)))
  (cond ((endp res) (gen-car-cdr-aux
                     car
                     cdr
                     carstr
                     cdrstr
                     depth
                     `(("" x))))
        ((== depth 0) res)
        (t (app (if (consp (cdr res)) res nil)
                (gen-car-cdr-aux
                 car
                 cdr
                 carstr
                 cdrstr
                 (1- depth)
                 (gen-car-cdr-aux-1 car cdr carstr cdrstr res))))))

(check= (gen-car-cdr-aux 'head 'tail "h" "t" 1 nil)
        `(("h" `(head ,x))
          ("t" `(tail ,x))))

(check= (gen-car-cdr-aux 'head 'tail "h" "t" 2 nil)
        `(("h" `(head ,x))
          ("t" `(tail ,x))
          ("hh" `(head (head ,x)))
          ("th" `(tail (head ,x)))
          ("ht" `(head (tail ,x)))
          ("tt" `(tail (tail ,x)))))

(definec gen-car-cdr-defs-fn
  (l :l-str-all prefix :string suffix :string pkg :string) :all
  :pre (!= pkg "")
  (if (endp l)
      l
    (b* ((mname (defdata::s+ (str::cat prefix (caar l) suffix) :pkg pkg))
         (x (fix-intern$ "X" pkg)))
      (cons 
       `(defmacro ,mname (,x)
          ,(cadar l))
       (gen-car-cdr-defs-fn (cdr l) prefix suffix pkg)))))

(definec gen-car-cdr-macros-fn
  (car :var cdr :var carstr :string cdrstr :string prefix :string
       suffix :string depth :nat pkg :string) :all
  :pre (!= pkg "")
  :skip-tests t
  (let ((l (gen-car-cdr-aux car cdr carstr cdrstr depth nil)))
    `(encapsulate
      ()
      ,@(gen-car-cdr-defs-fn l prefix suffix pkg))))

(check=
 (gen-car-cdr-macros-fn 'head 'tail "A" "D" "LC" "R" 2 "ACL2S")
 `(encapsulate
   nil
   (defmacro lcar (x) `(head ,x))
   (defmacro lcdr (x) `(tail ,x))
   (defmacro lcaar (x) `(head (head ,x)))
   (defmacro lcdar (x) `(tail (head ,x)))
   (defmacro lcadr (x) `(head (tail ,x)))
   (defmacro lcddr (x) `(tail (tail ,x)))))

(defmacro gen-car-cdr-macros
  (car cdr carstr cdrstr prefix suffix depth)
  `(make-event
    (gen-car-cdr-macros-fn
     ',car ',cdr ,carstr ,cdrstr ,prefix ,suffix ,depth
     (current-package state))))

(gen-car-cdr-macros head tail "A" "D" "LC" "R" 4)

; Generates the following redundant events, where "s" means "strict":


(defmacro lcar (x) `(head ,x))
(defmacro lcdr (x) `(tail ,x))

(defmacro lcaar (x) `(head (head ,x)))
(defmacro lcadr (x) `(head (tail ,x)))
(defmacro lcdar (x) `(tail (head ,x)))
(defmacro lcddr (x) `(tail (tail ,x)))

(defmacro lcaaar (x) `(head (head (head ,x))))
(defmacro lcaadr (x) `(head (head (tail ,x))))
(defmacro lcadar (x) `(head (tail (head ,x))))
(defmacro lcaddr (x) `(head (tail (tail ,x))))
(defmacro lcdaar (x) `(tail (head (head ,x))))
(defmacro lcdadr (x) `(tail (head (tail ,x))))
(defmacro lcddar (x) `(tail (tail (head ,x))))
(defmacro lcdddr (x) `(tail (tail (tail ,x))))

(defmacro lcaaaar (x) `(head (head (head (head ,x)))))
(defmacro lcaaadr (x) `(head (head (head (tail ,x)))))
(defmacro lcaadar (x) `(head (head (tail (head ,x)))))
(defmacro lcaaddr (x) `(head (head (tail (tail ,x)))))
(defmacro lcadaar (x) `(head (tail (head (head ,x)))))
(defmacro lcadadr (x) `(head (tail (head (tail ,x)))))
(defmacro lcaddar (x) `(head (tail (tail (head ,x)))))
(defmacro lcadddr (x) `(head (tail (tail (tail ,x)))))
(defmacro lcdaaar (x) `(tail (head (head (head ,x)))))
(defmacro lcdaadr (x) `(tail (head (head (tail ,x)))))
(defmacro lcdadar (x) `(tail (head (tail (head ,x)))))
(defmacro lcdaddr (x) `(tail (head (tail (tail ,x)))))
(defmacro lcddaar (x) `(tail (tail (head (head ,x)))))
(defmacro lcddadr (x) `(tail (tail (head (tail ,x)))))
(defmacro lcdddar (x) `(tail (tail (tail (head ,x)))))
(defmacro lcddddr (x) `(tail (tail (tail (tail ,x)))))

(gen-car-cdr-macros head tail "A" "D" "LC" "R" 4)

#|

 Generates the following macros, where "l" means true-list :

 lcar:  (head x)
 lcdr:  (tail x)
 lcaar: (head (head x))
 lcadr: (head (tail x))

 ...

 lcddddr: (tail (tail (tail (tail x))))

|#

; strict versions of first, ..., tenth: we require that x is a tl
; with enough elements
(defmacro lfirst   (x) `(lcar ,x))
(defmacro lsecond  (x) `(lcadr ,x))
(defmacro lthird   (x) `(lcaddr ,x))
(defmacro lfourth  (x) `(lcadddr ,x))
(defmacro lfifth   (x) `(lcar (lcddddr ,x)))
(defmacro lsixth   (x) `(lcadr (lcddddr ,x)))
(defmacro lseventh (x) `(lcaddr (lcddddr ,x)))
(defmacro leighth  (x) `(lcadddr (lcddddr ,x)))
(defmacro lninth   (x) `(lcar (lcddddr (lcddddr ,x))))
(defmacro ltenth   (x) `(lcadr (lcddddr (lcddddr ,x))))

; A forward-chaining rule to deal with the relationship
; between len and cdr.

(defthm expand-len-with-trigger-cdr
  (implies (and (<= c (len x))
                (posp c))
           (<= (1- c) (len (cdr x))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((< (len x) c) (cdr x)))))

(defthm len-non-nil-with-trigger-cdr
  (implies (and (<= c (len x))
                (posp c))
           x)
  :rule-classes ((:forward-chaining :trigger-terms ((< (len x) c)))))

#|

 This may be useful. I started with this, but used the above rule
 instead.

 (defthm exp-len1
   (implies (and (syntaxp (quotep c))
                 (syntaxp (< (second c) 100))
 		 (posp c)
 		 (<= c (len x)))
            (<= (1- c) (len (cdr x))))
   :rule-classes ((:forward-chaining :trigger-terms ((< (len x) c)))))

 (defthm exp-len2
   (implies (and (syntaxp (quotep c))
                 (syntaxp (< (second c) 100))
 		 (posp c)
 		 (<= c (len x)))
	    x)
   :rule-classes ((:forward-chaining :trigger-terms ((< (len x) c)))))

|#

#|

 A collection of forward-chaining rules that help with reasoning about
 conses with car, cdr, head, tail, left, right.

|#

(defthm cddr-implies-cdr-trigger-cddr
  (implies (cddr x)
	   (cdr x))
  :rule-classes ((:forward-chaining :trigger-terms ((cddr x)))))

(defthm tlp-implies-tlpcdr-trigger-cdr
  (implies (true-listp x)
	   (true-listp (cdr x)))
  :rule-classes ((:forward-chaining :trigger-terms ((cdr x)))))

(defthm tlp-consp-cdr-implies-tail-trigger-tail
  (implies (and (true-listp x)
		(consp (cdr x)))
	   (tail x))
  :rule-classes ((:forward-chaining :trigger-terms ((tail x)))))

(defthm tlp-consp-implies-tlp-tail-trigger-tail
  (implies (and (true-listp x) x)
	   (true-listp (tail x)))
  :rule-classes ((:forward-chaining :trigger-terms ((tail x)))))

(defthm consp-cdr-implies-right-trigger-right
  (implies (consp (cdr x))
	   (right x))
  :rule-classes ((:forward-chaining :trigger-terms ((right x)))))

(defthm tlp-consp-implies-tlp-right-trigger-right
  (implies (and (true-listp x) x)
	   (true-listp (right x)))
  :rule-classes ((:forward-chaining :trigger-terms ((right x)))))

; Basic left-right theorems
(defthm left-cons
  (equal (left (cons x y))
         x))

(defthm right-cons
  (equal (right (cons x y))
         y))

(defthm left-consp
  (implies (force (consp x))
           (equal (left x) (car x))))

(defthm right-consp
  (implies (force (consp x))
           (equal (right x) (cdr x))))

; Basic head-tail theorems
(defthm head-cons
  (implies (force (tlp y))
           (equal (head (cons x y))
                  x)))

(defthm tail-cons
  (implies (force (tlp y))
           (equal (tail (cons x y))
                  y)))

(defthm head-consp
  (implies (and (force (tlp x)) (force x))
           (equal (head x) (car x))))

(defthm tail-consp
  (implies (and (force (tlp x)) (force x))
           (equal (tail x) (cdr x))))

; Disable tail, head, left, right so that it is easier to debug
; proofs
(in-theory (disable tail tail-definition-rule
                    head head-definition-rule
                    left left-definition-rule
                    right right-definition-rule))

#||

 Suppose I want to define a datatype corresponding to a non-empty list of
 integers that ends with a natural number. Here's one way to do that.

 (defdata loin (oneof (list nat)
                      (cons integer loin)))

 By defining the snoc constructor, we can instead 

 (defdata loi (listof int))
 (defdata loins (snoc loi nat))

 (defdata-equal-strict loin loins)

||#

(definec snoc (l :tl e :all) :ne-tl
  (append l (list e)))

(defmacro lsnoc (l e)
  `(snoc ,l ,e))

(definec snocl (l :ne-tl) :tl
  (butlast l 1))

(definec snocr (l :ne-tl) :all
  (car (last l)))

(register-data-constructor
 (ne-tlp snoc)
 ((tlp snocl) (allp snocr))
 :rule-classes nil
 :proper nil)

(definec lendp (x :tl) :bool
  (atom x))

(definec llen (x :tl) :nat
  (len x))

(definec lrev (x :tl) :tl
  (rev x))

