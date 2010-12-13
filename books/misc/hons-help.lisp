;   hons-help.lisp                                Boyer & Hunt

(in-package "ACL2")
(include-book "gentle")
(set-state-ok t)


; In this file one may find some helpful functions and lemmas in the "HONS
; School", but none of them require "under the hood" definitions.  That is, the
; "user" could do all this by himself.



(defmacro all-memoized-fns (&optional show-conditions)
  (if show-conditions
      '(table-alist 'memoize-table (w state))
    '(strip-cars (table-alist 'memoize-table (w state)))))



; FAST ALIST UTILITIES -----------------------------------------------------

(defn make-fal (al name)
  ":Doc-Section Hons-and-Memoization

  Make a fast alist out of an alist~/

  (MAKE-FAL al name) copies the alist AL with hons-acons
  to make a fast alist that ends with NAME.~/~/"

  (cond ((atom al)
         name)
        ((atom (car al))
         (make-fal (cdr al) name))
        (t
         (hons-acons (caar al)
                     (cdar al)
                     (make-fal (cdr al) name)))))

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


; [Jared]: Removing ansfl1 since I think we don't use it?

;; (defmacro ansfl1 (x)
;;   `((lambda (ansfl1-do-not-use-elsewhere1)
;;       ((lambda (ansfl1-do-not-use-elsewhere1
;;                 ansfl1-do-not-use-elsewhere2)
;;          (declare (ignore ansfl1-do-not-use-elsewhere2))
;;         ansfl1-do-not-use-elsewhere1)))
;;     ,x))

(defmacro ansfl-list (l x)

; (ansfl-list (a b c ...) x) -- frees a, b, c, ..., returns x

  (if (atom l)
      x
    `(ansfl (ansfl-list ,(cdr l) ,x)
            ,(car l))))


(defn ansfl-last-list (r bindings)

; [Jared]: BOZO please document this.  It's used in het*.

; bindings is an alist.  in het* the bindings are names being bound
; like in a let*.
;
; all of the names being bound are freed, then we return r.

  (if (atom bindings)
      r
    `(ansfl ,(ansfl-last-list r (gentle-cdr bindings))
            ,(gentle-caar bindings))))

(defmacro het* (bindings &rest r)

; This implementation of het* is somewhat defective in that it is
; incapable of returning multiple values.  We cannot see how to fix
; it.

; this is basically let*, but we try to fast-alist-free everything that gets
; bound.  which works out, in a weird kind of way, for anything that
; isn't a fast alist anyway, but is really pretty gross.

  `(let* ,bindings
     ,@(butlast r 1)
     ,(ansfl-last-list (car (last r)) bindings)))

(defmacro with-fast-list (var term name form)

; bind a variable to a fast-alist created by binding every element of term to t,
; with the final name name.  then run form and free var.

  `(let ((,var (hons-put-list
                ,term
                t
                ,name)))
     (ansfl ,form ,var)))


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
    (let* ((cp          (consp values))
           (val         (if cp (car values) values))
           (next-values (if cp (cdr values) values))
           (old-pair    (hons-get (car keys) l))
           (redundant   (and old-pair (hons-equal val (cdr old-pair))))
           (next-l      (if redundant l (hons-acons (car keys) val l))))
      (hons-put-list (cdr keys) next-values next-l))))




; LIST OPERATIONS USING HONS -----------------------------------------------

(defn hons-binary-append (x y)
  (mbe :logic (append x y)
       :exec (if (atom x)
                 y
               (hons (car x)
                     (hons-binary-append (cdr x) y)))))

(defmacro hons-append (x y &rest rst)
  "APPEND using HONS instead of CONS"
  (xxxjoin 'hons-binary-append (cons x (cons y rst))))

(defn hons-revappend (x y)
  "REVAPPEND using HONS instead of CONS"
  (mbe :logic (revappend x y)
       :exec (if (atom x)
                 y
               (hons-revappend (cdr x) (hons (car x) y)))))

(defn hons-reverse (x)
  "REVERSE using HONS instead of CONS"
  (mbe :logic (reverse x)
       :exec (if (stringp x)
                 (reverse x)
               (hons-revappend x nil))))

(defmacro hons-list (&rest x)
  "(LIST ...) using HONS instead of CONS"
  (if (atom x)
      nil
    (list 'hons (car x) (cons 'hons-list (cdr x)))))

(defmacro hons-list* (&rest x)
  "(LIST* ...) using HONS instead of CONS"
  (cond ((atom x)
         x)
        ((atom (cdr x))
         (car x))
        (t
         (list 'hons (car x) (cons 'hons-list* (cdr x))))))

(defn hons-make-list-acc (n val ac)
  ":Doc-Section Hons-and-Memoization

  ~c[(HONS-MAKE-LIST-ACC n obj acc)] honses obj onto acc N times.
  Equal to (hons-append (make-list n :initial-element n) e).~/~/~/"

  (mbe :logic (make-list-ac n val ac)
       :exec (if (not (posp n))
                 ac
               (hons-make-list-acc (1- n) val (hons val ac)))))

(defmacro hons-make-list (size &key initial-element)
  ":Doc-Section Hons-and-Memoization
  Like ~ilc[make-list], but produces honses.~/~/~/"

  `(hons-make-list-acc ,size ,initial-element nil))




; LIST OPERATIONS USING HONS-EQUAL -----------------------------------------

(defn hons-member-equal (x y)
  "MEMBER-EQUAL using HONS-EQUAL for each equality check"

; [Jared]: BOZO this is exactly the same as gentle-member-equal.  Why duplicate
; it?  Well, maybe gentle-member-equal should actually be changed to use equal,
; and this function should be left alone.

  (mbe :logic (member-equal x y)
       :exec (cond ((atom y) nil)
                   ((hons-equal x (car y)) y)
                   (t (hons-member-equal x (cdr y))))))




; FAST DUPLICATE CHECKING AND REMOVAL --------------------------------------

(defn hons-dups-p1 (l tab)
  "Basic duplicates check; table is a fast alist that associates already-seen
   elements with t."
  (cond ((atom l)
         (ansfl nil tab))
        ((hons-get (car l) tab)
         (ansfl l tab))
        (t
         (hons-dups-p1 (cdr l)
                       (hons-acons (car l) t tab)))))

(defn hons-dups-p (l)

; If L has no duplicate members, then (HONS-DUPS-P L) is NIL.  If L
; has equal members, then (HONS-DUPS-P l) returns the second tail of L
; whose CAR is the first member of L that occurs twice in L.

; [Jared]: BOZO stylistically, would it be better to free the table in this
; function, rather than in hons-dups-p1?

  (hons-dups-p1 l '*hons-dups-p*))

(defn hons-duplicates1 (l tab)
  (cond ((atom l) (ansfl nil tab))
        ((hons-get (car l) tab)
         (cons (car l) (hons-duplicates1 (cdr l) tab)))
        (t (hons-duplicates1 (cdr l) (hons-acons (car l) t tab)))))

(defn hons-duplicates (l)
  (hons-duplicates1 l nil))
         


(defn hons-remove-duplicates1 (l tab)
  (cond ((atom l)
         (ansfl nil tab))
        ((hons-get (car l) tab)
         (hons-remove-duplicates1 (cdr l) tab))
        (t
         (cons (car l)
               (hons-remove-duplicates1 (cdr l)
                                        (hons-acons (car l) t tab))))))

(defn hons-remove-duplicates (l)

; preserves order, deleting later occurrences

  (hons-remove-duplicates1 l '*hons-remove-duplicates*))




; SUBLIS WITH FAST ALISTS AND MEMOIZATION ----------------------------------

(defun hons-sublis-aux (fal x)
  (declare (xargs :guard t))
  (if (atom x)
      (let ((pair (hons-get x fal)))
        (if pair (cdr pair) x))
    (cons (hons-sublis-aux fal (car x))
          (hons-sublis-aux fal (cdr x)))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (alistp x)
                   (equal (hons-assoc-equal a x)
                          (assoc a x)))
          :hints(("Goal" :induct (len x)))))

 (defthm hons-sublis-aux-removal
   (implies (alistp fal)
            (equal (hons-sublis-aux fal x)
                   (sublis fal x)))))

(make-event
 (if (hons-enabledp state)
     '(memoize 'hons-sublis-aux :condition '(consp x))
   '(value-triple :skipping-memoization)))

(defun hons-sublis (fal x)

  ":Doc-Section Hons-and-Memoization
   Memoized version of SUBLIS which uses fast-alists.~/~/

   ~c[(hons-sublis fal x)] is like ~il[sublis], but may be faster in two
   ways.

   1. It uses ~il[hons-get] instead of ~il[assoc], which may provide a speedup
   when the alist in question is very long.  Note that for good performance, the
   fast-alist argument, ~c[fal], must be a valid fast-alist.

   2. It uses a memoized auxiliary function, which may provide a speedup when
   the tree argument, ~c[x], contains large, shared structures.
   ~/"

  (declare (xargs :guard t))
  (let ((ret (hons-sublis-aux fal x)))
    (prog2$
     (clear-memoize-table 'hons-sublis-aux)
     ret)))

(defthm hons-sublis-removal
  (implies (alistp fal)
           (equal (hons-sublis fal x)
                  (sublis fal x))))




; SET OPERATIONS USING HONS ------------------------------------------------

; Some "fast" operations for "set" intersection, union, and set-diff
; intended for use on lists of ACL2 objects without duplications.

(defconst *magic-number-for-hashing*

  18

  ":Doc-Section Hons-and-Memoization

  Assoc is sometimes faster than gethash.~/

  Lisp folklore says it is faster to use ASSOC than GETHASH on a list
  if the list has length 18 or less.~/~/")

(defun worth-hashing1 (l n)
  (declare (type (integer 0 18) n)
           (xargs :guard t))
  (cond ((eql n 0) t)
        ((atom l) nil)
        (t (worth-hashing1 (cdr l) (the (integer 0 18)
                                     ;; 18 is a *magic-number*
                                     (1- n))))))

(defn worth-hashing (l)
  (worth-hashing1 l *magic-number-for-hashing*))

; [Jared] BOZO it would be nice to prove these equivalent to simple set
; operations with no fast alist stuff.

(defn hons-int1 (l1 al2)
  (cond ((atom l1)
         nil)
        ((hons-get (car l1) al2)
         (cons (car l1) (hons-int1 (cdr l1) al2)))
        (t
         (hons-int1 (cdr l1) al2))))

(defn hons-intersection2 (l1 l2)
  (cond ((atom l1)
         nil)
        ((hons-member-equal (car l1) l2)
         (cons (car l1) (hons-intersection2 (cdr l1) l2)))
        (t
         (hons-intersection2 (cdr l1) l2))))

(defn hons-intersection (l1 l2)  ; preserves order of members in l1
  (cond ((worth-hashing l2)
         (with-fast-list fl2 l2 '*hons-intersection-alist*
                         (hons-int1 l1 fl2)))
        (t
         (hons-intersection2 l1 l2))))

(defn hons-intersect-p1 (l1 al2)
  (cond ((atom l1) 
         nil)
        ((hons-get (car l1) al2)
         t)
        (t
         (hons-intersect-p1 (cdr l1) al2))))

(defn hons-intersect-p2 (l1 l2)
  (cond ((atom l1) nil)
        ((hons-member-equal (car l1) l2)
         t)
        (t
         (hons-intersect-p2 (cdr l1) l2))))

(defn hons-intersect-p (l1 l2) ; returns T or NIL
  (cond ((and (worth-hashing l1)
              (worth-hashing l2))
         (with-fast-list fl2 l2 '*hons-intersect-p-alist*
                         (hons-intersect-p1 l1 fl2)))
        (t
         (hons-intersect-p2 l1 l2))))

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
        (t
         ;; [Jared]: calling len on both lists seems inefficient; we could
         ;; write a cdr-both style function that determines which is longer
         (let ((len1 (len l1))
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
  (if (atom l)
      nil
    (hons-union (car l)
                (hons-union-list (cdr l)))))


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




; DEFHONST -----------------------------------------------------------------

;; [Jared]: bozo new hons means defhonst changes...

;; Defhonst is like defconst.

;; The record for all defhonst values is kept in the ACL2 global
;; 'defhonst.  To flush all defhonst records manually, one may:
;; (f-put-global 'defhonst nil state).


; [Jared]: if defhonst is really like defconst, then why have it?  What's the
; difference?  Why is it desirable?  We should have some documentation for it.
; It seems there are a couple of consequences of using defhonst, e.g.,
; persistent hons table, evisceration, etc.


;; [Jared]: removed this, but not sure what it was for.

;; (defmacro update-defhonst (f r)
;;   `(let ((f ,f) (r ,r))
;;      (pprogn
;;       (f-put-global
;;        'defhonst
;;        (hons (hons (cadr r)
;;                    (concatenate 'string "," (symbol-name f)))
;;              (if (boundp-global 'defhonst state)
;;                  (get-global 'defhonst state)
;;                nil))
;;        state)
;;       (value f))))



(defmacro defhonst (name form &key (evisc 'nil eviscp) check doc)

; From Matt Mon Sep 29 09:53:49 CDT 2008

  `(with-output
    :off summary
    (progn
      ;; [Jared]: switched to hons-copy-persistent
      (defconst ,name (hons-copy-persistent ,form) ,doc)
      (table evisc-table
             ,name
             ,(if eviscp
                  evisc
                (let ((str (symbol-name name)))
                  (if (may-need-slashes str)
                      (concatenate 'string "#.|" str "|")
                    (concatenate 'string "#." str)))))

;; [Jared]: removed the table event
;;       (table persistent-hons-table
;;              (let ((x ,name))
;;                (if (or (consp x) (stringp x))

;; ; honsp-check without check

;;                    x
;;                  nil))
;;              t)
      ,@(and check
             `((assert-event ,check)))
      (value-triple ',name))))




; UNRELATED TO HONS --------------------------------------------------------

; [Jared]: BOZO why is this stuff in hons-help.lisp?  What does any of this
; have to do with hons?  Can we move this elsewhere?





(defstub fail (x y) t :doc

; [Jared]: find a better place for this?

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
   occur.~/")



(defn plev-fn (length level lines circle pretty readably state)
  (declare (xargs :mode :program))
  (let* ((old-tuple (abbrev-evisc-tuple state))
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
                (list :length length
                      :level level
                      :lines lines
                      :circle circle
                      :readably readably
                      :pretty pretty)
                state))))

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




; STUFF I REMOVED ----------------------------------------------------------


; [Jared]: Removing this because the MBE I added is better.

; (defthm symbol-listp-hons-copy-list-r
;   (implies (symbol-listp x)
;            (symbol-listp (hons-copy-list-r x))))


; [Jared]: Removing hons-len1 and hons-len.  New ACL2 versions appear to
; optimize len anyway, and make it tail recursive.  And, at any rate, it
; doesn't appear that this is being used.

;; (defun hons-len1 (x acc)
;;   (declare (xargs :guard (and (integerp acc) (<= 0 acc))))
;;   (mbe :logic (+ (len x) acc)
;;        :exec (if (atom x)
;;                  acc
;;                (hons-len1 (cdr x) (+ 1 acc)))))
;;
;; (defn hons-len (x)
;;   (mbe :logic (len x)
;;        :exec (hons-len1 x 0)))
;;
;; (defthm natp-hons-len
;;   (implies (integerp n)
;;            (and (integerp (hons-len1 x n))
;;                 (>= (hons-len1 x n) n))))




; [Jared]: I'm removing this.  It may actually be kind of a nice idea, but this
; function is clearly defective.  For instance,
;
; (alist-subsetp
;  (hons-acons 'a 3 (hons-acons 'b 2 nil))
;  (hons-acons 'b 2 (hons-acons 'a 1 nil)))
;
; Returns T.  The problem is that we should be double-car'ing el, if we're
; going to pass in al1 as its value.  Also, I think we should not name this
; function alist-equal, something like fast-alist-equal would be more
; appropriate.

;; (defn alist-subsetp1 (l1 l2 el)
;;   (cond ((atom el) t)
;;         (t (and (equal (hons-get (car el) l1)
;;                        (hons-get (car el) l2))
;;                 (alist-subsetp1 l1 l2 (cdr el))))))
;;
;; (defn alist-subsetp (al1 al2)
;;   (alist-subsetp1 al1 al2 al1))
;;
;; (defn alist-equal (al1 al2)
;;   ":Doc-Section Hons-and-Memoization
;;
;;   (ALIST-EQUAL al1 al2) returns T or NIL according to whether for all
;;   x, (equal (hons-get x AL1) (hons-get x AL2)).~/
;;
;;   ALIST-EQUAL sometimes runs rather fast on fast alists. ~/~/"
;;
;;   (and (equal (fast-alist-len al1)
;;               (fast-alist-len al2))
;;        (alist-subsetp al1 al2)))



;; [Jared]: I think these are not used, and would prefer to get rid of them.

;; ; The functions HONS-GETPROP and HONS-PUTPROP support fast property
;; ; lists for any type of keys, not just symbols.  With HONS-PUTPROP you
;; ; can cause X to have the value VAL under the key Y, and with
;; ; HONS-GETPROP you can later ask for the value of X under the key Y
;; ; and get back VAL.  As usual in Lisp, there is potential confusion
;; ; over whether NIL is a value of an indication of no value.

;; ; [Jared]: BOZO are these useful?  Can we get rid of them?

;; (defn hons-getprop (x y al)
;;   (cdr (hons-get (hons x y) al)))

;; (defn hons-putprop (x y val al)
;;   (hons-acons (hons x y) val al))

;; (defthm hons-getprop-of-hons-putprop
;;   (equal (hons-getprop x1 y1 (hons-putprop x2 y2 val al))
;; 	 (if (and (equal x1 x2)
;; 		  (equal y1 y2))
;; 	     val
;; 	   (hons-getprop x1 y1 al))))




;; [Jared]: Removing this; it seems like you usually don't want to have the
;; spine honsed anyway.
;;
;; (defn make-fal! (al name)
;;   (cond ((atom al)
;;          name)
;;         ((atom (car al))
;;          (make-fal (cdr al) name))
;;         (t
;;          (hons-acons! (caar al)
;;                       (cdar al)
;;                       (make-fal (cdr al) name)))))



;; (defn make-list-of-numbers (n)

;; ; [Jared]: Seems like fluff, why include it here?  Why use hons?  If there's a
;; ; good reason, then why not hons in the base case?  Could do better to return
;; ; (list 0)?  I moved it to hons-tests.lisp

;;   (declare (xargs :guard (natp n)))
;;   (if (zp n)
;;       (list n)
;;     (hons n (make-list-of-numbers (1- n)))))





;; [Jared]: removing the mergesort since I don't think it's really used.

;; (defn odds1 (x ans)
;;   (cond ((atom x) ans)
;;         ((atom (cdr x)) (cons (car x) ans))
;;         (t (odds1 (cddr x) (cons (car x) ans)))))

;; (defn evens1 (x ans)
;;   (cond ((atom x) ans)
;;         ((atom (cdr x)) ans)
;;         (t (evens1 (cddr x) (cons (cadr x) ans)))))

;; (defthm odds1-length
;;   (implies (and (not (atom x))
;;                 (not (atom (cdr x))))
;;            (< (len (odds1 x ans))
;;               (+ (len x)
;;                  (len ans))))
;;   :rule-classes :linear)

;; (defthm evens1-length
;;   (implies (and (not (atom x))
;;                 (not (atom (cdr x))))
;;            (< (len (evens1 x ans))
;;               (+ (len x)
;;                  (len ans))))
;;   :rule-classes :linear)

;; (defun ms-merge (l1 l2 h)

;; ; If (1) both L1 and and L2 are alists,
;; ;    (2) H is an alist that maps the car of each member of L1 and L2
;; ;        to an ACL2 ordinal, cf. O-P, and
;; ;    (3) both L1 and L2 are weakly O-P increasing with respect
;; ;        to the H values of their cars,
;; ; then (MS-MERGE L1 L2 H) is a permutation of (APPEND L1 L2)
;; ; that is weakly increasing with respect to the H value
;; ; of the cars of its members.

;;   (declare (xargs :guard t
;;                   :measure (+ (len l1) (len l2))))
;;   (cond ((atom l1) l2)
;;         ((atom l2) l1)
;;         ((atom (car l1)) nil) ; to help with guards
;;         ((atom (car l2)) nil)
;;         (t (let ((m1 (cdr (hons-get (caar l1) h)))
;;                  (m2 (cdr (hons-get (caar l2) h))))
;;              (cond ((and (o-p m1)
;;                          (o-p m2)
;;                          (o< m1 m2))
;;                     (cons (car l1) (ms-merge (cdr l1) l2 h)))
;;                    (t (cons (car l2) (ms-merge l1 (cdr l2) h))))))))

;; (defun merge-sort (a h)

;; ; If both A and H are alists and H maps the car of each member of A to
;; ;    an ACL2 ordinal, cf. O-P,
;; ; then (MERGE-SORT A H) is a permutation of A whose cars are
;; ;    weakly O-<-increasing under H.

;; ; For efficiency, H should be a fast alist, but there is no reason for
;; ; A to be.

;;   (declare (xargs :guard t
;;                   :verify-guards nil
;;                   :measure (len a)))
;;   (if (or (atom a) (atom (cdr a))) a
;;     (ms-merge (merge-sort (odds1 a nil) h)
;;               (merge-sort (evens1 a nil) h)
;;               h)))

;; (verify-guards merge-sort)

;; (defn hons-merge-sort (a h)
;; ; BOZO Jared thinks this is never used.
;;   (hons-copy (merge-sort a h)))




;; (defn hons-take (n l)
;;   ":Doc-Section Hons-and-Memoization

;;  First n elements of l~/

;;  (HONS-TAKE n l) returns a honsed list of the first N elements of L.
;;  To always return a list of n elements, HONS-TAKE fills at the end
;;  with NIL, if necessary.~/~/"

;; ; [Jared]: Changed this to use hons-make-list.  The current definition agrees
;; ; with gentle-take, but not with take.  BOZO is there a good reason to have
;; ; this nil behavior?  It seems nicer to make it agree with take instead.

;;  (cond ((not (posp n))
;;         nil)
;;        ((atom l)
;;         (hons-make-list-acc n nil nil))
;;        (t
;;         (hons (car l)
;;               (hons-take (1- n) (cdr l))))))


;; (defn nil-list (n)
;;   (mbe :logic (make-list n :initial-element nil)
;;        :exec (hons-make-list-acc n nil nil)))




;;; [Jared]: hons-copy-r and hons-copy-list-r are not needed in the new hons
;;; system; just use hons-copy instead.

;; (defn hons-copy-r (x)

;; ; [Jared]: I don't understand this comment or why hons-copy-r is
;; ; better than hons-copy.

;; ; This is an "under the hood" remark.  If the system is built with
;; ; *break-honsp* non-NIL, then one will be rudely interrupted whenever
;; ; HONSP returns NIL.  So if you wish to copy a CONS structure into a
;; ; HONS structure, use HONS-COPY-R instead of HONS-COPY.

;;   ;; r stands for recursive
;;   (mbe :logic x
;;        :exec (if (atom x) 
;;                  x
;;                (hons (hons-copy-r (car x))
;;                      (hons-copy-r (cdr x))))))

;; (defn hons-copy-list-r (x)
;;   ;; r stands for recursive
;;   (mbe :logic x
;;        :exec (if (atom x)
;;                  x
;;                (hons (car x)
;;                      (hons-copy-list-r (cdr x))))))



;;; [Jared]: this doesn't seem to be used

;; (defn hons-remove-equal-cons (x y)
;;   "REMOVE-EQUAL using HONS-EQUAL for each equality check, produces CONSES"

;; ; [Jared]: BOZO. It would be really nice to change this to return nil in the
;; ; base case, so that it could be MBE equal to remove-equal, and hence we would
;; ; not be introducing yet another function symbol.

;;   (cond ((atom y) y)
;;         ((hons-equal x (car y))
;;          (hons-remove-equal-cons x (cdr y)))
;;         (t (cons (car y) (hons-remove-equal-cons x (cdr y))))))





;; [Jared and Sol] deleting this because it's never used and we have a new fancy
;; thing called with-fast-alist that is better

;; (defmacro with-fast-alist (var l1 l2 name form)
;;   `(let ((,var (hons-put-list ,l1 ,l2 ,name)))
;;      (ansfl ,form ,var)))
