; Memory Taggings and Dynamic Data Structures}

; J Strother Moore

; Department of Computer Science
; University of Texas at Austin
; Austin, Texas 78701
; moore@cs.utexas.edu

; This book is described in the above paper.  I have kept comments pretty
; sparse.

; (certify-book "memory-taggings")

(in-package "ACL2")

; This file is presumed to be located at:

; /projects/acl2/v2-8/books/workshops/2003/moore_rockwell/support/

(include-book "../../../../misc/records")
(include-book "../../../../arithmetic/top-with-meta")
(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

(defun seq-int (start len)
  (if (zp len)
      nil
    (cons start
        (seq-int (1+ start) (1- len)))))

(defun unique (list)
  (if (consp list)
      (and (not (member (car list) (cdr list)))
         (unique (cdr list)))
    t))

(mutual-recursion

(defun collect (typ ptr n ram dcl)
  (declare (xargs :measure (cons (+ 1 (nfix n)) 0)))
  (let ((descriptor (cdr (assoc typ dcl))))
    (if (zp n)
        nil
      (if (zp ptr)
          nil
        (if (atom descriptor)
            nil
          (append (seq-int ptr (len descriptor))
                  (collect-lst typ
                               ptr
                               0
                               (- n 1)
                               ram
                               dcl)))))))

(defun collect-lst (typ ptr i n ram dcl)
  (declare (xargs :measure
                  (cons (+ 1 (nfix n))
                        (nfix (- (len (cdr (assoc typ dcl))) (nfix i))))))
  (let* ((descriptor (cdr (assoc typ dcl)))
         (slot-typ (nth i descriptor))
         (i (nfix i)))

; It makes life a little simpler if we always know that ptr is non-zero.

    (cond ((zp ptr) nil)
          ((<= (len descriptor) i) nil)
          ((symbolp slot-typ)
           (append (collect slot-typ
                            (g (+ ptr i) ram)
                            n ram dcl)
                   (collect-lst typ
                                ptr
                                (+ 1 i)
                                n ram dcl)))
          (t (collect-lst typ
                          ptr
                          (+ 1 i)
                          n ram dcl)))))
)

; We next deal with marking arbitrary (non-pointer) elements in a
; given data structure at address ptr of type typ with a given
; descriptor.  We need a constrained function to denote the value we
; wish to put into field i of that data structure.  In actual
; applications we may wish the value to be a function of other fields,
; so we allow the function to see the ram.

; We originally declared an unconstrained function to compute the new
; value:

; (defstub new-field-value (typ ptr i ram) t).

; But then we needed the fact that

; (NEW-FIELD-VALUE TYP PTR K (S ADDR VAL RAM))
; =
; (NEW-FIELD-VALUE TYP PTR K RAM)

; in order to prove that we could commute an independent s out of the
; marking pass.  So we provide the following constraint.

(encapsulate
 (((new-field-value * * * * *) => *))
 (local (defun new-field-value (typ ptr i ram dcl)
          (declare (ignore typ ptr i ram dcl))
          0))
 (defthm new-field-value-s-commutes
   (implies (not (member addr (seq-int ptr (len (cdr (assoc typ dcl))))))
            (equal (new-field-value typ ptr i (s addr val ram) dcl)
                   (new-field-value typ ptr i ram              dcl)))))

; This contraint says that the new field value is impervious to writes
; ``far away'' from the field being smashed.  More precisely, the the
; new field value is invariant under writes to locations outside the
; (immediate) data object.  This means that it is permitted for the
; the new field value to look at other fields immediately within the
; data object.

(defun s* (typ ptr i ram dcl)
  (declare (xargs :measure (nfix (- (len (cdr (assoc typ dcl)))
                                    (nfix i)))))
  (let* ((descriptor (cdr (assoc typ dcl)))
         (i (nfix i))
         (slot-typ (nth i descriptor)))
    (cond
     ((zp ptr) ram)
     ((< i (len descriptor))
      (cond ((symbolp slot-typ)
             (s* typ ptr (+ 1 i) ram dcl))
            (t (let ((ram (s (+ ptr i)
                             (new-field-value typ ptr i ram dcl)
                             ram)))
                 (s* typ ptr (+ 1 i) ram dcl)))))
     (t ram))))

(mutual-recursion

(defun mark (typ ptr n ram dcl)
  (declare (xargs :measure (cons (+ 1 (nfix n)) 0)))
  (let ((descriptor (cdr (assoc typ dcl))))
    (if (zp n)
        ram
      (if (zp ptr)
          ram
        (if (atom descriptor)
            ram
          (let ((ram (s* typ ptr 0 ram dcl)))
            (mark-lst typ
                      ptr
                      0
                      (- n 1)
                      ram
                      dcl)))))))

(defun mark-lst (typ ptr i n ram dcl)
  (declare (xargs :measure
                  (cons (+ 1 (nfix n))
                        (nfix (- (len (cdr (assoc typ dcl)))
                                 (nfix i))))))
  (let* ((descriptor (cdr (assoc typ dcl)))
         (slot-typ (nth i descriptor))
         (i (nfix i)))
    (cond ((zp ptr) ram)
          ((<= (len descriptor) i) ram)
          ((symbolp slot-typ)
           (let ((ram (mark slot-typ
                            (g (+ ptr i) ram)
                            n ram dcl)))
             (mark-lst typ
                       ptr
                       (+ 1 i)
                       n ram dcl)))
          (t (mark-lst typ
                       ptr
                       (+ 1 i)
                       n ram dcl)))))
)

(defun compose-bab (typ1 ptr1 n1  typ2 ptr2 n2  typ3 ptr3 n3   ram dcl)
  (let ((ram (mark typ1 ptr1 n1 ram dcl)))
    (let ((ram (mark typ2 ptr2 n2 ram dcl)))
      (let ((ram (mark typ3 ptr3 n3 ram dcl)))
        ram))))

; Utility Functions and Lemmas

(defthm g-s
  (equal (g x (s y v r))
         (if (equal x y)
             v
           (g x r))))

(defthm member-append
  (iff (member e (append a b))
       (or (member e a)
           (member e b))))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defun intersectp (x y)
;   (declare (xargs :guard (and (eqlable-listp x)
;                               (eqlable-listp y))))
;   (cond ((endp x) nil)
;         ((member (car x) y) t)
;         (t (intersectp (cdr x) y))))

(defthm unique-append
  (iff (unique (append a b))
       (and (unique a)
            (unique b)
            (not (intersectp a b)))))

(defthm intersectp-append-1
  (iff (intersectp c (append a b))
       (or (intersectp c a)
           (intersectp c b))))

(defthm intersectp-append-2
  (iff (intersectp (append a b) c)
       (or (intersectp a c)
           (intersectp b c))))

; (SET-MATCH-FREE-ERROR NIL)

(defthm member-intersection-1
  (implies (and (not (intersectp b a))
                (member ptr b))
           (not (member ptr a))))

(encapsulate
 nil
 (local
  (defthm intersectp-commutes-1
    (implies  (not (member a1 b))
              (equal (intersectp b (cons a1 a2))
                     (intersectp b a2)))))

 (local
  (defthm intersectp-commutes-2
    (implies  (member a1 b)
              (intersectp b (cons a1 a2)))))

 (defthm intersectp-commutes
   (iff (intersectp a b)
        (intersectp b a))))

(defthm member-seq-int
  (implies (integerp j)
           (iff (member i (seq-int j n))
                (if (zp n)
                    nil
                  (and (integerp i)
                       (<= j i)
                       (<  i (+ j n)))))))

; ---------------------------------------------------------------------------
; Some key properties of s*

(defthm s*-s-commutes
  (implies (not (member addr (seq-int ;(+ i ptr)
                              ptr
                              (len (cdr (assoc typ dcl))))))
           (equal (s* typ ptr i (s addr val ram) dcl)
                  (s addr val (s* typ ptr i ram dcl)))))

(defthm g-s*
  (implies (not (member addr (seq-int ptr (len (cdr (assoc typ dcl))))))
           (equal (g addr (s* typ ptr i ram dcl))
                  (g addr ram))))

(defthm member-intersection-2
  (implies (and (not (intersectp a b))
                (member e b))
           (not (member e a))))

(defthm new-field-value-s*
  (implies (and (integerp i2)
                (<= 0 i2)
                (not (intersectp
                      (seq-int (+ i2 ptr2)
                               (- (len (cdr (assoc typ2 dcl))) i2))
                      (seq-int ptr1 (len (cdr (assoc typ1 dcl)))))))
           (equal (new-field-value typ1 ptr1 i1 (s* typ2 ptr2 i2 ram dcl) dcl)
                  (new-field-value typ1 ptr1 i1 ram dcl))))

(defthm subsetp-seq-int
  (implies (and (not (zp ptr1))
                (integerp i1)
                (<= 0 i1))
           (subsetp (seq-int (+ i1 ptr1)
                             (+ (- i1) n1))
                    (seq-int ptr1 n1))))

(defthm intersectp-subsetp
  (implies (and (not (intersectp a b))
                (subsetp a1 a))
           (not (intersectp b a1)))
  :rule-classes ((:rewrite :match-free :all)))

(defthm s*-s*-commutes
  (implies (and (not (zp ptr1))
                (not (zp ptr2))
                (integerp i1)
                (<= 0 i1)
                (integerp i2)
                (<= 0 i2)
                (not (intersectp (seq-int ptr1 ;(+ i1 ptr1)
                                          (len (cdr (assoc typ1 dcl))))
                                 (seq-int ptr2 ;(+ i2 ptr2)
                                          (len (cdr (assoc typ2 dcl)))))))
           (equal (s* typ1 ptr1 i1 (s* typ2 ptr2 i2 ram dcl) dcl)
                  (s* typ2 ptr2 i2 (s* typ1 ptr1 i1 ram dcl) dcl)))
  :rule-classes ((:rewrite :loop-stopper ((typ1 typ2)))))




; ---------------------------------------------------------------------------
; More Proof-Specific Lemmas

; Next I eliminate the mutual recursion and deal just with the
; fundamental functions collect-lst and mark-lst.  I rename them ral
; and mal for brevity.

(defun collect-fn (fn typ ptr i n ram dcl)
  (declare (xargs :measure
                  (if (equal fn :ALL)
                      (cons (+ 1 (nfix n))
                            (nfix (- (len (cdr (assoc typ dcl))) (nfix i))))
                    (cons (+ 1 (nfix n)) 0))))
  (if (equal fn :ALL)
      (let* ((descriptor (cdr (assoc typ dcl)))
             (slot-typ (nth i descriptor))
             (i (nfix i)))
        (cond ((zp ptr) nil)
              ((<= (len descriptor) i) nil)
              ((symbolp slot-typ)
               (append (collect-fn :ONE slot-typ
                                   (g (+ ptr i) ram)
                                   i
                                   n ram dcl)
                       (collect-fn :ALL typ
                                   ptr
                                   (+ 1 i)
                                   n ram dcl)))
              (t (collect-fn :ALL typ
                             ptr
                             (+ 1 i)
                             n ram dcl))))
    (let ((descriptor (cdr (assoc typ dcl))))
      (if (zp n)
          nil
        (if (zp ptr)
            nil
          (if (atom descriptor)
              nil
            (append (seq-int ptr (len descriptor))
                    (collect-fn :ALL typ
                                ptr
                                0
                                (- n 1)
                                ram
                                dcl))))))))

(defun mark-fn (fn typ ptr i n ram dcl)
  (declare (xargs :measure
                  (if (equal fn :ALL)
                      (cons (+ 1 (nfix n))
                            (nfix (- (len (cdr (assoc typ dcl)))
                                     (nfix i))))
                    (cons (+ 1 (nfix n)) 0))))

  (if (equal fn :ALL)
      (let* ((descriptor (cdr (assoc typ dcl)))
             (slot-typ (nth i descriptor))
             (i (nfix i)))
        (cond ((zp ptr) ram)
              ((<= (len descriptor) i) ram)
              ((symbolp slot-typ)
               (let ((ram (mark-fn :ONE slot-typ
                                   (g (+ ptr i) ram)
                                   i n ram dcl)))
                 (mark-fn :ALL typ
                           ptr
                           (+ 1 i)
                           n ram dcl)))
              (t (mark-fn :ALL typ
                           ptr
                           (+ 1 i)
                           n ram dcl))))
    (let ((descriptor (cdr (assoc typ dcl))))
      (if (zp n)
          ram
        (if (zp ptr)
            ram
          (if (atom descriptor)
              ram
            (let ((ram (s* typ ptr 0 ram dcl)))
              (mark-fn :ALL typ
                        ptr
                        0
                        (- n 1)
                        ram
                        dcl))))))))

(defun s*-tags-ok (typ ptr i dcl tags)
  (declare (xargs :measure (nfix (- (len (cdr (assoc typ dcl)))
                                    (nfix i)))))
  (let* ((descriptor (cdr (assoc typ dcl)))
         (i (nfix i))
         (slot-typ (nth i descriptor)))
    (cond
     ((zp ptr) t)
     ((< i (len descriptor))
      (cond ((symbolp slot-typ)
             (cond ((equal (g (+ ptr i) tags) :PTR)
                    (s*-tags-ok typ ptr (+ 1 i) dcl tags))
                   (t nil)))
            ((equal (g (+ ptr i) tags) :DATA)
             (s*-tags-ok typ ptr (+ 1 i) dcl tags))
            (t nil)))
     (t t))))

(defun tags-ok-fn (fn typ ptr i n ram dcl tags)
  (declare (xargs :measure
                  (if (equal fn :ALL)
                      (cons (+ 1 (nfix n))
                            (nfix (- (len (cdr (assoc typ dcl))) (nfix i))))
                    (cons (+ 1 (nfix n)) 0))))
  (if (equal fn :ALL)
      (let* ((descriptor (cdr (assoc typ dcl)))
             (slot-typ (nth i descriptor))
             (i (nfix i)))
        (cond ((zp ptr) t)
              ((<= (len descriptor) i) t)
              ((symbolp slot-typ)
               (cond
                ((equal (g (+ ptr i) tags) :PTR)
                 (and (tags-ok-fn :ONE slot-typ
                                  (g (+ ptr i) ram)
                                  i
                                  n ram dcl tags)
                      (tags-ok-fn :ALL typ
                                  ptr
                                  (+ 1 i)
                                  n ram dcl tags)))
                (t nil)))
              ((equal (g (+ ptr i) tags) :DATA)
               (tags-ok-fn :ALL typ
                           ptr
                           (+ 1 i)
                           n ram dcl tags))
              (t nil)))
    (let ((descriptor (cdr (assoc typ dcl))))
      (if (zp n)
          t
        (if (zp ptr)
            t
          (if (atom descriptor)
              t
            (and (s*-tags-ok typ ptr 0 dcl tags)
                 (tags-ok-fn :ALL typ
                             ptr
                             0
                             (- n 1)
                             ram
                             dcl tags))))))))

(defthm auto-open-collect-fn
  (implies (if (equal fn :ALL)
               (< (nfix i) (len (cdr (assoc typ dcl))))
             (not (zp n)))
           (equal (collect-fn fn typ ptr i n ram dcl)
                  (if (equal fn :ALL)
                      (let* ((descriptor (cdr (assoc typ dcl)))
                             (slot-typ (nth i descriptor))
                             (i (nfix i)))
                        (cond
                         ((zp ptr) nil)
                         ((symbolp slot-typ)
                          (append (collect-fn :ONE slot-typ
                                              (g (+ ptr i) ram)
                                              i
                                              n ram dcl)
                                  (collect-fn :ALL typ
                                              ptr
                                              (+ 1 i)
                                              n ram dcl)))
                         (t (collect-fn :ALL typ
                                        ptr
                                        (+ 1 i)
                                        n ram dcl))))
                    (let ((descriptor (cdr (assoc typ dcl))))
                      (if (zp ptr)
                          nil
                        (if (atom descriptor)
                            nil
                          (append (seq-int ptr (len descriptor))
                                  (collect-fn :ALL typ
                                              ptr
                                              0
                                              (- n 1)
                                              ram
                                              dcl)))))))))

(defthm auto-open-mark-fn
  (implies (if (equal fn :ALL)
               (< (nfix i) (len (cdr (assoc typ dcl))))
             (not (zp n)))
           (equal (mark-fn fn typ ptr i n ram dcl)
                  (if (equal fn :ALL)
                      (let* ((descriptor (cdr (assoc typ dcl)))
                             (slot-typ (nth i descriptor))
                             (i (nfix i)))
                        (cond ((zp ptr) ram)
                              ((<= (len descriptor) i) ram)
                              ((symbolp slot-typ)
                               (let ((ram (mark-fn :ONE slot-typ
                                                   (g (+ ptr i) ram)
                                                   i n ram dcl)))
                                 (mark-fn :ALL typ
                                          ptr
                                          (+ 1 i)
                                          n ram dcl)))
                              (t (mark-fn :ALL typ
                                          ptr
                                          (+ 1 i)
                                          n ram dcl))))
                    (let ((descriptor (cdr (assoc typ dcl))))
                      (if (zp n)
                          ram
                        (if (zp ptr)
                            ram
                          (if (atom descriptor)
                              ram
                            (let ((ram (s* typ ptr 0 ram dcl)))
                              (mark-fn :ALL typ
                                       ptr
                                       0
                                       (- n 1)
                                       ram
                                       dcl))))))))))

(defthm auto-open-tags-ok-fn
  (implies (if (equal fn :ALL)
               (< (nfix i) (len (cdr (assoc typ dcl))))
             (not (zp n)))
           (equal (tags-ok-fn fn typ ptr i n ram dcl tags)
                  (if (equal fn :ALL)
                      (let* ((descriptor (cdr (assoc typ dcl)))
                             (slot-typ (nth i descriptor))
                             (i (nfix i)))
                        (cond ((zp ptr) t)
                              ((symbolp slot-typ)
                               (cond
                                ((equal (g (+ ptr i) tags) :PTR)
                                 (and (tags-ok-fn :ONE slot-typ
                                                  (g (+ ptr i) ram)
                                                  i
                                                  n ram dcl tags)
                                      (tags-ok-fn :ALL typ
                                                  ptr
                                                  (+ 1 i)
                                                  n ram dcl tags)))
                                (t nil)))
                              ((equal (g (+ ptr i) tags) :DATA)
                               (tags-ok-fn :ALL typ
                                           ptr
                                           (+ 1 i)
                                           n ram dcl tags))
                              (t nil)))
                    (let ((descriptor (cdr (assoc typ dcl))))
                      (if (zp ptr)
                          t
                        (if (atom descriptor)
                            t
                          (and (s*-tags-ok typ ptr 0 dcl tags)
                               (tags-ok-fn :ALL typ
                                           ptr
                                           0
                                           (- n 1)
                                           ram
                                           dcl tags)))))))))


(defthm assoc-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm equal-len-0
  (equal (equal (len x) 0)
         (not (consp x))))

(defthm collect-s
  (implies (and (tags-ok-fn fn typ ptr i n ram dcl tags)
                (equal (g addr tags) :DATA))
           (equal (collect-fn fn typ ptr i n (s addr val ram) dcl)
                  (collect-fn fn typ ptr i n ram dcl))))

(defthm intersectp-seq-int-cons
  (implies (and (not (zp ptr1))
                (integerp ptr2)
                (<= ptr1 ptr2)
                (< ptr2 (+ (nfix n) ptr1)))
           (intersectp (seq-int ptr1 n)
                       (cons ptr2 lst))))

(defthm tags-ok-fn-s
  (implies (equal (g ptr1 tags) :DATA)
           (equal (tags-ok-fn fn typ ptr i n
                              (s ptr1 val ram)
                              dcl tags)
                  (tags-ok-fn fn typ ptr i n
                              ram dcl tags))))

(defthm collect-fn-s*
  (implies (and (tags-ok-fn fn typ ptr i n ram dcl tags)
                (s*-tags-ok typ1 ptr1 k1 dcl tags))
           (equal (collect-fn fn typ ptr i n
                              (s* typ1 ptr1 k1 ram dcl)
                              dcl)
                  (collect-fn fn typ ptr i n ram dcl))))

(defthm hack2a
  (implies (and (integerp k)
                (integerp kmax)
                (<= 0 k)
                (< k kmax)
                (integerp ptr))
           (member (+ k ptr) (seq-int ptr kmax))))

(defthm hack2b
  (implies (and (not (intersectp a b))
                (member e b))
           (not (member e a))))

(defthm hack2
  (implies
   (and (not (intersectp a
                         (seq-int ptr1 k1max)))
	(not (zp ptr1))
	(integerp k1)
        (<= 0 k1)
        (< k1 k1max)
        (integerp k1max))
   (not (member (+ k1 ptr1) a))))

(defthm unique-seq-int-lemma
  (implies (< e ptr)
           (not (member e (seq-int ptr n)))))

(defthm unique-seq-int
  (unique (seq-int ptr n)))

(defthm intersectp-hack1
  (implies (intersectp a b)
           (intersectp a (cons ptr1 b))))

(defthm intersectp-x-x
  (iff (intersectp x x)
       (consp x)))

(defthm consp-seq-int
  (equal (consp (seq-int ptr n))
         (not (zp n))))

(defthm tags-ok-fn-s*
  (implies (s*-tags-ok typ ptr i dcl tags)
           (equal (tags-ok-fn fn1 typ1 ptr1 i1 n1
                              (s* typ ptr i ram dcl)
                              dcl tags)
                  (tags-ok-fn fn1 typ1 ptr1 i1 n1 ram dcl tags))))

(defthm g-s*-new
  (implies (and (s*-tags-ok typ ptr i dcl tags)
                (equal (g ptr1 tags) :ptr))
           (equal (g ptr1 (s* typ ptr i ram dcl))
                  (g ptr1 ram))))


(defun tags-ok-fn-mark-fn-hint (fn typ ptr i n ram dcl tags
                                   fn1 typ1 ptr1 i1 n1)
  (declare (xargs :measure
                  (if (equal fn :ALL)
                      (cons (+ 1 (nfix n))
                            (nfix (- (len (cdr (assoc typ dcl)))
                                     (nfix i))))
                    (cons (+ 1 (nfix n)) 0))))

  (if (equal fn :ALL)
      (let* ((descriptor (cdr (assoc typ dcl)))
             (slot-typ (nth i descriptor))
             (i (nfix i)))
        (cond ((zp ptr) (list tags fn1 typ1 ptr1 i1 n1))
              ((<= (len descriptor) i) ram)
              ((symbolp slot-typ)
               (let ((ram1 (mark-fn :ONE slot-typ
                                    (g (+ ptr i) ram)
                                    i n ram dcl)))
                 (list
                  (tags-ok-fn-mark-fn-hint :ONE slot-typ
                                           (g (+ ptr i) ram)
                                           i n ram dcl tags
                                           fn1 typ1 ptr1 i1 n1)
                  (tags-ok-fn-mark-fn-hint :ONE slot-typ
                                           (g (+ ptr i) ram)
                                           i n ram dcl tags
                                           :ALL typ ptr (+ i 1) n)
                  (tags-ok-fn-mark-fn-hint :ALL typ
                                           ptr
                                           (+ 1 i)
                                           n ram1 dcl tags
                                           fn1 typ1 ptr1 i1 n1)
                  )))
              (t (tags-ok-fn-mark-fn-hint :ALL typ
                                          ptr
                                          (+ 1 i)
                                          n ram dcl tags
                                          fn1 typ1 ptr1 i1 n1))))
    (let ((descriptor (cdr (assoc typ dcl))))
      (if (zp n)
          ram
        (if (zp ptr)
            ram
          (if (atom descriptor)
              ram
            (let ((ram (s* typ ptr 0 ram dcl)))
              (tags-ok-fn-mark-fn-hint :ALL typ
                                       ptr
                                       0
                                       (- n 1)
                                       ram
                                       dcl tags
                                       fn1 typ1 ptr1 i1 n1))))))))

(defthm tags-ok-fn-mark-fn
  (implies (tags-ok-fn fn2 typ2 ptr2 i2 n2 ram dcl tags)
           (equal (tags-ok-fn fn1 typ1 ptr1 i1 n1
                              (mark-fn fn2 typ2 ptr2 i2 n2 ram dcl)
                              dcl tags)
                  (tags-ok-fn fn1 typ1 ptr1 i1 n1 ram dcl tags)))
  :hints (("Goal"
           :induct
           (tags-ok-fn-mark-fn-hint fn2 typ2 ptr2 i2 n2 ram dcl tags
                                    fn1 typ1 ptr1 i1 n1))))


; Generalized Challenge Theorem 1 (first of two parts)
(defthm g-mark-fn-1
  (implies (and (tags-ok-fn fn typ ptr i n ram dcl tags)
                (equal (g addr tags) :PTR))
           (equal (g addr (mark-fn fn typ ptr i n ram dcl))
                  (g addr ram)))
  :hints (("Goal" :induct (mark-fn fn typ ptr i n ram dcl))))

(defthm collect-fn-mark-fn
  (implies (and (tags-ok-fn fn1 typ1 ptr1 i1 n1 ram dcl tags)
                (tags-ok-fn fn2 typ2 ptr2 i2 n2 ram dcl tags))
           (equal (collect-fn fn1 typ1 ptr1 i1 n1
                              (mark-fn fn2 typ2 ptr2 i2 n2 ram dcl)
                              dcl)
                  (collect-fn fn1 typ1 ptr1 i1 n1 ram dcl)))
  :hints (("Goal" :induct (mark-fn fn2 typ2 ptr2 i2 n2 ram dcl))))

; Generalized Challenge Theorem 1 (second part)
(defthm g-mark-fn-2
  (implies (and (not (member addr (collect-fn fn typ ptr i n ram dcl)))
                (tags-ok-fn fn typ ptr i n ram dcl tags))
           (equal (g addr (mark-fn fn typ ptr i n ram dcl))
                  (g addr ram)))
  :hints (("Goal" :induct (mark-fn fn typ ptr i n ram dcl))))

; Now I will relate collect and collect-lst to collect-fn, etc.

(defthm collect-is-collect-fn-main
  (equal (collect-fn fn typ ptr i n ram dcl)
         (if (equal fn :ALL)
             (collect-lst typ ptr i n ram dcl)
           (collect typ ptr n ram dcl)))
  :rule-classes nil)

(defthm collect-is-collect-fn
  (and (equal (collect typ ptr n ram dcl)
              (collect-fn :ONE typ ptr i n ram dcl))
       (equal (collect-lst typ ptr i n ram dcl)
              (collect-fn :ALL typ ptr i n ram dcl)))
  :hints (("Goal" :use ((:instance collect-is-collect-fn-main (fn ':ONE))
                        (:instance collect-is-collect-fn-main (fn :ALL))))))

(defthm mark-is-mark-fn-main
  (equal (mark-fn fn typ ptr i n ram dcl)
         (if (equal fn :ALL)
             (mark-lst typ ptr i n ram dcl)
           (mark typ ptr n ram dcl)))
  :rule-classes nil)

(defthm mark-is-mark-fn
  (and (equal (mark typ ptr n ram dcl)
              (mark-fn :ONE typ ptr i n ram dcl))
       (equal (mark-lst typ ptr i n ram dcl)
              (mark-fn :ALL typ ptr i n ram dcl)))
  :hints (("Goal" :use ((:instance mark-is-mark-fn-main (fn ':ONE))
                        (:instance mark-is-mark-fn-main (fn :ALL))))))

; Generalized Challenge Theorem 2
(defthm read-over-bab
  (implies
   (and (tags-ok-fn :ONE typ1 ptr1 i n1 ram dcl tags)
        (tags-ok-fn :ONE typ2 ptr2 i n2 ram dcl tags)
        (tags-ok-fn :ONE typ3 ptr3 i n3 ram dcl tags)
        (not (member addr (append (collect typ1 ptr1 n1 ram dcl)
                                  (collect typ2 ptr2 n2 ram dcl)
                                  (collect typ3 ptr3 n3 ram dcl)))))
   (equal
    (g addr (compose-bab typ1 ptr1 n1
                         typ2 ptr2 n2
                         typ3 ptr3 n3
                         ram dcl))
    (g addr ram)))
  :hints (("Goal" :restrict ((g-mark-fn-2 ((tags tags)))
                             (TAGS-OK-FN-MARK-FN ((tags tags)))
                             (COLLECT-FN-MARK-FN ((tags tags)))))))

(defthm mark-fn-s
  (implies (and (equal (g addr tags) :DATA)
                (not (member addr
                             (collect-fn fn typ ptr i n ram dcl)))
                (tags-ok-fn fn typ ptr i n ram dcl tags))
           (equal (mark-fn fn typ ptr i n (s addr val ram) dcl)
                  (s addr val (mark-fn fn typ ptr i n ram dcl))))
  :hints (("Goal" :induct (mark-fn fn typ ptr i n ram dcl))))

(defthm new-field-value-s*
  (implies
   (and
    (integerp i2)
    (<= 0 i2)
    (not
     (intersectp (seq-int (+ i2 ptr2)
                          (- (len (cdr (assoc typ2 dcl))) i2))
                 (seq-int ptr1 (len (cdr (assoc typ1 dcl)))))))
   (equal
    (new-field-value typ1 ptr1 i1 (s* typ2 ptr2 i2 ram dcl)
                     dcl)
    (new-field-value typ1 ptr1 i1 ram dcl))))

(defthm new-field-value-mark-fn
  (implies (and (not (intersectp (seq-int ptr2
                                          (len (cdr (assoc typ2 dcl))))
                                 (collect-fn fn typ ptr i n ram dcl)))
                (tags-ok-fn fn typ ptr i n ram dcl tags))
           (equal
            (new-field-value typ2
                             ptr2 i2 (mark-fn fn typ ptr i n ram dcl)
                             dcl)
            (new-field-value typ2 ptr2 i2 ram dcl)))
  :hints (("Goal" :induct (mark-fn fn typ ptr i n ram dcl))))

; It ain't pretty, but I'm just trying to finish!

(defthm mark-fn-s*
  (implies (and (not (intersectp (seq-int ptr2 ;(+ ptr2 i2)
                                          (len (cdr (assoc typ2 dcl))) ;(-  i2)
                                          )
                                 (collect-fn fn typ ptr i n ram dcl)))
                (tags-ok-fn fn typ ptr i n ram dcl tags)
                (s*-tags-ok typ2 ptr2 i2 dcl tags))
           (equal (mark-fn fn typ ptr i n (s* typ2 ptr2 i2 ram dcl) dcl)
                  (s* typ2 ptr2 i2 (mark-fn fn typ ptr i n ram dcl) dcl)))
  :hints (("Goal" :restrict ((new-field-value-mark-fn ((tags tags)))
                             (mark-fn-s ((tags tags)))))))

(defthm g-mark-fn
  (implies (and (not (member ptr2
                             (collect-fn fn typ ptr i n ram dcl)))
                (tags-ok-fn fn typ ptr i n ram dcl tags))
           (equal (g ptr2 (mark-fn fn
                                   typ ptr i n ram
                                   dcl))
                  (g ptr2 ram)))
  :hints (("Goal" :induct (MARK-FN FN TYP PTR I N RAM DCL))))

; Generalized Challenge Theorem 3

(defthm mark-fn-mark-fn
  (implies (and (tags-ok-fn fn1 typ1 ptr1 i1 n1 ram dcl tags)
                (tags-ok-fn fn2 typ2 ptr2 i2 n2 ram dcl tags)
                (not (intersectp (collect-fn fn1 typ1 ptr1 i1 n1 ram dcl)
                                 (collect-fn fn2 typ2 ptr2 i2 n2 ram dcl))))
           (equal (mark-fn fn1 typ1 ptr1 i1 n1
                           (mark-fn fn2 typ2 ptr2 i2 n2 ram dcl)
                           dcl)
                  (mark-fn fn2 typ2 ptr2 i2 n2
                           (mark-fn fn1 typ1 ptr1 i1 n1 ram dcl)
                           dcl)))
  :hints (("Goal"
           :induct (MARK-FN FN2 TYP2 PTR2 I2 N2 RAM DCL)
           :restrict ((g-mark-fn ((tags tags)))
                      (MARK-FN-S* ((tags tags)))))))

; ----

; What makes the above work relevant to the Rockwell challenge, which
; may be characterized by its focus on the collection of relevant
; addresses and their disjointness?  The key observations are two.

; First, if the collection of addresses is unique, then there exists a
; tagging that satisfies tags-ok-fn.  The idea is that if the collection
; is unique, each address is visited only once and the tagging can
; assign which ever tag is used.

; Second, if you have a tagging for each of two pointers and the corresponding
; collections are disjoint, you can assemble a tagging that works for both.
; The idea here is that you take one of the working taggings and move into it
; all the taggings from the other one, exploiting the disjointness to know that
; you have not disturbed the other tagging.

; I prove the second result first.

(defun merge-tags (addrs tags1 tags2)
  (cond ((endp addrs) tags2)
        (t (s (car addrs)
              (g (car addrs) tags1)
              (merge-tags (cdr addrs) tags1 tags2)))))

(defthm g-merge-tags
  (equal (g addr (merge-tags addrs tags1 tags2))
         (if (member addr addrs)
             (g addr tags1)
           (g addr tags2))))

(defthm merge-tags-append
  (equal (merge-tags (append a b) tags1 tags2)
         (merge-tags a tags1 (merge-tags b tags1 tags2))))

(defthm merge-tags-s
  (equal (merge-tags a tags1 (s addr (g addr tags1) tags))
         (s addr (g addr tags1) (merge-tags a tags1 tags)))
  :hints (("Subgoal *1/2''" :cases ((equal (car a) addr)))))

(defthm merge-tags-commutes
  (equal (merge-tags a tags1 (merge-tags b tags1 tags2))
         (merge-tags b tags1 (merge-tags a tags1 tags2))))

(defthm s*-tags-ok-merge-tags-1
  (implies (and (s*-tags-ok typ ptr i dcl tags)
                (not (intersectp addrs
                                 (seq-int ptr (len (cdr (assoc typ dcl)))))))
           (s*-tags-ok typ ptr i dcl
                       (merge-tags addrs tags1 tags))))

(defthm s*-tags-ok-s
  (implies (force
            (not (member addr (seq-int (+ ptr (nfix i))
                                       (- (len (cdr (assoc typ dcl)))
                                          (nfix i))))))
           (equal (s*-tags-ok typ ptr i dcl (s addr val tags))
                  (s*-tags-ok typ ptr i dcl tags))))

; I just proved the theorem below.  When I first tried it, I used the
; hypothesis that addr was not a member of

; (collect-fn fn typ ptr i n ram dcl).

; But that is not a theorem.  I then changed that collection to

; (append
;   (if (equal fn :ALL)
;       (seq-int ptr (len (cdr (assoc typ dcl))))
;     nil)
;   (collect-fn fn typ ptr i n ram dcl))

; You might ask why I need the stronger hypothesis?  Suppose we use
; the weaker hypothesis.  Then it might be that addr is ptr and fn is
; :ALL.  The reason is that ptr does not generally occur in the :ALL
; collection from ptr.  So if we smash ptr with (s addr val tags) --
; when addr is ptr -- then the :ALL collect ends up treating ptr as of
; type val.  instead of its old type.  Because I will need this
; hypothesis repeatedly, I define a stronger version of collect-fn.

(defun kollect-fn (fn typ ptr i n ram dcl)
  (append
   (if (equal fn :ALL)
       (seq-int (+ ptr (nfix i))
                (- (len (cdr (assoc typ dcl)))
                   (nfix i)))
     nil)
   (collect-fn fn typ ptr i n ram dcl)))

(defthm tags-ok-fn-s-tags
  (implies (not (member addr (kollect-fn fn typ ptr i n ram dcl)))
           (equal (tags-ok-fn fn typ ptr i n ram dcl
                              (s addr tag tags))
                  (tags-ok-fn fn typ ptr i n ram dcl tags))))

(defthm s*-tags-ok-merge-tags
  (implies (not (intersectp addrs
                            (seq-int (+ ptr (nfix i))
                                     (- (len (cdr (assoc typ dcl)))
                                        (nfix i)))))
           (equal (s*-tags-ok typ ptr i dcl (merge-tags addrs tag1 tags))
                  (s*-tags-ok typ ptr i dcl tags))))


(defthm tags-ok-fn-merge-tags-2
  (implies (not (intersectp addrs
                            (kollect-fn fn typ ptr i n ram dcl)))
           (equal (tags-ok-fn fn typ ptr i n ram dcl
                              (merge-tags addrs tags1 tags))
                  (tags-ok-fn fn typ ptr i n ram dcl tags))))

(defthm s*-tags-ok-merge-tags-2
  (implies (and (not (zp ptr))
                (integerp i)
                (<= 0 i)
                (< i (len (cdr (assoc typ dcl)))))
           (equal (s*-tags-ok typ ptr i dcl
                              (merge-tags
                               (seq-int (+ i ptr)
                                        (- (len (cdr (assoc typ dcl)))
                                           i))
                               tags1 tags2))
                  (s*-tags-ok typ ptr i dcl tags1))))

(defthm s*-tags-ok-merge-tags-2-0
  (implies (and (not (zp ptr))
                (consp (cdr (assoc typ dcl))))
           (equal (s*-tags-ok typ ptr 0 dcl
                              (merge-tags
                               (seq-int ptr
                                        (len (cdr (assoc typ dcl))))
                               tags1 tags2))
                  (s*-tags-ok typ ptr 0 dcl tags1)))
  :hints (("Goal" :use (:instance s*-tags-ok-merge-tags-2 (i 0)))))

(defthm s-merge-tags-noop-1
  (implies (member addr addrs)
           (equal (s addr (g addr tags1) (merge-tags addrs tags1 tags2))
                  (merge-tags addrs tags1 tags2)))
  :hints (("Goal" :induct (member addr addrs))))

(defthm s-merge-tags-noop-2
  (implies (not (member addr addrs))
           (equal (s addr (g addr tags2) (merge-tags addrs tags1 tags2))
                  (merge-tags addrs tags1 tags2)))
  :hints (("Goal" :induct (member addr addrs))))

(defthm s-merge-tags-noop-val-1
  (implies (and (member addr addrs)
                (equal (g addr tags1) val))
           (equal (s addr val (merge-tags addrs tags1 tags2))
                  (merge-tags addrs tags1 tags2))))

(defthm s-merge-tags-noop-val-2
  (implies (and (not (member addr addrs))
                (equal (g addr tags2) val))
           (equal (s addr val (merge-tags addrs tags1 tags2))
                  (merge-tags addrs tags1 tags2))))

(defthm merge-tags-s-commutes-val
  (implies (equal (g addr tags1) val)
           (equal (merge-tags a tags1 (s addr val tags2))
                  (s addr val (merge-tags a tags1 tags2)))))

(defthm s-merge-tags-noop-val-kb-hack
  (implies (and (member addr addrs1)
                (equal (g addr tags1) val))
           (equal (s addr
                     val
                     (merge-tags addrs3
                                 tags1
                                 (merge-tags addrs2
                                             tags1
                                             (merge-tags addrs1 tags1 tags2))))
                  (merge-tags addrs3
                              tags1
                              (merge-tags addrs2
                                          tags1
                                          (merge-tags addrs1 tags1 tags2))))))

(defun tags-ok-fn-merge-tags-3-hint (fn typ ptr i n ram dcl tags addrs2)
  (declare (xargs :measure
                  (if (equal fn :ALL)
                      (cons (+ 1 (nfix n))
                            (nfix (- (len (cdr (assoc typ dcl))) (nfix i))))
                    (cons (+ 1 (nfix n)) 0))))
  (if (equal fn :ALL)
      (let* ((descriptor (cdr (assoc typ dcl)))
             (slot-typ (nth i descriptor))
             (i (nfix i)))
        (cond ((zp ptr) (list addrs2))
              ((<= (len descriptor) i) t)
              ((symbolp slot-typ)
               (cond
                ((equal (g (+ ptr i) tags) :PTR)
                 (list (tags-ok-fn-merge-tags-3-hint
                        :ONE slot-typ (g (+ ptr i) ram) i n ram dcl tags
                        (cons (+ ptr i)
                              (append (kollect-fn :ALL typ ptr (+ i 1) n ram dcl)
                                      addrs2)))

                       (tags-ok-fn-merge-tags-3-hint
                        :ONE slot-typ (g (+ ptr i) ram) i n ram dcl tags
                        (append (kollect-fn :ALL typ ptr (+ i 1) n ram dcl)
                                addrs2))

                       (tags-ok-fn-merge-tags-3-hint
                        :ALL typ ptr (+ 1 i) n ram dcl tags
                        (cons (+ ptr i)
                              (append (collect-fn :ONE
                                                  (nth i (cdr (assoc typ dcl)))
                                                  (g (+ ptr i) ram)
                                                  i n ram dcl)
                                      addrs2)))

                       (tags-ok-fn-merge-tags-3-hint
                        :ALL typ ptr (+ 1 i) n ram dcl tags
                        (append (collect-fn :ONE
                                            (nth i (cdr (assoc typ dcl)))
                                            (g (+ ptr i) ram)
                                            i n ram dcl)
                                addrs2))))
                (t nil)))
              ((equal (g (+ ptr i) tags) :DATA)
               (list (tags-ok-fn-merge-tags-3-hint
                      :ALL typ ptr (+ 1 i) n ram dcl tags
                      (cons (+ ptr i)
                            addrs2))
                     (tags-ok-fn-merge-tags-3-hint
                      :ALL typ ptr (+ 1 i) n ram dcl tags
                      addrs2)))

              (t nil)))
    (let ((descriptor (cdr (assoc typ dcl))))
      (if (zp n)
          t
        (if (zp ptr)
            t
          (if (atom descriptor)
              t
            (list (s*-tags-ok typ ptr 0 dcl tags)
                  (tags-ok-fn-merge-tags-3-hint
                   :ALL typ ptr 0 (- n 1) ram dcl tags
                   addrs2))))))))

(defthm tags-ok-fn-merge-tags-3-main-lemma
  (equal (tags-ok-fn fn typ ptr i n ram dcl
                     (merge-tags (append (kollect-fn fn typ ptr i n ram dcl)
                                         addrs2)
                                 tags1
                                 tags2))
         (tags-ok-fn fn typ ptr i n ram dcl tags1))
  :hints (("Goal"
           :induct
           (tags-ok-fn-merge-tags-3-hint fn typ ptr i n ram dcl tags1 addrs2))
          ("Subgoal *1/10" :in-theory (disable merge-tags-commutes)))
  :rule-classes nil)

(defthm true-listp-kollect-fn
  (true-listp (kollect-fn fn typ ptr i n ram dcl)))

(defthm append-right-id
  (implies (true-listp lst) (equal (append lst nil) lst)))

; The following theorem establishes that if you have a tagging for a
; given pointer then merging preserves it as a tagging.  This
; preservation is assured provided the good tagging is first of the
; two taggings merged.  Note that tags-ok-fn-merge-tags-2 handles the
; other case.  That is, if the merging maps over a list that has no
; intersection with the kollection, then the second tagging is
; preserved.

(defthm tags-ok-fn-merge-tags-3
  (equal (tags-ok-fn fn typ ptr i n ram dcl
                     (merge-tags (kollect-fn fn typ ptr i n ram dcl)
                                 tags1
                                 tags2))
         (tags-ok-fn fn typ ptr i n ram dcl tags1))
  :hints (("Goal" :in-theory (disable kollect-fn)
           :use (:instance tags-ok-fn-merge-tags-3-main-lemma
                           (addrs2 nil)))))

(defthm tags-ok-fn-merge-tags-3-corollary
  (equal (tags-ok-fn :ONE typ ptr i n ram dcl
                     (merge-tags (collect-fn :ONE typ ptr i n ram dcl)
                                 tags1
                                 tags2))
         (tags-ok-fn :ONE typ ptr i n ram dcl tags1))
  :hints (("Goal"
           :use (:instance tags-ok-fn-merge-tags-3-main-lemma
                           (addrs2 nil)
                           (fn :ONE)))))


; Next, I turn to the problem of generating a tagging. I will use
; merge-tags to define the constructor.  This allows me to decompose
; the recursive into simple recursion instead of reflexive recursion.

(defun s*-tags-witness (typ ptr i dcl)
  (declare (xargs :measure (nfix (- (len (cdr (assoc typ dcl)))
                                    (nfix i)))))
  (let* ((descriptor (cdr (assoc typ dcl)))
         (i (nfix i))
         (slot-typ (nth i descriptor)))
    (cond
     ((zp ptr) nil)
     ((< i (len descriptor))
      (cond ((symbolp slot-typ)
             (s (+ ptr i) :PTR
                (s*-tags-witness typ ptr (+ 1 i) dcl)))
            (t
             (s (+ ptr i) :DATA
                (s*-tags-witness typ ptr (+ 1 i) dcl)))))
     (t nil))))

(defthm g-s*-tags-witness
  (implies (and (not (zp ptr))
                (integerp i)
                (<= 0 i)
                (< i (len (cdr (assoc typ dcl)))))
           (EQUAL (G addr
                     (S*-TAGS-WITNESS TYP PTR I DCL))
                  (if (member addr
                              (seq-int (+ ptr i)
                                       (- (len (cdr (assoc typ dcl))) i)))
                      (if (symbolp (nth (- addr ptr)
                                        (cdr (assoc typ dcl))))
                          :PTR
                        :DATA)
                    nil))))

(defthm s*-tags-ok-s-unforced
  (implies
   (not (member addr
                (seq-int (+ ptr (nfix i))
                         (- (len (cdr (assoc typ dcl)))
                            (nfix i)))))
   (equal (s*-tags-ok typ ptr i dcl (s addr val tags))
          (s*-tags-ok typ ptr i dcl tags))))

(in-theory (disable s*-tags-ok-s))

(defthm s*-tags-ok-s*-tags-witness
  (s*-tags-ok typ ptr i dcl
              (s*-tags-witness typ ptr i dcl)))

(defun tags-witness-fn (fn typ ptr i n ram dcl)
  (declare (xargs :measure
                  (if (equal fn :ALL)
                      (cons (+ 1 (nfix n))
                            (nfix (- (len (cdr (assoc typ dcl))) (nfix i))))
                    (cons (+ 1 (nfix n)) 0))))
  (if (equal fn :ALL)
      (let* ((descriptor (cdr (assoc typ dcl)))
             (slot-typ (nth i descriptor))
             (i (nfix i)))
        (cond ((zp ptr) nil)
              ((<= (len descriptor) i) nil)
              ((symbolp slot-typ)
               (s (+ ptr i) :PTR
                  (merge-tags (collect-fn :ONE slot-typ
                                          (g (+ ptr i) ram)
                                          i
                                          n ram dcl)
                              (tags-witness-fn :ONE slot-typ
                                               (g (+ ptr i) ram)
                                               i
                                               n ram dcl)
                              (tags-witness-fn :ALL typ
                                               ptr
                                               (+ 1 i)
                                               n ram dcl))))
              (t
               (s (+ ptr i) :DATA
                  (tags-witness-fn :ALL typ
                                   ptr
                                   (+ 1 i)
                                   n ram dcl)))))
    (let ((descriptor (cdr (assoc typ dcl))))
      (if (zp n)
          nil
        (if (zp ptr)
            nil
          (if (atom descriptor)
              nil
            (merge-tags (seq-int ptr (len (cdr (assoc typ dcl))))
                        (s*-tags-witness typ ptr 0 dcl)
                        (tags-witness-fn :ALL typ
                                         ptr
                                         0
                                         (- n 1)
                                         ram
                                         dcl))))))))

(defthm weird-optimization-lemma-1
  (implies (and (not (member addr addrs))
                (equal (g addr tags2) val))
           (equal (merge-tags addrs
                              (s addr val tags1)
                              tags2)
                  (merge-tags addrs
                              tags1
                              tags2))))

(defthm weird-optimization
  (implies (and (not (zp ptr))
                (integerp i)
                (<= 0 i)
                (< i (len (cdr (assoc typ dcl))))
                (tags-ok-fn :ALL typ ptr i n ram dcl tags))
           (equal (merge-tags (seq-int (+ ptr i)
                                       (- (len (cdr (assoc typ dcl))) i))
                              (s*-tags-witness typ ptr i dcl)
                              tags)
                  tags))
  :hints

; Subgoal numbers changed by Matt K. for v2-9 (probably needed because of
; change to call-stack).  Removed two identical subgoal :expand hints entirely
; after v8-0 in favor of a single "Goal" hint, to fix a failure that occurred
; when no longer expanding away LETs on right-hand sides of rewrite rules when
; storing the rules.

  (("Goal" :expand (SEQ-INT (+ I PTR) 1))))

(defthm weird-optimization-corollary
  (implies (and (not (zp ptr))
                (consp (cdr (assoc typ dcl)))
                (tags-ok-fn :ALL typ ptr 0 n ram dcl tags))
           (equal (merge-tags (seq-int ptr
                                       (len (cdr (assoc typ dcl))))
                              (s*-tags-witness typ ptr 0 dcl)
                              tags)
                  tags))
  :hints (("Goal" :use (:instance weird-optimization (i 0)))))


(defthm weird-optimization-part-2
  (implies (and (not (zp ptr))
                (integerp i)
                (<= 0 i)
                (< i (len (cdr (assoc typ dcl))))
                (tags-ok-fn :ALL typ ptr i n ram dcl tags))
           (s*-tags-ok typ ptr i dcl tags)))

(defthm positive-len
  (equal (< 0 (len x))
         (consp x)))

(defthm unique-implies-tags-exists
  (implies (unique (kollect-fn fn typ ptr i n ram dcl))
           (tags-ok-fn fn typ ptr i n ram dcl
                       (tags-witness-fn fn typ ptr i n ram dcl))))


(in-theory (disable kollect-fn))

; Now we assemble the various pieces.

(defthm g-mark-fn-2-via-kollect-fn
  (implies (and (unique (kollect-fn fn typ ptr i n ram dcl))
                (not (member addr (collect-fn fn typ ptr i n ram dcl))))
           (equal (g addr (mark-fn fn typ ptr i n ram dcl))
                  (g addr ram)))
  :hints (("Goal" :use unique-implies-tags-exists
           :in-theory (disable unique-implies-tags-exists)))
  :rule-classes nil)

(defthm collect-fn-mark-fn-via-kollect-fn
  (implies (and (unique (kollect-fn fn2 typ2 ptr2 i2 n2 ram dcl))
                (unique (kollect-fn fn1 typ1 ptr1 i1 n1 ram dcl))
                (not (intersectp (kollect-fn fn2 typ2 ptr2 i2 n2 ram dcl)
                                 (kollect-fn fn1 typ1 ptr1 i1 n1 ram dcl))))
           (equal (collect-fn fn1 typ1 ptr1 i1 n1
                              (mark-fn fn2 typ2 ptr2 i2 n2 ram dcl)
                              dcl)
                  (collect-fn fn1 typ1 ptr1 i1 n1 ram dcl)))

  :hints (("Goal"
           :use
           ((:instance unique-implies-tags-exists
                       (fn fn2) (typ typ2) (ptr ptr2) (i i2) (n n2))
            (:instance unique-implies-tags-exists
                       (fn fn1) (typ typ1) (ptr ptr1) (i i1) (n n1))
            (:instance
             collect-fn-mark-fn
             (tags (merge-tags
                    (kollect-fn fn2 typ2 ptr2 i2 n2 ram dcl)
                    (TAGS-WITNESS-FN FN2 TYP2 PTR2 I2 N2 RAM DCL)
                    (TAGS-WITNESS-FN FN1 TYP1 PTR1 I1 N1 RAM DCL)))))
           :in-theory (disable unique-implies-tags-exists
                               collect-fn-mark-fn)))
  :rule-classes nil)

; Now I get rid of kollect-fn by focusing on the fn=:ONE case only.

(defthm challenge-theorem-1-lemma
  (implies (and (not (member addr (collect-fn :ONE typ ptr i n ram dcl)))
                (unique (collect-fn :ONE typ ptr i n ram dcl)))
           (equal (g addr (mark-fn :ONE typ ptr i n ram dcl))
                  (g addr ram)))

  :hints (("Goal" :use
           (:instance g-mark-fn-2-via-kollect-fn (fn :ONE))
           :in-theory (enable kollect-fn))))

(defthm challenge-theorem-1
  (implies (and (not (member addr (collect typ ptr n ram dcl)))
                (unique (collect typ ptr n ram dcl)))
           (equal (g addr (mark typ ptr n ram dcl))
                  (g addr ram))))

(defthm challenge-theorem-2-lemma
  (implies (unique (append (collect-fn :ONE typ2 ptr2 i2 n2 ram dcl)
                           (collect-fn :ONE typ1 ptr1 i1 n1 ram dcl)))
           (equal (collect-fn :ONE typ1 ptr1 i1 n1
                              (mark-fn :ONE typ2 ptr2 i2 n2 ram dcl)
                              dcl)
                  (collect-fn :ONE typ1 ptr1 i1 n1 ram dcl)))

    :hints (("Goal" :use
           (:instance collect-fn-mark-fn-via-kollect-fn
                      (fn2 :ONE)
                      (fn1 :ONE))
           :in-theory (enable kollect-fn))))

(defthm challenge-theorem-2
  (implies
   (and (unique (append (collect typ1 ptr1 n1 ram dcl)
                        (collect typ2 ptr2 n2 ram dcl)
                        (collect typ3 ptr3 n3 ram dcl)))
        (not (member addr (append (collect typ1 ptr1 n1 ram dcl)
                                  (collect typ2 ptr2 n2 ram dcl)
                                  (collect typ3 ptr3 n3 ram dcl)))))
   (equal
    (g addr (compose-bab typ1 ptr1 n1
                         typ2 ptr2 n2
                         typ3 ptr3 n3
                         ram dcl))
    (g addr ram))))


(defthm challenge-theorem-3
  (implies (unique (append (collect typ1 ptr1 n1 ram dcl)
                           (collect typ2 ptr2 n2 ram dcl)))
           (equal (mark typ1 ptr1 n1 (mark typ2 ptr2 n2 ram dcl)
                        dcl)
                  (mark typ2 ptr2 n2 (mark typ1 ptr1 n1 ram dcl)
                        dcl)))
  :hints
  (("Goal"
    :use
    ((:instance unique-implies-tags-exists (fn :ONE)
                (typ typ1)
                (ptr ptr1)
                (i i)
                (n n1))
     (:instance unique-implies-tags-exists (fn :ONE)
                (typ typ2)
                (ptr ptr2)
                (i i)
                (n n2))
     (:instance
      mark-fn-mark-fn (fn1 :ONE)
      (fn2 :ONE)
      (i2 i)
      (i1 i)
      (tags (merge-tags (collect-fn :ONE typ1 ptr1 i n1 ram dcl)
                        (tags-witness-fn :ONE typ1 ptr1 i n1 ram dcl)
                        (tags-witness-fn :ONE typ2 ptr2 i n2 ram dcl)))))
    :in-theory
    (e/d (kollect-fn)
         (unique-implies-tags-exists mark-fn-mark-fn)))))


; This theorem is proved just to illustrate the basic link between
; unique disjoint collection and the existence of a consistent tagging
; for two pointer structures.

(defthm unique-collection-implies-exists-ok-tagging
  (implies (unique (append (collect typ1 ptr1 n1 ram dcl)
                           (collect typ2 ptr2 n2 ram dcl)))
           (let ((tags
                  (merge-tags (collect typ1 ptr1 n1 ram dcl)
                              (tags-witness-fn :ONE typ1 ptr1 0 n1 ram dcl)
                              (tags-witness-fn :ONE typ2 ptr2 0 n2 ram dcl))))
             (and (tags-ok-fn :ONE typ1 ptr1 0 n1 ram dcl tags)
                  (tags-ok-fn :ONE typ2 ptr2 0 n2 ram dcl tags))))
  :hints
  (("Goal"
    :use ((:instance collect-is-collect-fn
                     (typ typ1) (ptr ptr1) (i 0) (n n1))
          (:instance collect-is-collect-fn
                     (typ typ2) (ptr ptr2) (i 0) (n n2))
          (:instance unique-implies-tags-exists
                     (fn :ONE) (typ typ1) (ptr ptr1) (i 0) (n n1))
          (:instance unique-implies-tags-exists
                     (fn :ONE) (typ typ2) (ptr ptr2) (i 0) (n n2))
          (:instance mark-fn-mark-fn
                     (fn1 :ONE)
                     (fn2 :ONE)
                     (i2 0)
                     (i1 0)
                     (tags
                      (merge-tags
                       (collect-fn :ONE typ1 ptr1 0 n1 ram dcl)
                       (tags-witness-fn :ONE typ1 ptr1 0 n1 ram dcl)
                       (tags-witness-fn :ONE typ2 ptr2 0 n2 ram dcl)))))
    :in-theory (e/d (kollect-fn)
                    (unique-implies-tags-exists
                     mark-fn-mark-fn
                     collect-is-collect-fn)))))


