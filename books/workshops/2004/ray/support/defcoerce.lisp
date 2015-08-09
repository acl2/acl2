(in-package "ACL2")

#|

  defcoerce.lisp
  ~~~~~~~~~~~~~~

Author: Sandip Ray
Date: 12/10/2004

This book implements a macro suggested by John Matthews (and described
and implemented independently by me and John/Daron for the ACL2
workshop. The idea is to define a macro defcoerce that takes a stobj
and returns two functions copy-from and copy-to so that each is
identity in the logic, but has the property that copy-from returns an
ordinary object while copy-to returns a single-threaded object by
copying the fields of the ordinary object. This has been used by
John/Daron in implementing symbolic verification of sequential
programs and by me in implementing defpun-exec with stobjs. (The
defpun-exec book with stobjs here does not use the defcoerce
macro, since that book is still messy.

Acknowledgements:

1. Thanks to John Matthews for suggesting the idea of defcoerce.
2. Thanks to the referees in the workshop for suggesting that I
implement it.

Known issues:

1. The macro does not work for stobjs with no array field at all. (In
the defpun-exec with defcoerce I dont use the macro unless there is
some array field, which is why the negligence.)

2.It also does not work with types T for arrays. I think I will be
able to handle that soon. But so far I have not done it.

Note on the implementation:

My implementation is different from the one that John and Daron have
done. (This is based on my impression reading their paper, but not
looking at their code, so I might be a little off.) The key point in
my implementation is the use of functional instantiation on generic
theorems. For arrays in particular, it is often nice to show that the
nth i of the array is the same as that in the copy. I regularly take
this approach to show that an array is equal to the copy. In this
work, therefore, I take the opportunity to define such generic set of
theorems and show how to functionally instantiate them. Admittedly I
need a lot of theorems in the macro. I should have just gone for an
inductive proof over update-nth. However, there is a certain amount of
elegance in the functional instantiation stuff that I like, and also I
think this is one thing that ACL2 users should use more often. Thus I
am inclined to do it this way. Also I think this way makes the macro
more robust (although as they say the taste of the pudding....:->)

|#

;; We use some arithmetic books. As is customary with me in recent
;; days, I will simply use Robert's arithmetic-2 library.

;; The only real issue in defining the functions copy-from and copy-to
;; are in handling arrays. So I will simply focus on this case for
;; now.

;; Defining the functions copy-from-stor and copy-to-stor requires several
;; theorems between nth and update-nth. I use the version of these theorems
;; that I have used for the verification of a stobj-based quicksort.

(in-theory (enable nth update-nth))

(defthm nth-update-nth-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (nth n (update-nth m v l)) (nth n l))))

(defthm nth-update-nth-same
  (implies (equal (nfix n) (nfix m))
           (equal (nth n (update-nth m v l)) v)))

(defthm update-nth-update-nth-same
  (equal (update-nth n v (update-nth n x l))
         (update-nth n v l)))

(defthm update-nth-update-nth-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (update-nth n v (update-nth m x l))
                  (update-nth m x (update-nth n v l))))
  :rule-classes ((:rewrite :loop-stopper ((n m)))))

(defthm len-update-nth-reduction
  (implies (natp i)
           (equal (len (update-nth i v l))
                  (if (< i (len l)) (len l) (1+ i)))))

(defthm update-nth-true-listp
  (implies (force (and (natp i)
                       (< i (len l))))
           (equal (true-listp (update-nth i v l))
                  (true-listp l))))

(in-theory (disable nth update-nth))

(local
 ;; [Jared] changed this to use arithmetic-3 instead of 2
 (include-book "arithmetic-3/bind-free/top" :dir :system))

;; Ok so how does it all work? Given an array field we define the
;; function copy-from-array as follows.

; The following was removed with the addition of natp-compound-recognizer to
; ACL2 2.9.2.
;(local
; (defthm natp-compound-recognizer
;   (iff (natp n)
;        (and (integerp n)
;             (<= 0 n)))
;   :rule-classes :compound-recognizer))

(local
 (in-theory (disable natp)))

(defun snoc (x e)
  (declare (xargs :guard (true-listp x)))
  (if (endp x) (list e) (cons (first x) (snoc (rest x) e))))

(defthm nth-snoc-reduction
  (implies (natp i)
           (equal (nth i (snoc x e))
                  (cond ((< i (len x)) (nth i x))
                        ((= i (len x)) e)
                        (t nil))))
  :hints (("Goal"
           :in-theory (enable nth)
           :do-not '(eliminate-destructors generalize fertilize))))


;; END generic stuff.

;; The geenric book contains the generic theory that I instantiate.


(include-book "generic")

#|

This example shows what theorems I need and how I prove the entire
thing. This is a good example and also shows how the macro works.

(defstobj stb$
  (fld1 :type (array (unsigned-byte 31) (64)) :initially 0 :resizable t)
  (fld2 :type (unsigned-byte 31) :initially 0))

(defun copy-from-stb$-fld1-aux (len stb$)
  (declare (xargs :stobjs stb$
                  :guard (and (natp len)
                              (<= len (fld1-length stb$)))))
  (if (zp len) nil
    (snoc (copy-from-stb$-fld1-aux (1- len) stb$)
          (fld1i (1- len) stb$))))

(defun copy-from-stb$-fld1 (stb$)
  (declare (xargs :stobjs stb$))
  (copy-from-stb$-fld1-aux (fld1-length stb$) stb$))


(local
 (defthm copy-from-stb$-fld1-len
   (implies (natp len)
            (equal (len (copy-from-stb$-fld1-aux len stb$))
                   len))))

(local
 (defthm nth-copy-from-stb$-fld1
   (implies (and (natp i)
                 (natp len)
                 (< i len))
            (equal (nth i (copy-from-stb$-fld1-aux len stb$))
                   (nth i (nth 0 stb$))))))


(local (defthm fld-p-implies-true-listp-aux
         (implies (fld1p x)
                  (true-listp x))))

(local
 (defthm stb$p-implies-true-listp
   (implies (stb$p stb$)
            (true-listp (nth *fld1i* stb$)))
   :rule-classes :forward-chaining))


(local
 (defthmd copy-from-stb$-fld1-identity-aux
        (implies (stb$p stb$)
                 (equal (copy-from-stb$-fld1-aux (len (nth *fld1i* stb$)) stb$)
                        (nth *fld1i* stb$)))
        :otf-flg t
        :hints (("Goal"
                 :do-not-induct t
                 :in-theory (disable stb$p |copy from field is identity|)
                 :use ((:instance
                        (:functional-instance
                         |copy from field is identity|
                         (fldf (lambda () *fld1i*))
                         (copy-from-fld
                          (lambda (x)
                            (copy-from-stb$-fld1-aux (len (nth 0 x))
                                                 x))))
                        (x stb$)))))))

(local
 (defthm copy-from-stb$-fld1-identity
   (implies (stb$p stb$)
            (equal (copy-from-stb$-fld1 stb$)
                   (nth *fld1i* stb$)))
   :hints (("Goal"
            :use ((:instance copy-from-stb$-fld1-identity-aux))))))

(in-theory (disable copy-from-stb$-fld1))

(defun stb$-fld1p-logic (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (unsigned-byte-p 31 (car x))
           (stb$-fld1p-logic (cdr x)))
    (equal x nil)))

(defun copy-to-stb$-fld1-aux (l len stb$)
  (declare (xargs :stobjs stb$
                  :verify-guards nil
                  :guard (and (natp len)
                              (stb$-fld1p-logic l)
                              (<= len (len l))
                              (<= len (fld1-length stb$)))))
  (if (zp len) stb$
    (let ((stb$ (copy-to-stb$-fld1-aux l (1- len) stb$)))
      (update-fld1i (1- len)
                    (nth (1- len) l)
                    stb$))))


(defthm other-fields-are-untouched
  (implies (and (not (equal i *fld1i*))
                (natp i))
           (equal (nth i (copy-to-stb$-fld1-aux l len stb$))
                  (nth i stb$)))
  :hints (("Goal"
           :induct (copy-to-stb$-fld1-aux l len stbS))))

(defthm stb$p-logic-implies-true-listp
  (implies (stb$-fld1p-logic l)
           (true-listp l)))

(defthm stb$p-logic-implies-unsigned-byte-p
  (implies (and (stb$-fld1p-logic l)
                (natp i)
                (< i (len l)))
           (unsigned-byte-p 31 (nth i l)))
  :hints (("Goal"
           :in-theory (enable nth))))

(defthm copy-to-stb$-fld1-aux-true-listp
  (implies (true-listp (nth *fld1i* stb$))
           (true-listp (nth *fld1i* (copy-to-stb$-fld1-aux l len stb$))))
  :rule-classes :type-prescription)

(defthm copy-to-stb$-fld1-len
  (implies (natp len)
           (equal (len (nth *fld1i* (copy-to-stb$-fld1-aux l len stb$)))
                  (if (< len (len (nth *fld1i* stb$)))
                      (len (nth *fld1i* stb$))
                    len))))

(verify-guards  copy-to-stb$-fld1-aux
                :hints (("Goal" :in-theory (disable unsigned-byte-p))))


(defthm nth-copy-to-fld1-stb$
  (implies (and (natp i)
                (natp len)
                (< i len))
           (equal (nth i (nth *fld1i* (copy-to-stb$-fld1-aux l len stb$)))
                  (nth i l))))


(defthm fld1p-implies-true-listp
  (implies (fld1p l)
           (true-listp l)))

(defthmd copy-to-fld1-identity-aux
  (implies (and (stb$-fld1p-logic l)
                (equal (len l) (len (nth *fld1i* stb$)))
                (fld1p (nth *fld1i* stb$)))
           (equal (nth *fld1i*
                       (copy-to-stb$-fld1-aux l
                                              (len (nth *fld1i* stb$))
                                              stb$))
                  l))
  :hints (("Goal"
           :in-theory (disable |copy to field is identity|)
           :use ((:instance
                  (:functional-instance
                   |copy to field is identity|
                   (copy-to-fld
                    (lambda (l x)
                      (copy-to-stb$-fld1-aux l (len l)
                                             x)))
                   (fld (lambda () *fld1i*)))
                  (x stb$))))))

(defun copy-to-stb$-fld1 (l stb$)
  (declare (xargs :stobjs stb$
                  :guard (and (stb$-fld1p-logic l)
                              (= (len l) (fld1-length stb$)))))
  (copy-to-stb$-fld1-aux l (fld1-length stb$) stb$))


(defthm update-nth-true-listp
  (implies (force (and (natp i)
                       (< i (len l))))
           (equal (true-listp (update-nth i v l))
                  (true-listp l)))
  :hints (("Goal"
           :in-theory (enable update-nth))))

(defthm copy-to-stb$-fld1-aux-len
  (implies (stb$p stb$)
           (equal (len (copy-to-stb$-fld1-aux l len stb$))
                  (len stb$))))

(defthm copy-to-stb$-fld1-s-len
  (implies (stb$p stb$)
           (equal (len (copy-to-stb$-fld1 l stb$))
                  (len stb$))))


(defthm copy-to-stb$-fld1-is-truelistp-aux
  (implies (stb$p stb$)
           (true-listp (copy-to-stb$-fld1-aux l len stb$))))

(defthm copy-to-stb$-is-true-listp
  (implies (stb$p stb$)
           (true-listp (copy-to-stb$-fld1 l stb$))))

(defthm copy-to-array-identity
  (implies (and (stb$-fld1p-logic l)
                (equal (len l) (len (nth *fld1i* stb$)))
                (fld1p (nth *fld1i* stb$)))
           (equal (nth *fld1i* (copy-to-stb$-fld1 l stb$))
                  l))
  :hints (("Goal"
           :use copy-to-fld1-identity-aux)))

(in-theory (disable copy-to-stb$-fld1))

;; OK so these are the theorems that I prove for each array component of the
;; stobj. Then we sum it up for all.

(defun stb$p-logic (l)
  (declare (xargs :guard t))
  (and (true-listp l)
       (equal (len l) 2)
       (stb$-fld1p-logic (nth *fld1i* l))
       (unsigned-byte-p 31 (nth *fld2* l))))

(defun copy-from-stb$ (stb$)
  (declare (xargs :stobjs stb$))
  (list (copy-from-stb$-fld1 stb$)
        (fld2 stb$)))

(defthm len-copy-from-stb$
  (equal (len (copy-from-stb$ stb$)) 2))

(defthm all-copy-from-identity
  (implies (and (natp i)
                (stb$p stb$)
                (< i (len stb$)))
           (equal (nth i (copy-from-stb$ stb$))
                  (nth i stb$)))
  :hints (("Goal"
           :cases ((equal i 0) (equal i 1)))))

(defthm copy-from-stb$-identity
  (implies (stb$p stb$)
           (equal (copy-from-stb$ stb$)
                  stb$))
  :hints (("Goal"
           :in-theory (disable copy-from-stb$
                               |copy from is identity|)
           :use ((:instance
                  (:functional-instance
                   |copy from is identity|
                   (hypos (lambda (x) (stb$p x)))
                   (copy-from
                    (lambda (x) (copy-from-stb$ x))))
                  (x stb$))))))

;; And finally copy-to

(defun copy-to-stb$ (l stb$)
  (declare (xargs :stobjs stb$
                  :guard (and (stb$p-logic l)
                              (equal (len (nth *fld1i* l))
                                     (fld1-length stb$)))
                  :guard-hints (("Goal"
                                 :do-not-induct t))))
  (let* ((stb$ (copy-to-stb$-fld1 (nth 0 l) stb$))
         (stb$ (update-fld2 (nth 1 l) stb$)))
    stb$))

(defthm nth-copy-to-stb$
  (implies (and (natp i)
                (stb$p-logic l)
                (stb$p stb$)
                (equal (len (nth *fld1i* l))
                       (len (nth *fld1i* stb$)))
                (< i (len l)))
           (equal (nth i (copy-to-stb$ l stb$))
                  (nth i l)))
  :hints (("Goal"
           :cases ((equal i 0) (equal i 1)))))

(defthm copy-to-stb$-true-listp
  (implies (and (stb$p stb$)
                (stb$p-logic l))
           (true-listp (copy-to-stb$ l stb$)))
  :hints (("Goal"
           :do-not-induct t)))

(defthm copy-to-stb$-identity
  (implies (and (stb$p stb$)
                (stb$p-logic l)
                (equal (len (nth *fld1i* l))
                       (len (nth *fld1i* stb$))))
           (equal (copy-to-stb$ l stb$)
                  l))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   |copy to whole is identity|
                   (copy-to
                    (lambda (l x)
                      (copy-to-stb$ l x)))
                   (hypotheses
                    (lambda (l x)
                      (and (stb$p x)
                           (stb$p-logic l)
                           (equal (len (nth *fld1i* l))
                                  (len (nth *fld1i* x)))))))
                  (x stb$))))))


|#

;; The function array-thms below creates a list of functions and theorems for
;; each array field.

(defun array-thms (stb etype fld)
  (declare (xargs :mode :program))
  (let* ((fld-length (packn (list fld '-length)))
         (fldi* (packn (list '* fld 'i*)))
         (fldp (packn (list fld 'p)))
         (etype (translate-declaration-to-guard etype 'y nil))
         (etype-name (if (consp etype) (car etype) t))
         (fldi (packn (list fld 'i)))
         (update-fldi (packn (list 'update- fldi)))
         (stbp (packn (list stb 'p)))
         (copy-from-fld (packn (list 'copy-from- stb '- fld)))
         (copy-from-fld-aux (packn (list copy-from-fld '-aux)))
         (copy-from-fld-len (packn (list copy-from-fld '-len)))
         (nth-copy-from-fld (packn (list 'nth- copy-from-fld)))
         (fldp-implies-true-listp (packn (list stbp fld '-implies-true-listp)))
         (stbp-implies-true-listp (packn (list stbp fldp-implies-true-listp)))
         (copy-from-fld-identity (packn (list copy-from-fld '-identity)))
         (copy-from-fld-identity-aux (packn (list copy-from-fld-identity
                                                  '-aux)))
         (fldp-logic (packn (list stb '- fld 'p-logic)))
         (copy-to-fld (packn (list 'copy-to- stb '- fld)))
         (copy-to-fld-aux (packn (list copy-to-fld '-aux)))
         (other-untouched (packn (list stb '- fld '-other-untouched)))
         (fldp-logic-implies-truelistp (packn (list fldp-logic
                                                   '-implies-truelistp)))
         (fldp-logic-implies-type (packn (list fldp-logic '-implies- etype-name)))
         (copy-to-fld-aux-true-listp (packn (list copy-to-fld-aux
                                                '-truelistp)))
         (copy-to-fld-len (packn (list copy-to-fld-aux '-len)))
         (nth-copy-to-fld (packn (list 'nth- copy-to-fld)))
         (copy-to-fld-identity (packn (list copy-to-fld '-identity)))
         (copy-to-fld-identity-aux (packn (list copy-to-fld-identity '-aux)))
         (copy-to-fld-aux-len-whole (packn (list copy-to-fld-aux '-len-whole)))
         (copy-to-fld-len-whole (packn (list copy-to-fld '-len-whole)))
         (copy-to-fld-is-true-listp-aux (packn (list copy-to-fld
                                                     '-is-true-listp-aux)))
         (copy-to-fld-is-true-listp (packn (list copy-to-fld
                                                 '-is-true-listp))))



    (list

     `(defun ,copy-from-fld-aux (len ,stb)
       (declare (xargs :stobjs ,stb
                       :guard (and (natp len)
                                   (<= len (,fld-length ,stb)))))
       (if (zp len) nil
         (snoc (,copy-from-fld-aux (1- len) ,stb)
               (,fldi (1- len) ,stb))))

     `(defun ,copy-from-fld (,stb)
       (declare (xargs :stobjs ,stb))
       (,copy-from-fld-aux (,fld-length ,stb) ,stb))

     `(local
       (defthm ,copy-from-fld-len
         (implies (natp len)
                  (equal (len (,copy-from-fld-aux len stb))
                         len))))


     `(local
       (defthm ,nth-copy-from-fld
         (implies (and (natp i)
                       (natp len)
                       (< i len))
                  (equal (nth i (,copy-from-fld-aux len stb))
                         (nth i (nth ,fldi* stb))))))


     `(local
       (defthm ,fldp-implies-true-listp
         (implies (,fldp l)
                  (true-listp l))))


     `(local
       (defthm ,stbp-implies-true-listp
         (implies (,stbp stb)
                  (true-listp (nth ,fldi* stb)))
         :rule-classes :forward-chaining))

     `(local
       (defthmd ,copy-from-fld-identity-aux
         (implies (,stbp stb)
                  (equal (,copy-from-fld-aux (len (nth ,fldi* stb)) stb)
                         (nth ,fldi* stb)))
        :hints (("Goal"
                 :in-theory (disable ,stbp
                                     |copy from field is identity|)
                 :use ((:instance
                        (:functional-instance
                         |copy from field is identity|
                         (fldf (lambda () ,fldi*))
                         (copy-from-fld
                          (lambda (x)
                            (,copy-from-fld-aux (len (nth ,fldi* x))
                                                 x))))
                        (x stb)))))))


     `(local
       (defthm ,copy-from-fld-identity
         (implies (,stbp stb)
                  (equal (,copy-from-fld stb)
                         (nth ,fldi* stb)))
        :hints (("Goal"
                 :use ((:instance ,copy-from-fld-identity-aux))))))

     `(in-theory (disable ,copy-from-fld))


      `(defun ,fldp-logic (x)
        (declare (xargs :guard t))
        (if (consp x)
            (let ((y (car x)))
              (and ,etype
                   (,fldp-logic (cdr x))))
         (equal x nil)))

     `(defun ,copy-to-fld-aux (l len ,stb)
        (declare (xargs :stobjs ,stb
                        :verify-guards nil
                        :guard (and (natp len)
                                   (,fldp-logic l)
                                   (<= len (len l))
                                   (<= len (,fld-length ,stb)))))
       (if (zp len) ,stb
         (let ((,stb (,copy-to-fld-aux l (1- len) ,stb)))
           (,update-fldi (1- len)
                         (nth (1- len) l)
                         ,stb))))

     `(local
       (defthm ,other-untouched
         (implies (and (not (equal i ,fldi*))
                     (natp i))
                  (equal (nth i (,copy-to-fld-aux l len stb))
                         (nth i stb)))
         :hints (("Goal"
                  :induct (,copy-to-fld-aux l len stb)))))



     `(local
       (defthm ,fldp-logic-implies-truelistp
         (implies (,fldp-logic l)
                  (true-listp l))))

      `(local
        (defthm ,fldp-logic-implies-type
          (implies (and (,fldp-logic l)
                        (natp i)
                        (< i (len l)))
                 (let ((y (nth i l)))
                   ,etype))
        :hints (("Goal"
                 :in-theory (enable nth)))))



     `(local
       (defthm ,copy-to-fld-aux-true-listp
         (implies (true-listp (nth ,fldi* stb))
                  (true-listp (nth ,fldi* (,copy-to-fld-aux l len stb))))
         :rule-classes :type-prescription))

     `(local
       (defthm ,copy-to-fld-len
         (implies (natp len)
                  (equal (len (nth ,fldi* (,copy-to-fld-aux l len stb)))
                         (if (< len (len (nth ,fldi* stb)))
                             (len (nth ,fldi* stb))
                           len)))))


     `(verify-guards ,copy-to-fld-aux
                    :hints (("Goal" :in-theory (disable ,etype-name))))


     `(local
        (defthm ,nth-copy-to-fld
          (implies (and (natp i)
                        (natp len)
                        (< i len))
                   (equal (nth i (nth ,fldi* (,copy-to-fld-aux l len stb)))
                          (nth i l)))))



     `(local
       (defthmd ,copy-to-fld-identity-aux
         (implies (and (,fldp-logic l)
                       (equal (len l) (len (nth ,fldi* stb)))
                       (,fldp (nth ,fldi* stb)))
                  (equal (nth ,fldi*
                              (,copy-to-fld-aux
                               l
                               (len (nth ,fldi* stb))
                               stb))
                         l))
         :hints (("Goal"
                  :in-theory (disable |copy to field is identity|)
                  :use ((:instance
                         (:functional-instance
                          |copy to field is identity|
                          (copy-to-fld
                           (lambda (l x)
                             (,copy-to-fld-aux l (len l)
                                               x)))
                          (fld (lambda () ,fldi*)))
                       (x stb)))))))


     `(defun ,copy-to-fld (l ,stb)
        (declare (xargs :stobjs ,stb
                        :guard (and (,fldp-logic l)
                                    (= (len l) (,fld-length ,stb)))))
        (,copy-to-fld-aux l (,fld-length ,stb) ,stb))

     `(local
       (defthm ,copy-to-fld-aux-len-whole
         (implies (,stbp stb)
                  (equal (len (,copy-to-fld-aux l len stb))
                         (len stb)))))


     `(local
       (defthm ,copy-to-fld-len-whole
         (implies (,stbp stb)
                  (equal (len (,copy-to-fld l stb))
                         (len stb)))))



     `(local
       (defthm ,copy-to-fld-is-true-listp-aux
         (implies (,stbp stb)
                  (true-listp (,copy-to-fld-aux l len stb)))))

     `(local
       (defthm ,copy-to-fld-is-true-listp
         (implies (,stbp stb)
                  (true-listp (,copy-to-fld l stb)))))


     `(local
       (defthm ,copy-to-fld-identity
         (implies (and (,fldp-logic l)
                       (equal (len l) (,fld-length stb))
                       (equal (len (nth ,fldi* stb)) (,fld-length stb))
                       (,fldp (nth ,fldi* stb)))
                  (equal (nth ,fldi* (,copy-to-fld l stb))
                         l))
         :hints (("Goal"
                  :do-not-induct t
                  :use ,copy-to-fld-identity-aux))))

     `(in-theory (disable ,copy-to-fld))

     )))

;; OK so I need to figure out the type of each component. I initially did it by
;; looking over the world for each component of the array. But now that I am
;; installing these functions while defining the stobj, I do not have to do
;; that any more. I merely get the fields from the type declaration of the
;; stobj.

(defun get-type-of (fld)
  (cond ((endp fld) t)
        ((eq (car fld) :type) (cadr fld))
        (t (get-type-of (rest fld)))))

(defun resizable-fldp (fld)
  (cond ((endp fld) nil)
        ((eq (car fld) :resizable) (cadr fld))
        (t (resizable-fldp (cdr fld)))))

;; That really simplifies things from the existing code. Thanks a lot to John
;; Matthews and Daron Vroon for suggesting this in their ACL2 workshop talk.


;; Now we do create array-thms for every array field using the following
;; recursive function. In a way, this function is the heart of this tool.


(defun defcoerce-fn-aux (stb flds fldsp-logic cases lenps copy-from-flds
                             copy-to-flds events len)
  (declare (xargs :mode :program))
  (if (endp flds)

      ;; Put everything together here.
      (let* ((stbp (packn (list stb 'p)))
             (stbp-logic (packn (list stbp '-logic)))
             (copy-from (packn (list 'copy-from- stb)))
             (copy-to (packn (list 'copy-to- stb)))
             (lenps (if (atom lenps) t lenps))
             (len-copy-from (packn (list 'len- copy-from)))
             (all-identity-copy-from (packn (list 'all-identity- copy-from)))
             (copy-from-identity (packn (list copy-from '-identity)))
             (nth-copy-to (packn (list 'nth- copy-to)))
             (copy-to-true-listp (packn (list copy-to '-truelistp)))
             (copy-to-identity (packn (list copy-to '-identity))))

        (append

         events

         (list
          `(defun ,stbp-logic (l)
             (declare (xargs :guard t))
             (and (true-listp l)
                  (equal (len l) ,len)
                  ,@fldsp-logic))

          `(defun ,copy-from (,stb)
             (declare (xargs :stobjs ,stb))
             ,(cons 'list copy-from-flds))

         `(local
           (defthm ,len-copy-from
             (equal (len (,copy-from ,stb)) ,len)))

         `(local
           (defthm ,all-identity-copy-from
             (implies (and (natp i)
                           (,stbp ,stb)
                           (< i (len ,stb)))
                      (equal (nth i (,copy-from ,stb))
                             (nth i ,stb)))
             :otf-flg t
             :hints (("Goal"
                      :do-not-induct t
                      :cases (,@cases)))))

         `(defthm ,copy-from-identity
            (implies (,stbp stb)
                     (equal (,copy-from stb)
                            stb))
            :hints (("Goal"
                     :in-theory (disable ,copy-from
                                         |copy from is identity|)
                     :use ((:instance
                            (:functional-instance
                             |copy from is identity|
                             (hypos (lambda (x) (,stbp x)))
                             (copy-from
                              (lambda (x) (,copy-from x))))
                            (x stb))))))

         `(in-theory (disable ,copy-from))

         ;; And finally copy-to

         `(defun ,copy-to (l ,stb)
            (declare (xargs :stobjs ,stb
                            :guard (and (,stbp-logic l)
                                        ,@lenps)
                            :guard-hints (("Goal"
                                           :do-not-induct t))))

            (let* (,@copy-to-flds)
              ,stb))

         `(local
           (defthm ,nth-copy-to
             (implies (and (natp i)
                           (,stbp-logic l)
                           (,stbp ,stb)
                           (< i (len l))
                           ,@lenps)
                      (equal (nth i (,copy-to l ,stb))
                             (nth i l)))
           :hints (("Goal"
                    :cases (,@cases)))))

         `(local
           (defthm ,copy-to-true-listp
             (implies (and (,stbp stb)
                           (,stbp-logic l))
                      (true-listp (,copy-to l stb)))))


         `(defthm ,copy-to-identity
            (implies (and (,stbp ,stb)
                          (,stbp-logic l)
                          ,@lenps)
                     (equal (,copy-to l ,stb)
                            l))
            :hints (("Goal"
                     :in-theory (disable |copy to whole is identity|)
                     :use ((:instance
                            (:functional-instance
                             |copy to whole is identity|
                             (copy-to
                              (lambda (l x)
                                (,copy-to l x)))
                             (hypotheses
                              (lambda (l x)
                                (and (,stbp x)
                                     (,stbp-logic l)
                                     (let ((,stb x))
                                       ,@lenps)))))
                            (x ,stb))))))

         `(in-theory (disable ,copy-to)))))


    (if (atom (car flds))

        ;; For inline fields
        (defcoerce-fn-aux stb
          (cdr flds)
          fldsp-logic
          cases
          lenps
          copy-from-flds
          copy-to-flds
          events
          len)

      ;; The real stuff now.... Notice that this function is now more
      ;; complicated than before. This is because I am generating everything
      ;; "on the fly" rather than
      (let* ((fld (car flds))
             (fld-name (car fld))
             (type (get-type-of (cdr fld))))
        (if (and (consp type)
                 (eq (car type) 'array))
            (let* ((fldp-logic (packn (list stb '- fld-name 'p-logic)))
                   (fld-length (packn (list fld-name '-length)))
                   (etype (cadr type))
                   (copy-from-fld (packn (list 'copy-from- stb '- fld-name)))
                   (copy-to-fld (packn (list 'copy-to- stb '- fld-name))))
              (defcoerce-fn-aux
                stb
                (cdr flds)

                ;; add the condition that this particular index is a consp.
                ;; Note: Here I am going on creating the fldsp list so that I
                ;; can finally define the stbp predicate. But of course this
                ;; means that I need to create a predicate called fldp for
                ;; every field of the stobj.


                 (append (if (resizable-fldp fld)

                             ;; Do not have the length parameter for resizable
                             ;; arrays.

                             (list `(consp (nth ,len l))
                                   `(,fldp-logic (nth ,len l)))
                           (list `(consp (nth ,len l))
                                 `(,fldp-logic (nth ,len l))
                                 `(equal (len (nth ,len l))
                                         ,(caaddr type))))
                        fldsp-logic)

                (cons `(equal i ,len) cases)

                (snoc lenps `(equal (len (nth ,len l))
                                    (,fld-length ,stb)))

                (snoc copy-from-flds `(,copy-from-fld ,stb))

                (snoc  copy-to-flds `(,stb (,copy-to-fld (nth ,len l) ,stb)))

                 (append (array-thms stb etype fld-name)
                         events)

                (1+ len)))

          ;; The non-array case: This part is obviously much easier....:->:->

          (let* ((update-fld (packn (list 'update- fld-name))))
              (defcoerce-fn-aux
                stb
                (cdr flds)

                ;; add the condition that this particular index is a consp.
                ;; Note: Here I am going on creating the fldsp list so that I
                ;; can finally define the stbp predicate. But of course this
                ;; means that I need to create a predicate called fldp for
                ;; every field of the stobj.

                (snoc fldsp-logic `(let* ((y (nth ,len l)))
                                     ,(if (translate-declaration-to-guard type
                                                                          'y
                                                                          nil)
                                          (translate-declaration-to-guard type
                                                                          'y
                                                                          nil)
                                        T)))

                (cons `(equal i ,len) cases)

                lenps

                (snoc copy-from-flds `(,fld-name ,stb))

                (snoc copy-to-flds `(,stb (,update-fld (nth ,len l) ,stb)))

                events

                (1+ len))))))))


;; OK so I am done with defining the function. Now let us package everything up
;; in a macro.

(defun defcoerce-fn (stb-def)
  (declare (xargs :mode :program))
  `(encapsulate
    ()
    (defstobj ,@stb-def)
    ,@(defcoerce-fn-aux
        (car stb-def) ;; stb
        (cdr stb-def) ;; flds
        nil nil nil nil nil nil
        0)))

(defmacro defcoerce (stbname &rest args)
  (defcoerce-fn (cons stbname args)))



#|

;; Testing: Here I define a stobj with two fields, and see how the theorems
;; work ouy.

ACL2 !>(defcoerce stb1
         (fld1 :type (array (signed-byte 31) (60))
               :initially 0
               :resizable t)
         (fld2 :type t))



ACL2 Warning [Guards] in TOP-LEVEL:  Guard-checking will be inhibited
on recursive calls of the executable counterpart (i.e., in the ACL2
logic) of GET-TYPE-OF.  To check guards on all recursive calls:
  (set-guard-checking :all)
To leave behavior unchanged except for inhibiting this message:
  (set-guard-checking :nowarn)


To verify that the 40 encapsulated events correctly extend the current
theory we will evaluate them.  The theory thus constructed is only
ephemeral.

Encapsulated Events:


ACL2 !>>(SET-IGNORE-OK T)
T


ACL2 !>>(SET-IRRELEVANT-FORMALS-OK T)
T

< ACL2 Output Deleted >

End of Encapsulated Events.

Having verified that the encapsulated events validate the signatures
of the ENCAPSULATE event, we discard the ephemeral theory and extend
the original theory as directed by the signatures and the non-LOCAL
events.

We export COPY-TO-STB1, COPY-FROM-STB1, STB1P-LOGIC, COPY-TO-STB1-FLD1,
COPY-TO-STB1-FLD1-AUX, STB1-FLD1P-LOGIC, COPY-FROM-STB1-FLD1, COPY-
FROM-STB1-FLD1-AUX, UPDATE-FLD2, FLD2, UPDATE-FLD1I, FLD1I, RESIZE-
FLD1, FLD1-LENGTH, CREATE-STB1, STB1P, FLD2P and FLD1P.


Summary
Form:  ( ENCAPSULATE NIL (SET-IGNORE-OK T) ...)
Rules: NIL
Warnings:  Non-rec
Time:  1.31 seconds (prove: 0.65, print: 0.23, other: 0.43)
 T


ACL2 !>(defcoerce stb2 (fld3 :type (array integer (60)) :initially 0) (fld4 :type integer :initially 6))

ACL2 Warning [Guards] in TOP-LEVEL:  Guard-checking will be inhibited
on recursive calls of the executable counterpart (i.e., in the ACL2
logic) of GET-TYPE-OF.  To check guards on all recursive calls:
  (set-guard-checking :all)
To leave behavior unchanged except for inhibiting this message:
  (set-guard-checking :nowarn)


To verify that the 40 encapsulated events correctly extend the current
theory we will evaluate them.  The theory thus constructed is only
ephemeral.

Encapsulated Events:


ACL2 !>>(SET-IGNORE-OK T)
T


ACL2 !>>(SET-IRRELEVANT-FORMALS-OK T)
T

 < ACL2 Output Deleted >

End of Encapsulated Events.

Having verified that the encapsulated events validate the signatures
of the ENCAPSULATE event, we discard the ephemeral theory and extend
the original theory as directed by the signatures and the non-LOCAL
events.

We export COPY-TO-STB2, COPY-FROM-STB2, STB2P-LOGIC, COPY-TO-STB2-FLD3,
COPY-TO-STB2-FLD3-AUX, STB2-FLD3P-LOGIC, COPY-FROM-STB2-FLD3, COPY-
FROM-STB2-FLD3-AUX, UPDATE-FLD4, FLD4, UPDATE-FLD3I, FLD3I, RESIZE-
FLD3, FLD3-LENGTH, CREATE-STB2, STB2P, FLD4P and FLD3P.


Summary
Form:  ( ENCAPSULATE NIL (SET-IGNORE-OK T) ...)
Rules: NIL
Warnings:  Non-rec
Time:  1.23 seconds (prove: 0.64, print: 0.07, other: 0.52)
 T
ACL2 !>


|#
