; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; load-stobj.lisp -- automation for loading lists into STOBJ arrays.
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/lists/list-fix" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
;;(local (include-book "unicode/take" :dir :system))
;;(local (include-book "unicode/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "tools/do-not" :dir :system))
(local (do-not generalize fertilize))


; The macro DEF-LOAD-STOBJ-ARRAY, which is introduced in this book, lets you
; quickly define an easy-to-work-with function for loading lists of data into a
; resizable stobj array.  For instance, if you have a stobj like:
;
;  (defstobj mystobj$
;    ...
;    (myarr :type (array (...) (10))
;           :initially nil
;           :resizable t))
;    ...)
;
; Then this macro can give you a function whose logical definition is:
;
;    (load-myarr list mystobj$)
;      =
;    (update-nth *myarri* (list-fix list) mystobj$)
;
; And whose executable definition loads up mystobj$ up with the elements of the
; list in the obvious way.
;
; See load-stobj-tests.lisp for examples of using the macro.
;
; BOZO the interface is very clunky.  It could probably be made much nicer if
; someone goes to the work of figuring out how to look up information about
; stobjs from the world.  I don't want to spend the time to do that, so you
; just have to provide the name of the field, its index, etc.


(defun-nx nth-nx (n x)
  (declare (xargs :guard t))
  (ec-call (nth n x)))

(defun-nx update-nth-nx (n val x)
  (declare (xargs :guard t))
  (ec-call (update-nth n val x)))



;; BOZO library theorems that probably belong somewhere else

(local (defthm equal-of-cons-rewrite
         (equal (equal (cons a b) x)
                (and (consp x)
                     (equal (car x) a)
                     (equal (cdr x) b)))))

;; (local (defthm cdr-of-nthcdr
;;          (equal (cdr (nthcdr n x))
;;                 (nthcdr (+ 1 (nfix n)) x))))

;; (local (defthm cdr-of-xfirstn
;;          (equal (cdr (xfirstn a x))
;;                 (xfirstn (- a 1) (cdr x)))
;;          :hints(("Goal" :in-theory (enable xfirstn)))))

(local (in-theory (enable cdr-over-nthcdr
                          take-is-xfirstn)))

(local (defthm xfirstn-of-nthcdr
         (implies (and (posp a)
                       (posp n))
                  (equal (xfirstn a (nthcdr n x))
                         (cons (nth n x) (xfirstn (- a 1) (nthcdr (+ n 1) x)))))
         :hints(("Goal" :expand ((xfirstn a (nthcdr n x)))))))

(local (defthm xfirstn-when-zp
         (implies (zp n)
                  (equal (xfirstn n x)
                         nil))
         :hints(("Goal" :in-theory (enable xfirstn)))))

(local (defthm nth-of-xfirstn
         (equal (nth a (xfirstn b x))
                (if (< (nfix a) (nfix b))
                    (nth a x)
                  nil))
         :hints(("Goal" :in-theory (enable xfirstn)))))

;; part of std/lists now
;; (local (defthm nth-of-list-fix
;;          (equal (nth n (list-fix a))
;;                 (nth n a))
;;          :hints(("Goal" :in-theory (enable nth list-fix)))))



(defund load-stobj-array (n a b)

; This function emulates loading data into a STOBJ array.  N is the current
; index, A is the data to load, and B is the "array."  We copy elements from A
; into B, essentially doing:
;
;    B[n]   := A[0]
;    B[n+1] := A[1]
;    ...
;
; Until we run out of elements in A.

  (if (atom a)
      (list-fix b)
    (load-stobj-array (+ 1 (nfix n))
                      (cdr a)
                      (update-nth (nfix n) (car a) b))))

(local (in-theory (enable load-stobj-array)))

(local (defthm true-listp-of-load-stobj-array
         (true-listp (load-stobj-array n a b))
         :rule-classes :type-prescription))

(local (defthm len-of-load-stobj-array
         (equal (len (load-stobj-array n a b))
                (max (len b)
                     (if (consp a)
                         (+ (nfix n) (len a))
                       0)))
         :hints(("Goal" :induct (load-stobj-array n a b)))))

(local (defthm nth-of-load-stobj-array-smaller
         (implies (< (nfix i) (nfix n))
                  (equal (nth i (load-stobj-array n a b))
                         (nth i b)))
         :hints(("Goal" :induct (load-stobj-array n a b)))))

(local
 (encapsulate
   ()
   (local (defthmd l0
            (implies (natp n)
                     (equal (xfirstn (len a)
                                          (nthcdr n (load-stobj-array n a b)))
                            (list-fix a)))))

   (local (defthmd l1
            (equal (xfirstn (len a) (load-stobj-array 0 a b))
                   (list-fix a))
            :hints(("Goal" :use ((:instance l0 (n 0)))))))

   (defthm nth-of-load-stobj-array
     (implies (< (nfix n) (len a))
              (equal (nth n (load-stobj-array 0 a b))
                     (nth n a)))
     :hints(("goal"
             :do-not-induct t
             :in-theory (disable nth-of-xfirstn)
             :use ((:instance l1)
                   (:instance nth-of-xfirstn
                              (a n)
                              (b (len a))
                              (x (load-stobj-array 0 a b)))))))))

(defthm load-stobj-array-correct
  (implies (equal (len a) (len b))
           (equal (load-stobj-array 0 a b)
                  (list-fix a)))
  :hints(("Goal"
          :do-not-induct t
          :in-theory (disable load-stobj-array)
          :use ((:functional-instance
                 acl2::equal-by-nths
                 (acl2::equal-by-nths-hyp (lambda () (equal (len a) (len b))))
                 (acl2::equal-by-nths-lhs (lambda () (load-stobj-array 0 a b)))
                 (acl2::equal-by-nths-rhs (lambda () (list-fix a))))))))





; Now we make the macro.

(defthmd load-stobj-array-lemma-0
  (equal (update-nth j b (update-nth i a l))
         (if (equal (nfix i) (nfix j))
             (update-nth j b l)
           (update-nth i a (update-nth j b l))))
  :rule-classes
  ((:rewrite :corollary
    (implies (equal (nfix i) (nfix j))
             (equal (update-nth j b (update-nth i a l))
                    (update-nth j b l))))
   (:rewrite :corollary
    (implies (not (equal (nfix i) (nfix j)))
             (equal (update-nth j b (update-nth i a l))
                    (update-nth i a (update-nth j b l))))))
  :hints(("Goal" :use ((:instance update-nth-update-nth)))))

(defthmd load-stobj-array-lemma-1
  (equal (len (resize-list lst m default))
         (nfix m)))

(defthmd load-stobj-array-lemma-2
  (implies (< (nfix n) (len l))
           (equal (update-nth n (nth n l) l)
                  l)))


(deftheory load-stobj-array-rules
  '(load-stobj-array-lemma-0
    load-stobj-array-lemma-1
    load-stobj-array-lemma-2
    booleanp-compound-recognizer
    booleanp
    nfix
    natp
    max
    nth-nx
    nth-update-nth
    update-nth-nx
    update-nth-array
    len-update-nth
    load-stobj-array
    len
    length
    len-of-list-fix
    llist-fix
    (:t list-fix)
    (:type-prescription len)
    list-fix-when-true-listp))


(defmacro def-load-stobj-array (name &key

; Easy fields:
                                     stobj        ; stobj's name
                                     stobjp       ; stobj's recognizer
                                     index        ; array's stobj index, e.g., *arri*
                                     arrp         ; array's recognizer
                                     update-arri  ; array's updater
                                     resize-arr   ; array's resizer
                                     arr-length   ; array's length function
                                     default      ; array's default value (:initially)

; ELEMP is a recognizer for proper array elements.  If your array field is
; something like (array t (0)), then you can just leave ELEMP as NIL.  But if
; you have an array with a restricted type, you have to provide a term about
; the variable ACL2::X that recognizes an element.  For instance,
;
;     Declaration                          What ELEM should be:
;     (array t (0))                        nil
;     (array integer (0))                  (integerp x)
;     (array (unsigned-byte 32) (0))       (unsigned-byte-p 32 x)
;     (array symbol (0))                   (symbolp x)

                                     elemp)

  (let* ((booleanp-of-arrp
          (intern-in-package-of-symbol
           (concatenate 'string "LSA-BOOLEANP-OF-" (symbol-name arrp))
           name))

         (true-listp-when-arrp
          (intern-in-package-of-symbol
           (concatenate 'string "LSA-TRUE-LISTP-WHEN-" (symbol-name arrp))
           name))

         (arrp-of-cdr
          (intern-in-package-of-symbol
           (concatenate 'string "LSA-" (symbol-name arrp) "-OF-CDR")
           name))

         (elemp-of-car
          (intern-in-package-of-symbol
           (concatenate 'string "LSA-ELEMP-OF-CAR-WHEN-" (symbol-name arrp))
           name))

         (load-base
          (intern-in-package-of-symbol
           (concatenate 'string (symbol-name name) "-BASE-CASE")
           name))

         (load-main
          (intern-in-package-of-symbol
           (concatenate 'string (symbol-name name) "-MAIN-LOOP")
           name))

         (load-main-correct
          (intern-in-package-of-symbol
           (concatenate 'string (symbol-name load-main) "-CORRECT")
           name)))

    `(encapsulate
       ()
       (local (set-default-hints nil))
       (local (in-theory (theory 'minimal-theory)))
       (local (in-theory (enable load-stobj-array-rules
                                 ,stobjp
                                 ,update-arri
                                 ,resize-arr
                                 ,arr-length)))

       (local (defthm ,booleanp-of-arrp
                (booleanp (,arrp x))
                :rule-classes :type-prescription
                :hints(("Goal" :in-theory (enable ,arrp)))))

       (local (defthm ,true-listp-when-arrp
                (implies (,arrp x)
                         (true-listp x))
                :rule-classes :compound-recognizer
                :hints(("Goal" :in-theory (enable ,arrp)))))

       (local (defthm ,arrp-of-cdr
                (implies (,arrp x)
                         (,arrp (cdr x)))
                :hints(("Goal" :in-theory (enable ,arrp)))))

       ,@(and elemp
              `((local (defthm ,elemp-of-car
                         (implies (and (,arrp x)
                                       (consp x))
                                  ,(subst '(car x) 'x elemp))
                         :hints(("Goal" :in-theory (enable ,arrp)))))))

       (defund ,load-base (,stobj)
         (declare (xargs :stobjs ,stobj))
         (mbe :logic (let* ((old-arr (nth-nx ,index ,stobj))
                            (new-arr (list-fix old-arr)))
                       (update-nth-nx ,index new-arr ,stobj))
              :exec ,stobj))

       (defund ,load-main (n a ,stobj)
         (declare (xargs :guard (and (natp n)
                                     (,arrp a)
                                     (<= (+ n (len a)) (,arr-length ,stobj)))
                         :stobjs ,stobj))
         (if (atom a)
             (,load-base ,stobj)
           (let ((,stobj (,update-arri (mbe :logic (nfix n) :exec n) (car a) ,stobj)))
             (,load-main (+ 1 (mbe :logic (nfix n) :exec n)) (cdr a) ,stobj))))

       (local (defthm ,load-main-correct
         (equal (,load-main n a ,stobj)
                (update-nth ,index
                            (load-stobj-array n a (nth ,index ,stobj))
                            ,stobj))
         :hints(("goal"
                 :in-theory (enable ,load-main ,load-base)
                 :induct (,load-main  n a ,stobj)))))

       (defun ,name (a ,stobj)
         ;: We leave this enabled because its logical definition is good.
         (declare (xargs :guard (,arrp a)
                         :stobjs ,stobj
                         :verify-guards nil))
         (mbe :logic
              (update-nth-nx ,index (list-fix a) ,stobj)
              :exec
              (b* ((a (llist-fix a))
                   (,stobj (,resize-arr (length a) ,stobj)))
                (,load-main 0 a ,stobj))))

       (verify-guards ,name
         :guard-debug t
         :hints(("Goal"
                 :in-theory (e/d (,name)
                                 ,(if elemp
                                      `(,elemp-of-car)
                                    nil))
                 :use ((:instance load-stobj-array-correct
                                  (a (list-fix a))
                                  (b (resize-list (nth ,index ,stobj)
                                                  (len a) ,default)))))))
       )))

