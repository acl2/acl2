;;
;; Copyright (C) 2020, David Greve
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
;;
(in-package "PIGEONHOLE")
(include-book "xdoc/top" :dir :system)

(encapsulate
    (
     ((fn *) => *)
     ((n)    => *)
     )

  (local
   (defun fn (x) (declare (ignore x)) 0))

  (local
   (defun n () 10))

  (defthm n-type
    (posp (n))
    :rule-classes (:type-prescription :rewrite))

  (defthm fn-type
    (integerp (fn x))
    :rule-classes (:type-prescription :rewrite))

  (defthm fn-bound
    (and (<= 0 (fn x))
         (< (fn x) (n)))
    :rule-classes (:linear
                   (:forward-chaining :trigger-terms ((fn x)))))

  )

(local
 (encapsulate
     ()

(defun duplicate-values (args available used)
  (if (not (consp args)) (mv 0 0)
    (let ((value (fn (car args))))
      (if (assoc value used) (mv (car args) (cdr (assoc value used)))
        (if (member value available) 
            (duplicate-values (cdr args) (remove value available) (acons value (car args) used))
          (mv 0 0))))))

(defun range-invariant (n available used)
  (if (zp n) t
    (let ((n (1- n)))
      (and (iff (assoc n used) (not (member n available)))
           (range-invariant n available used)))))

(defun unique-count (list)
  (if (not (consp list)) 0
    (1+ (unique-count (remove (car list) (cdr list))))))

(encapsulate
 ()

 (local
  (encapsulate
      ()

    (defthm member-remove
      (iff (member-equal x (remove-equal y list))
           (if (equal x y) nil
             (member-equal x list))))
    
    (defthm remove-remove
      (equal (remove-equal x (remove-equal x z))
             (remove-equal x z)))
    
    (defthm remove-commute
      (equal (remove-equal x (remove-equal y z))
             (remove-equal y (remove-equal x z))))
    
    (defthm open-unique-count-remove
      (implies
       (consp available)
       (equal (unique-count (remove-equal v available))
              (if (equal v (car available))
                  (unique-count (remove-equal (car available) (cdr available)))
                (1+ (unique-count (remove-equal v (remove-equal (car available) (cdr available))))))))
      :hints (("Goal" :do-not-induct t
               :expand ((remove-equal v available)
                        (:free (a z) (unique-count (cons a z)))))))
    
    (defthm open-unique-count-member
      (implies
       (member-equal v available)
       (equal (unique-count available)
              (1+ (unique-count (remove-equal v available)))))
      :hints (("Goal" :in-theory (disable remove-equal))))

    ))

 (defthm unique-count-remove
   (implies
    (member-equal v available)
    (equal (unique-count (remove-equal v available))
           (1- (unique-count available))))
   :hints (("Goal" :in-theory (disable remove-equal))))
 
 )

(defun fn-alistp (alist)
  (if (not (consp alist)) t
    (let ((entry (car alist)))
      (and (equal (car entry) (fn (cdr entry)))
           (fn-alistp (cdr alist))))))

(defthm fn-assoc-fn-alistp
  (implies
   (and
    (fn-alistp used)
    (assoc-equal v used))
   (equal (fn (cdr (assoc-equal v used)))
          v)))

(defthm member-remove
  (iff (member-equal x (remove-equal y list))
       (if (equal x y) nil
         (member-equal x list))))

(defthm range-invariant-step
  (implies
   (range-invariant n available used)
   (range-invariant n (remove-equal (fn x) available)
                    (cons (cons (fn x) x) used))))

(defun bound-p (n x)
  (< (nfix x) (nfix n)))

(defun enumerate-n (n)
  (if (zp n) nil
    (let ((n (1- n)))
      (cons n (enumerate-n n)))))

(defthm bound-p-reduction
  (iff (bound-p n x)
       (member (nfix x) (enumerate-n n))))

(defthm remove-enumerate-n
  (implies
   (<= (nfix m) (nfix n))
   (equal (remove-equal n (enumerate-n m))
          (enumerate-n m))))

(defthm unique-count-enumerate-n
  (equal (unique-count (enumerate-n n))
         (nfix n))
  :hints (("Goal" :induct (enumerate-n n)
           :do-not-induct t
           :expand (:free (a x) (unique-count (cons a x))))))

(defun range-invariant-1 (n available)
  (if (zp n) t
    (let ((n (1- n)))
      (and (member n available)
           (range-invariant-1 n available)))))

(defthm range-invariant-reduction
  (iff (range-invariant n available nil)
       (range-invariant-1 n available)))

(defthm range-invariant-cons
  (implies
   (and
    (natp n)
    (natp a)
    (<= n a))
   (equal (range-invariant-1 n (cons a b))
          (range-invariant-1 n b))))

(defthm range-invariant-1-enumerate-n
   (range-invariant-1 n (enumerate-n n)))

(defun alist-values (used)
  (if (not (consp used)) nil
    (let ((entry (car used)))
      (cons (cdr entry)
            (alist-values (cdr used))))))

(defun disjoint-from-domain (args used)
  (if (not (consp args)) t
    (and (not (member (car args) (alist-values used)))
         (disjoint-from-domain (cdr args) used))))

(defun no-duplicates (args)
  (if (not (consp args)) t
    (and (not (member (car args) (cdr args)))
         (no-duplicates (cdr args)))))

(defthm disjoint-from-domain-invariant
  (implies
   (and
    (disjoint-from-domain args used)
    (not (member arg args)))
   (disjoint-from-domain args (cons (cons val arg) used))))
                                
(defthmd range-invariant-assoc-reduction
  (implies
   (and
    (natp v)
    (RANGE-INVARIANT n AVAILABLE USED)
    (< v (nfix n)))
   (iff (assoc-equal v used)
        (not (member v available)))))

(defthm not-member-values-not-equal-cdr-assoc
  (implies
   (and
    (not (member-equal arg (alist-values used)))
    (assoc-equal z used))
   (not (equal arg (cdr (assoc-equal z used))))))

(defthm member-alist-values
  (implies
   (assoc-equal v used)
   (member-equal (cdr (assoc v used))
                 (alist-values used))))

(in-theory (disable mv-nth))

(defthm general-property
  (implies
   (and 
    (fn-alistp used)
    (range-invariant (n) available used)
    (no-duplicates args)
    (disjoint-from-domain args used)
    (< (unique-count available) (len args)))
   (mv-let (a b) (duplicate-values args available used)
           (and (or (member a args)
                    (member a (alist-values used)))
                (or (member b args)
                    (member b (alist-values used)))
                (not (equal a b))
                (equal (fn a) (fn b)))))
  :rule-classes nil
  :hints (("Goal" 
           :do-not-induct t
           :induct (duplicate-values args available used)
           :expand (disjoint-from-domain args used))
          (and stable-under-simplificationp
               '(:in-theory (enable range-invariant-assoc-reduction)))))

(defthm disjoint-from-domain-nil
  (disjoint-from-domain args nil))

(defthmd property-instance
  (implies
   (and
    (no-duplicates args)
    ;; (0 1 2 3) < 4
    ;; (0 1 2 3 4) 5
    (< (n) (len args)))
   (mv-let (a b) (duplicate-values args (enumerate-n (n)) nil)
           (and (member a args)
                (member b args)
                (not (equal a b))
                (equal (fn a) (fn b)))))
  :hints (("Goal" :do-not-induct t
           :use (:instance general-property
                           (used nil)
                           (available (enumerate-n (n)))
                           ))))

(defthm not-member-enumerate-n
  (implies
   (and
    (natp m)
    (natp n)
    (<= n m))
   (not (member-equal m (enumerate-n n)))))

(defthm no-duplicates-enumerate-n
  (no-duplicates (enumerate-n m)))

(defthm len-enumerate-n
  (equal (len (enumerate-n m))
         (nfix m)))

(defthm nat-listp-enumerate-n
  (nat-listp (enumerate-n n))
  :rule-classes ((:forward-chaining :trigger-terms ((enumerate-n n)))))

(defthm natp-member-nat-listp
  (implies
   (and
    (member-equal x list)
    (nat-listp list))
   (natp x))
  :rule-classes :forward-chaining)

(defthm natp-implies
  (implies
   (natp x)
   (and (integerp x)
        (<= 0 x)))
  :rule-classes :forward-chaining)

(defthmd numeric-property-instance
  (implies
   (and
    (natp m)
    (< (n) m))
   (mv-let (a b) (duplicate-values (enumerate-n (1+ m)) (enumerate-n (n)) nil)
           (and (natp a)
                (natp b)
                (bound-p (1+ m) a)
                (bound-p (1+ m) b)
                (not (equal a b))
                (equal (fn a) (fn b)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable enumerate-n duplicate-values)
           :use (:instance property-instance
                           (args (enumerate-n (1+ m)))))))

))

(defun-sk exists-duplicates (m)
  (exists (a b) (and (natp a)
                     (natp b)
                     (<= a m)
                     (<= b m)
                     (not (equal a b))
                     (equal (fn a) (fn b)))))

(defthmd numeric-pigeonhole-property
  (implies
   (and
    (natp m)
    (< (n) m))
   (exists-duplicates m))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (bound-p) (bound-p-reduction exists-duplicates))
           :use (numeric-property-instance))))

(defmacro proof (fn n &key (function 'nil))
  (let ((pkg (or function (if (symbolp fn) fn 'hole-proof)))
        (function (or function fn)))
    (let ((exists-fn-duplicates         (acl2::packn-pos (list 'exists- function '-duplicates) pkg))
          (exists-fn-duplicates-witness (acl2::packn-pos (list 'exists- function '-duplicates-witness) pkg))
          (fn-pigeonhole-property      (acl2::packn-pos (list function '-pigeonhole-property) pkg)))
      `(encapsulate
           ()
         
         (defun-sk ,exists-fn-duplicates (m)
           (exists (a b) (and (natp a)
                              (natp b)
                              (<= a m)
                              (<= b m)
                              (not (equal a b))
                              (equal (,fn a) (,fn b)))))
         
         (defthm ,fn-pigeonhole-property
           (implies
            (and
             (natp m)
             (< ,n m))
            (,exists-fn-duplicates m))
           :hints (("Goal" :do-not-induct t
                    :use (:functional-instance numeric-pigeonhole-property
                                               (fn ,fn)
                                               (n  (lambda () ,n))
                                               (exists-duplicates ,exists-fn-duplicates)
                                               (exists-duplicates-witness ,exists-fn-duplicates-witness)))
                   ))
         
         ))))

(local
 (encapsulate
     ()

   (encapsulate
       (
        ((zed *) => *)
        )

     (local (defun zed (x) (declare (ignore x)) 10))

     (defthm integerp-zed
       (integerp (zed x)))

     (defthm zed-bound
       (and (<= 0 (zed x))
            (< (zed x) 100)))
     
     )
        
   (pigeonhole::proof zed 100)
   
   ;; This macro admits the form:
   ;;
   ;; (defun-sk exists-zed-duplicates (m)
   ;;   (exists (a b) (and (natp a)
   ;;                      (natp b)
   ;;                      (<= a m)
   ;;                      (<= b m)
   ;;                      (not (equal a b))
   ;;                      (equal (zed a) (zed b)))))
   ;;
   ;; And allows us to prove ..
   (defthm zed-pigeonhole-property-lemma
     (implies
      (and
       (natp m)
       (< 100 m))
      (exists-zed-duplicates m)))
           
   ))

(acl2::defxdoc pigeonhole::proof
  :short "A macro that proves the pigeonhole principle for functions with finite ranges"
  :parents (acl2::proof-automation)
  :long "
<p>
The pigeonhole book defines a simple macro @('pigeonhole::proof') that can
be used to prove the pigeonhole principle for functions with finite ranges.
The pigeonhole principle says that, given a function with k elements in
its range, among k+1 or more invocations of that function at least two will
generate identical outputs.
</p>
<p>Usage:</p>
@({
   (include-book \"misc/pigeonhole\" :dir :system)

   (encapsulate
       (
        ((zed *) => *)
        )

     (local (defun zed (x) (declare (ignore x)) 10))

     (defthm integerp-zed
       (integerp (zed x)))

     (defthm zed-bound
       (and (<= 0 (zed x))
            (< (zed x) 100)))
     
     )

   ;;        
   ;; This macro invocation:
   ;;
   (pigeonhole::proof zed 100)
   ;;
   ;; admits the form:
   ;;
   ;; (defun-sk exists-zed-duplicates (m)
   ;;   (exists (a b) (and (natp a)
   ;;                      (natp b)
   ;;                      (<= a m)
   ;;                      (<= b m)
   ;;                      (not (equal a b))
   ;;                      (equal (zed a) (zed b)))))
   ;;
   ;; And proves ..
   ;;
   (defthm zed-pigeonhole-property-lemma
     (implies
      (and
       (natp m)
       (< 100 m))
      (exists-zed-duplicates m)))

 })
")
