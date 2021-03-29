; A library for reasoning about ACL2 arrays (aref1, aset1, etc.)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/reverse-list" :dir :system) ;make local?
(include-book "bounded-nat-alists")
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; We disable functions about arrays, because this book introduces rules about
;; them:
(in-theory (disable dimensions
                    header
                    default
                    maximum-length
                    array1p
                    aset1
                    aref1
                    compress1
                    compress11
                    bounded-integer-alistp))

(in-theory (disable array1p-linear)) ; does not reflect our normal form

(local (in-theory (disable true-listp
                           assoc-keyword)))

;;;
;;; Normalize names (most of these functions ignore the name param)
;;;

(defthmd normalize-header-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (header name l)
                  (header :fake-name l)))
  :hints (("Goal" :in-theory (enable header))))

(local (in-theory (enable normalize-header-name)))

(defthmd normalize-default-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (default name l)
                  (default :fake-name l)))
  :hints (("Goal" :in-theory (enable default))))

(local (in-theory (enable normalize-default-name)))

(defthmd normalize-maximum-length-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (maximum-length name l)
                  (maximum-length :fake-name l)))
  :hints (("Goal" :in-theory (enable maximum-length))))

(local (in-theory (enable normalize-maximum-length-name)))

(defthmd normalize-dimensions-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (dimensions name l)
                  (dimensions :fake-name l)))
  :hints (("Goal" :in-theory (enable dimensions))))

(local (in-theory (enable normalize-dimensions-name)))

(defthmd normalize-compress11-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress11 name l i n default)
                  (compress11 :fake-name l i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

(local (in-theory (enable normalize-compress11-name)))

(defthmd normalize-compress1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress1 name l)
                  (compress1 :fake-name l)))
  :hints (("Goal" :in-theory (enable compress1))))

(local (in-theory (enable normalize-compress1-name)))

(defthmd normalize-compress211-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress211 name l i x j default)
                  (compress211 :fake-name l i x j default)))
  :hints (("Goal" :in-theory (enable compress211))))

(local (in-theory (enable normalize-compress211-name)))

(defthmd normalize-compress21-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress21 name l n i j default)
                  (compress21 :fake-name l n i j default)))
  :hints (("Goal" :in-theory (enable compress21))))

(local (in-theory (enable normalize-compress21-name)))

(defthmd normalize-compress2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress2 name l)
                  (compress2 :fake-name l)))
  :hints (("Goal" :in-theory (enable compress2))))

(local (in-theory (enable normalize-compress2-name)))

(defthmd normalize-aref1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref1 name l n)
                  (aref1 :fake-name l n)))
  :hints (("Goal" :in-theory (enable aref1))))

;; (local (in-theory (enable normalize-aref1-name)))

(defthmd normalize-aset1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aset1 name l n val)
                  (aset1 :fake-name l n val)))
  :hints (("Goal" :in-theory (enable aset1))))

;; (local (in-theory (enable normalize-aset1-name)))

(defthmd normalize-aset2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aset2 name l i j val)
                  (aset2 :fake-name l i j val)))
  :hints (("Goal" :in-theory (enable aset2))))

;; (local (in-theory (enable normalize-aset2-name)))

(defthmd normalize-aref2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref2 name l i j)
                  (aref2 :fake-name l i j)))
  :hints (("Goal" :in-theory (enable aref2))))

;; (local (in-theory (enable normalize-aref2-name)))

(defthmd normalize-array1p-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (array1p name l)
                  (and (symbolp name)
                       (array1p :fake-name l))))
  :hints (("Goal" :in-theory (enable array1p))))

;; (local (in-theory (enable normalize-array1p-name)))

(defthmd normalize-array2p-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (array2p name l)
                  (and (symbolp name)
                       (array2p :fake-name l))))
  :hints (("Goal" :in-theory (enable array2p))))

;; (local (in-theory (enable normalize-array2p-name)))

;; The -1 is here because array1p requries the length to be strictly less than
;; the :MAXIMUM-LENGTH (why?), and the :MAXIMUM-LENGTH is at most
;; *maximum-positive-32-bit-integer* .
(defconst *maximum-1-d-array-length* (+ -1 *maximum-positive-32-bit-integer*))

;; This is perhaps how array1p should be defined (but see the comment about
;; array1p in the ACL2 sources).
(defthmd array1p-rewrite
  (equal (array1p name l)
         (and
          (symbolp name)
          (alistp l)
          (let
              ((header-keyword-list (cdr (header name l))))
            (and
             (keyword-value-listp header-keyword-list)
             (let* ((dimensions (dimensions name l))
                    (len (car dimensions))
                    (maximum-length (maximum-length name l)))
               (and (true-listp dimensions)
                    (equal (len dimensions) 1)
                    (integerp len)
                    (integerp maximum-length)
                    (< 0 len)
                    (< len maximum-length)
                    (<= maximum-length *maximum-positive-32-bit-integer*)
                    (bounded-integer-alistp l len)))))))
  :hints (("Goal" :in-theory (e/d (array1p header dimensions maximum-length)
                                  ()))))


;; ;;;
;; ;;; header-intro
;; ;;;

;; Unfortunately, this has a free variable in the RHS.
(defthmd header-intro
  (equal (assoc-equal :header l)
         (header name l))
  :hints (("Goal" :in-theory (enable header))))

(theory-invariant (incompatible (:rewrite header-intro) (:definition header)))

;;;
;;; default-intro
;;;

;; We prefer a call to the function DEFAULT instead of its expanded form,
;; but some functions use the expanded form directly, so we use this rule to
;; convert things into our normal form.
(defthm default-intro
  (equal (cadr (assoc-keyword :default (cdr (header name l))))
         (default name l))
  :hints (("Goal" :in-theory (enable default))))

(theory-invariant (incompatible (:rewrite default-intro) (:definition default)))

;;;
;;; default-intro2
;;;

;; This one also collapses the call to header
;; Unfortunately, this has a free variable in the RHS.
(defthmd default-intro2
  (equal (cadr (assoc-keyword :default (cdr (ASSOC-EQUAL :HEADER L))))
         (default name l))
  :hints (("Goal" :in-theory (e/d (default header) (default-intro)))))

(theory-invariant (incompatible (:rewrite default-intro2) (:definition default)))


;;;
;;; dimensions-intro
;;;

;; We prefer a call to the function DIMENSIONS instead of its expanded form,
;; but some functions use the expanded form directly, so we use this rule to
;; convert things into our normal form.
(defthm dimensions-intro
  (equal (cadr (assoc-keyword :dimensions (cdr (header name l))))
         (dimensions name l))
  :hints (("Goal" :in-theory (enable dimensions))))

(theory-invariant (incompatible (:rewrite dimensions-intro) (:definition dimensions)))

;;;
;;; dimensions-intro2
;;;

;; This one also collapses the call to header
;; Unfortunately, this has a free variable in the RHS.
(defthmd dimensions-intro2
  (equal (cadr (assoc-keyword :dimensions (cdr (assoc-equal :header l))))
         (dimensions name l))
  :hints (("Goal" :in-theory (e/d (dimensions header) (dimensions-intro)))))

(theory-invariant (incompatible (:rewrite dimensions-intro2) (:definition dimensions)))

(defthm true-listp-of-dimensions
  (implies (array1p array-name array)
           (true-listp (dimensions array-name array)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (array1p-rewrite)
                                  ()))))


;;;
;;; alen1
;;;

;; Get the length of a 1-d array.  We prefer this to (car (dimensions ...))
;; because car in many cases get rewritten to a call of nth.
;todo: consider not even passing in name here
(defund alen1 (name l)
  (declare (xargs :guard (array1p name l)))
  (car (dimensions name l)))

(defthmd normalize-alen1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (alen1 name l)
                  (alen1 :fake-name l)))
  :hints (("Goal" :in-theory (e/d (alen1) ()))))

(local (in-theory (enable normalize-alen1-name)))

;todo: enable, but that changes the normal form
(defthm alen1-intro
  (equal (car (dimensions array-name array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (enable alen1))))

(theory-invariant (incompatible (:rewrite alen1-intro) (:definition alen1)))

;; (car (dimensions ..)) can arise from the guard of aref1 and can then be turned into (nth 0 (dimensions ...))
(defthm alen1-intro2
  (equal (nth 0 (dimensions array-name array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (e/d (alen1) (alen1-intro)))))

(theory-invariant (incompatible (:rewrite alen1-intro2) (:definition alen1)))

;; Here we also introduce alen1
(defthmd array1p-rewrite2
  (equal (array1p name l)
         (and
          (symbolp name)
          (alistp l)
          (let
              ((header-keyword-list (cdr (header name l))))
            (and
             (keyword-value-listp header-keyword-list)
             (let* ((dimensions (dimensions name l))
                    (len (alen1 name l))
                    (maximum-length (maximum-length name l)))
               (and (true-listp dimensions)
                    (equal (len dimensions) 1)
                    (integerp len)
                    (integerp maximum-length)
                    (< 0 len)
                    (< len maximum-length)
                    (<= maximum-length *maximum-positive-32-bit-integer*)
                    (bounded-integer-alistp l len)))))))
  :hints (("Goal" :in-theory (e/d (array1p-rewrite)
                                  ()))))


(defthm header-when-array1p
  (implies (array1p name2 l)
           (header name l))
  :hints (("Goal" :in-theory (e/d (array1p-rewrite dimensions) (dimensions-intro)))))

(defthm consp-of-header-when-array1p
  (implies (array1p name2 l)
           (consp (header name l)))
  :hints (("Goal" :in-theory (e/d (array1p-rewrite dimensions) (dimensions-intro)))))

(defthmd keyword-value-listp-of-cdr-of-header-when-array1p
  (implies (array1p array-name array)
           (keyword-value-listp (cdr (header array-name array))))
  :hints (("Goal" :in-theory (enable array1p header))))

(defthm integerp-of-alen1-gen
  (implies (array1p array-name2 array) ;array-name2 is a free var
           (integerp (alen1 array-name array)))
  :hints (("Goal" :in-theory (e/d (alen1 posp array1p-rewrite) (alen1-intro alen1-intro2)))))

;; no free vars
(defthm integerp-of-alen1
  (implies (array1p array-name array)
           (integerp (alen1 array-name array))))

(defthm posp-of-alen1
  (implies (array1p array-name2 array)
           (posp (alen1 array-name array)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable posp array1p-rewrite2))))

;; Note that bounded-integer-alistp is a bad name, because it allows a key of :header.

(defthm car-of-assoc-equal-cheap
  (implies (assoc-equal x alist)
           (equal (car (assoc-equal x alist))
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm car-of-assoc-equal-strong
  (equal (car (assoc-equal x alist))
         (if (assoc-equal x alist)
             x
           nil))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm assoc-equal-of-compress11-when-too-small
  (implies (< index i)
           (equal (assoc-equal index (compress11 name l i n default))
                  nil))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm alistp-of-reverse-list
  (equal (alistp (reverse-list x))
         (alistp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable alistp reverse-list))))

;; (defthm alistp-of-reverse-list
;;   (implies (alistp x)
;;            (alistp (reverse-list x)))
;;   :hints (("Goal" :in-theory (enable reverse-list))))

(defthm default-of-cons
  (equal (default name (cons a x))
         (if (equal :header (car a))
             (cadr (assoc-keyword :default (cdr a)))
           (default name x)))
  :hints (("Goal" :in-theory (e/d (default header) (default-intro)))))

(defthm maximum-length-of-cons
  (equal (maximum-length name (cons a x))
         (if (equal :header (car a))
             (cadr (assoc-keyword :maximum-length (cdr a)))
           (maximum-length name x)))
  :hints (("Goal" :in-theory (enable maximum-length header))))

(defthm equal-of-header-and-car-of-header
  (iff (equal :header (car (header array-name array)))
       (header array-name array))
  :hints (("Goal" :in-theory (enable header))))

(defthm assoc-equal-of-reverse-list-iff
  (implies (or (alistp x)
               key)
           (iff (assoc-equal key (reverse-list x))
                (assoc-equal key x)))
  :hints (("Goal" :in-theory (enable reverse-list))))


(local (in-theory (enable revappend-lemma)))

(defthm bounded-integer-alistp-of-append
  (implies (true-listp x)
           (equal (bounded-integer-alistp (append x y) n)
                  (and (bounded-integer-alistp x n)
                       (bounded-integer-alistp y n))))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp reverse-list))))

;use list fix in concl?
(defthm bounded-integer-alistp-of-reverse-list
  (implies (true-listp x)
           (equal (bounded-integer-alistp (reverse-list x) n)
                  (bounded-integer-alistp x n)))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp reverse-list))))

;; ;drop?
;; (defthm bounded-integer-alistp-of-revappend
;;   (implies (and (bounded-integer-alistp x n)
;;                 (bounded-integer-alistp y n))
;;            (bounded-integer-alistp (revappend x y) n))
;;   :hints (("Goal" :in-theory (enable bounded-integer-alistp revappend))))

(defthmd assoc-equal-when-assoc-equal-of-reverse-list
  (implies (and (assoc-equal key (reverse-list alist))
                (alistp alist))
           (assoc-equal key alist))
  :hints (("Goal" :in-theory (enable assoc-equal reverse-list))))

;might be better to strip the keys and call NO-DUPLICATESP?
(defun myduplicate-keysp (alist)
  (cond ((endp alist) nil)
        ((assoc-equal (caar alist) (cdr alist))
         t)
        (t (myduplicate-keysp (cdr alist)))))

(defthm assoc-equal-of-reverse-list
  (implies (and (not (myduplicate-keysp alist))
                (alistp alist))
           (equal (assoc-equal key (reverse-list alist))
                  (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable assoc-equal reverse-list
                                     assoc-equal-when-assoc-equal-of-reverse-list))))


(defthm header-of-cons
  (equal (header array-name (cons entry alist))
         (if (eq :header (car entry))
             entry
           (header array-name alist)))
  :hints (("Goal" :in-theory (enable header))))

(defthm dimensions-of-cons
  (equal (dimensions array-name (cons entry alist))
         (if (eq :header (car entry))
             (cadr (assoc-keyword :dimensions (cdr entry)))
           (dimensions array-name alist)))
  :hints (("Goal" :in-theory (e/d (dimensions)
                                  (dimensions-intro)))))

(defthm alen1-of-cons
  (equal (alen1 array-name (cons entry alist))
         (if (eq :header (car entry))
             (car (cadr (assoc-keyword :dimensions (cdr entry))))
           (alen1 array-name alist)))
  :hints (("Goal" :in-theory (e/d (alen1)
                                  (alen1-intro alen1-intro2)))))

;has more stuff wrapped up...




;can be expensive?
(defthmd consp-when-true-listp-and-non-nil
  (implies (and x ;limit?
                (true-listp x))
           (consp x)))

(defthm equal-of-assoc-equal-same
  (implies key
           (iff (equal key (car (assoc-equal key array)))
                (assoc-equal key array)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm header-of-compress1
  (equal (header array-name (compress1 array-name array))
         (header array-name array))
  :hints (("Goal" :in-theory (e/d (compress1 compress11 dimensions header)
                                  (dimensions-intro)))))

(defthm maximum-length-of-compress1
  (equal (maximum-length array-name (compress1 array-name array))
         (maximum-length array-name array))
  :hints (("Goal" :in-theory (e/d (compress1 compress11 maximum-length header)
                                  ()))))

(defthm dimensions-of-compress1
  (equal (dimensions array-name (compress1 array-name array))
         (dimensions array-name array))
  :hints (("Goal" :in-theory (e/d (dimensions) (dimensions-intro)))))

(defthm alen1-of-compress1
  (equal (alen1 array-name (compress1 array-name array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (e/d (alen1) (alen1-intro alen1-intro2)))))

(defthm dimensions-of-aset1
  (equal (dimensions array-name (aset1 array-name array n val))
         (if (eq :header n)
             (cadr (assoc-keyword :dimensions val))
           (dimensions array-name array)))
  :hints (("Goal" :in-theory (enable aset1))))

(defthm alen1-of-aset1
  (equal (alen1 array-name (aset1 array-name array n val))
         (if (eq :header n)
             (car (cadr (assoc-keyword :dimensions val)))
           (alen1 array-name array)))
  :hints (("Goal" :in-theory (e/d (alen1)
                                  (alen1-intro alen1-intro2)))))

(defthm header-of-nil
  (equal (header name nil)
         nil)
  :hints (("Goal" :in-theory (enable header))))

(defthm default-of-nil
  (equal (default name nil)
         nil)
  :hints (("Goal" :in-theory (e/d (default) (default-intro)))))

(defthm assoc-equal-of-header-and-compress11
  (implies (and (integerp i)
                (integerp n))
           (equal (assoc-equal :header (compress11 name l i n default))
                  nil))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm header-of-compress11
  (implies (integerp i)
           (equal (header name (compress11 name2 array i n default))
                 nil))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm default-of-compress11
  (implies (integerp i)
           (equal (default name (compress11 name2 array i n default))
                  nil))
  :hints (("Goal" :in-theory (enable compress11))))

;odd rhs
(defthm default-of-compress1
  (equal (default name (compress1 name2 l))
         (if (or (equal (array-order (header name2 l)) '<)
                 (equal (array-order (header name2 l)) '>))
             (default name2 l)
           (default name l)))
  :hints (("Goal" :in-theory (e/d (compress1 default) (array-order default-intro)))))

(defthm default-of-aset1
  (implies (integerp n)
           (equal (default array-name (aset1 array-name array n val))
                  (default array-name array)))
  :hints (("Goal" :in-theory (enable aset1))))

(defthm alistp-of-compress11
  (implies (alistp array)
           (alistp (compress11 name array i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm alistp-of-compress1
  (implies (and (alistp array)
                (consp (header array-name array)) ;why?
                )
           (alistp (compress1 array-name array)))
  :hints (("Goal" :in-theory (enable compress1))))

(defthm integerp-of-car-of-assoc-equal-when-bounded-integer-alistp
  (implies (and (bounded-integer-alistp array n)
                (assoc-equal i array))
           (equal (integerp (car (assoc-equal i array)))
                  (not (eq :header (car (assoc-equal i array))))))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp assoc-equal))))

(defthm bound-of-car-of-assoc-equal-when-bounded-integer-alistp
  (implies (and (bounded-integer-alistp array n)
                (natp n)
                (assoc-equal i array))
           (equal (< (car (assoc-equal i array)) n)
                  (if (eq :header (car (assoc-equal i array)))
                      (not (equal n 0))
                    t)))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp assoc-equal))))

(defthmd assoc-equal-when-bounded-integer-alistp-out-of-bounds
  (implies (and (bounded-integer-alistp array bound)
                (<= bound index)
                (natp index))
           (equal (assoc-equal index array)
                  nil))
  :hints (("Goal" :in-theory (e/d (bounded-integer-alistp assoc-equal) ()))))

(defthm bound2-of-car-of-assoc-equal-when-bounded-integer-alistp
  (implies (and (bounded-integer-alistp array n)
                (assoc-equal i array))
           (not (< (car (assoc-equal i array)) 0)))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp assoc-equal))))

(defthm bounded-integer-alistp-of-compress11
  (implies (and (bounded-integer-alistp array n)
                (natp n))
           (bounded-integer-alistp (compress11 name array i index default) n))
  :hints (("Goal" :in-theory (e/d (compress11 bounded-integer-alistp) (car-of-assoc-equal-strong
                                                                       car-of-assoc-equal-cheap)))))

(defthm bounded-integer-alistp-of-cons
  (equal (bounded-integer-alistp (cons item array) n)
         (and (bounded-integer-alistp array n)
              (or (eq :header (car item))
                  (and (natp (car item))
                       (natp n)
                       (< (car item) n)))))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp))))


(defthm bounded-integer-alistp-of-nil
  (equal (bounded-integer-alistp 'nil n)
         t)
  :hints (("Goal" :in-theory (enable bounded-integer-alistp))))

(in-theory (disable array-order))

(defthm bounded-integer-alistp-of-compress1
  (implies (and (bounded-integer-alistp array n)
                (natp n) ;drop?
                )
           (iff (bounded-integer-alistp (compress1 array-name array) n)
                (header array-name array)                 ;why?
                ))
  :hints (("Goal" :in-theory (enable compress1 ;bounded-integer-alistp
                                     ))))

(defthm consp-of-header
  (implies (array1p name array)
           (consp (header name array)))
  :hints (("Goal" :in-theory (e/d (array1p-rewrite dimensions header)
                                  (dimensions-intro)))))

(defthm array1p-of-aset1
  (implies (and (natp index)
                (< index (alen1 array-name array))
                (array1p array-name array))
           (array1p array-name (aset1 array-name array index val)))
  :hints (("Goal" :in-theory (e/d (aset1 array1p-rewrite2 dimensions ALEN1 maximum-length)
                                  (dimensions-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm assoc-keyword-of-cons-same
  (equal (assoc-keyword key (cons key lst))
         (cons key lst))
  :hints (("Goal" :in-theory (enable assoc-keyword))))

(defthm assoc-keyword-of-cons-diff
  (implies (not (equal key key2))
           (equal (assoc-keyword key (cons key2 lst))
                  (assoc-keyword key (cdr lst))))
  :hints (("Goal" :in-theory (enable assoc-keyword))))

;according to array1p, the maximum-length field of an array can be at most *maximum-positive-32-bit-integer* = 2147483647
;and the length (first dimension) of the array is at most 2147483646 since it must be strictly smaller than the :maximum-length (why strictly?)
;; Note that array1p disallows arrays of size 0 (why?), so this function does also.
(defund make-empty-array-with-default (name size default)
  (declare (type symbol name)
           (type (integer 1 2147483646) size)
           (xargs :guard-hints (("Goal" :in-theory (enable array1p)))))
  (compress1 name
             (acons-fast :header (list :dimensions (list size)
                                       ;;ffixme think about this:
                                       :maximum-length (min (* 2 size) *maximum-positive-32-bit-integer* ;the disassembled code was shorter with 2147483647 here than with *maximum-positive-32-bit-integer*
                                                            )
                                       :default default
                                       :name name)
                         nil)))

(defthm default-of-make-empty-array-with-default
  (equal (default dag-parent-array-name (make-empty-array-with-default dag-parent-array-name size default))
         default)
  :hints (("Goal" :in-theory (e/d (make-empty-array-with-default default) (default-intro)))))

;; Make an array with SIZE elements (and name NAME), where every index has the value nil.
(defund make-empty-array (name size)
  (declare (type symbol name)
           (type (integer 1 2147483646) size)
           (xargs :guard-hints (("Goal" :in-theory (enable array1p len)))))
  (make-empty-array-with-default name size nil))

(in-theory (disable (:e make-empty-array))) ;; Avoid exposing a constant involving a :header

(defthm default-of-make-empty-array
  (equal (default dag-parent-array-name (make-empty-array dag-parent-array-name size))
         nil)
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm array1p-of-make-empty-array-with-default
  (equal (array1p array-name (make-empty-array-with-default array-name len default))
         (and (posp len)
              (<= len 2147483646)
              (symbolp array-name)))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm array1p-of-make-empty-array
  (equal (array1p array-name (make-empty-array array-name len))
         (and (posp len)
              (<= len 2147483646)
              (symbolp array-name)))
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm dimensions-of-make-empty-array-with-default
  (implies (and (posp len)
                (<= len 2147483646)
                (symbolp array-name))
           (equal (dimensions array-name (make-empty-array-with-default array-name len default))
                  (list len)))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm alen1-of-make-empty-array-with-default
  (implies (and (posp len)
                (<= len 2147483646)
                (symbolp array-name))
           (equal (alen1 array-name (make-empty-array-with-default array-name len default))
                  len))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm dimensions-of-make-empty-array
  (implies (and (posp len)
                (<= len 2147483646)
                (symbolp array-name))
           (equal (dimensions array-name (make-empty-array array-name len))
                  (list len)))
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm alen1-of-make-empty-array
  (implies (and (posp len)
                (<= len 2147483646)
                (symbolp array-name))
           (equal (alen1 array-name (make-empty-array array-name len))
                  len))
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm rationalp-of-alen1-when-array1p
  (implies (array1p array-name array)
           (rationalp (alen1 array-name array)))
  :hints (("Goal" :in-theory (enable array1p-rewrite2))))

(defthm rationalp-of-nth-of-0-and-dimensions-when-array1p
  (implies (array1p array-name array)
           (rationalp (nth 0 (dimensions array-name array))))
  :hints (("Goal" :in-theory (enable array1p-rewrite2))))

(defthm natp-of-nth-of-0-and-dimensions-when-array1p
  (implies (array1p array-name array)
           (natp (nth 0 (dimensions array-name array))))
  :hints (("Goal" :in-theory (enable array1p-rewrite2))))

(defthm consp-of-dimensions-when-array1p
  (implies (array1p dag-array-name dag-array)
           (consp (dimensions dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable array1p-rewrite2))))

;requires that the arrays must be big enough for max-nodenum to be a valid index
;when copying a whole array, consider calling compress1 for speed?
(defun copy-array-vals (max-nodenum from-array-name from-array to-array-name to-array)
  (declare (xargs :measure (nfix (+ 1 max-nodenum))
                  :guard (and (rationalp max-nodenum)
                              (array1p from-array-name from-array)
                              (array1p to-array-name to-array)
                              (< max-nodenum (alen1 from-array-name from-array))
                              (< max-nodenum (alen1 to-array-name to-array)))))
  (if (not (natp max-nodenum))
      to-array
    (copy-array-vals (+ -1 max-nodenum)
                     from-array-name
                     from-array
                     to-array-name
                     (aset1 to-array-name to-array max-nodenum (aref1 from-array-name from-array max-nodenum)))))

;new stuff:

(defthm natp-of-car-of-assoc-equal
  (equal (natp (car (assoc-equal :header array)))
         nil)
  :hints (("Goal" :in-theory (enable assoc-equal))))


(local
 (defthmd assoc-equal-of-compress11
  (implies (and (<= i index)
                (< index n)
                (integerp i)
                (integerp index)
                (integerp n)
                )
           (equal (assoc-equal index (compress11 name l i n default))
                  (if (equal default (cdr (assoc-equal index l)))
                      nil
                    (assoc-equal index l))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable compress11)))))

(local
 (defthmd assoc-equal-of-compress11-too-high
  (implies (and (<= n index) ;this case
                (<= i index)
                (integerp i)
                (integerp index)
                (integerp n)
                )
           (equal (assoc-equal index (compress11 name l i n default))
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable compress11)))))

(defthm assoc-equal-of-compress11-both
  (implies (and (integerp i)
                (integerp index)
                (integerp n))
           (equal (assoc-equal index (compress11 name l i n default))
                  (if (or (< index i)
                          (<= n index))
                      nil
                    (if (equal default (cdr (assoc-equal index l)))
                        nil
                      (assoc-equal index l)))))
  :hints (("Goal" :use (assoc-equal-of-compress11-too-high
                        (:instance assoc-equal-of-compress11))
           :in-theory (e/d ()
                           (assoc-equal)))))

(defthm not-of-myduplicate-keysp-of-compress11
  (not (myduplicate-keysp (compress11 name l i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm assoc-equal-of-compress1
  (implies (and (natp index)
                ;; (< index (car (dimensions name l)))
                (array1p name l) ;name is mostly irrel here?
                (symbolp name)
                )
           (equal (assoc-equal index (compress1 name l))
                  (if (and (equal (cdr (assoc-equal index l))
                                  (default name l))
                           (or (equal (array-order (assoc-equal :header l)) '>)
                               (equal (array-order (assoc-equal :header l)) '<)))
                      ;;if it's equal to the default and we are sorting, then it gets removed
                      nil
                    (assoc-equal index l))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (compress1 array1p-rewrite2
                                      header
                                      assoc-equal-when-bounded-integer-alistp-out-of-bounds)
                           (ASSOC-EQUAL)))))


(in-theory (disable (:i assoc-equal)))

;move this and all the supporting stuff above!
(defthm aref1-of-aset1-same
  (implies (and (array1p array-name array) ;;(alistp array)
                (natp index)
                (< index (alen1 array-name array))
                )
           (equal (aref1 array-name (aset1 array-name2 array index val) index)
                  val))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-diff
  (implies (and (not (equal index1 index2))
                (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name array index1 val) index2)
                  (aref1 array-name array index2)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-both
  (implies (and (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name array index1 val) index2)
                  (if (equal index1 index2)
                      val
                    (aref1 array-name array index2)))))

(defund array-to-alist-aux (n len array-name array acc)
  (declare (xargs :measure (nfix (+ 1 (- len n)))
                  :guard (and (array1p array-name array)
                              (natp n)
                              (natp len)
                              (<= n (+ 1 len))
;                              (alistp acc)
                              (<= len (alen1 array-name array)))))
  (if (or (<= len n)
          (not (natp n))
          (not (natp len)))
      acc
    (let* ((val (aref1 array-name array n)))
      (array-to-alist-aux (+ 1 n) len array-name array (acons-fast n val acc)))))

(defthm alistp-of-array-to-alist-aux
  (implies (alistp acc)
           (alistp (array-to-alist-aux n len array-name array acc)))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm len-of-array-to-alist-aux
  (implies (and (natp len)
                (natp n))
           (equal (len (array-to-alist-aux n len array-name array acc))
                  (+ (nfix (- len n))
                     (len acc))))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm consp-of-array-to-alist-aux
  (implies (and (natp len)
                (natp n))
           (equal (consp (array-to-alist-aux n len array-name array acc))
                  (or (posp (nfix (- len n)))
                      (consp acc))))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm car-of-array-to-alist-aux
  (equal (car (array-to-alist-aux n len array-name array acc))
         (if (and (natp len)
                  (natp n)
                  (< n len))
             ;; usual case:
             (cons (+ -1 len) (aref1 array-name array (+ -1 len)))
           (car acc)))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

;; The indices in the result will be decreasing.
(defund array-to-alist (len array-name array)
  (declare (xargs :guard (and (array1p array-name array)
                              (natp len)
                              (<= len (alen1 array-name array)))))
  (array-to-alist-aux 0 len array-name array nil))

(defthm len-of-array-to-alist
  (implies (natp len)
           (equal (len (array-to-alist len array-name array))
                  len))
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm true-listp-of-array-to-alist-type
  (true-listp (array-to-alist len array-name array))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm car-of-array-to-alist
  (implies (posp len)
           (equal (car (array-to-alist len array-name array))
                  (cons (+ -1 len) (aref1 array-name array (+ -1 len)))))
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defun print-array-vals (high-index low-index array-name array)
  (declare (xargs :measure (+ 1 (nfix (- (+ 1 high-index) low-index)))
                  :guard (and (symbolp array-name)
                              (integerp high-index)
                              (array1p array-name array)
                              (< high-index (alen1 array-name array)))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))
                  )
           (type (integer 0 *) low-index))
  (if (or (< high-index low-index)
          (not (natp low-index))
          (not (natp high-index)))
      nil
    (print-array-vals (prog2$ (cw " ~y0"
                                  (cons high-index (aref1 array-name array high-index)) ;save this cons?
                                  )
                              (+ -1 high-index))
                      low-index
                      array-name
                      array)))


;fixme whitespace before and/or after isn't quite right
;does this do the right thing for very small arrays?
;prints the low elems-to-print elements
(defun print-array2 (array-name array elem-count-to-print)
  (declare (type (integer 0 *) elem-count-to-print)
           (xargs :guard (implies (not (eql 0 elem-count-to-print))
                                  (and (symbolp array-name)
                                       (array1p array-name array)
                                       (<= elem-count-to-print (alen1 array-name array))))
                  :guard-hints (("Goal" :in-theory (enable ARRAY1P-rewrite)))))
  (prog2$
   ;;print the open paren:
   (cw "(")
   (prog2$
    ;;print the elements
    (if (eql 0 elem-count-to-print)
        nil
      (if (equal 1 elem-count-to-print)
          (cw "~x0" (cons 0 (aref1 array-name array 0)))
        (prog2$ (cw "~y0" (cons (+ -1 elem-count-to-print) (aref1 array-name array (+ -1 elem-count-to-print)))) ;can we skip the conses?
                (prog2$ (print-array-vals (+ -2 elem-count-to-print) 1 array-name array)
                        (cw " ~x0" (cons 0 (aref1 array-name array 0))) ;no newline
                        ))))
    ;;print the close paren:
    (cw ")~%"))))

;Consider adding an option to reuse an existing array if large enough?
; The length of the resulting array is one more than the max key in the alist, unless the alist is empty, in which case the length is 1.
(defund make-into-array (array-name alist)
  (declare (xargs :guard (and (true-listp alist)
                              (bounded-natp-alistp alist (+ -1 *maximum-positive-32-bit-integer*)) ; might be able to drop the -1 if array1p is weakened a bit
                              )
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite))))
           (type symbol array-name))
  (let* ((len (if (consp alist)
                  ;; normal case:
                  (+ 1 (max-key alist 0)) ;could save this max if we know it's a dag-lst...
                ;; compress1 must be given a dimension of at least 1
                1)))
    (compress1 array-name
               (acons-fast :header (list :dimensions (list len)
                                         ;;ffixme think about this:
                                         :maximum-length (min (* 2 len) *maximum-positive-32-bit-integer* ;the disassembled code was shorter with 2147483647 here than with *maximum-positive-32-bit-integer*
                                                              )
                                         :default nil ;; fixme?
                                         :name array-name)
                           alist))))

(defthm default-of-make-into-array
  (equal (default array-name (make-into-array array-name alist))
         nil)
  :hints (("Goal" :in-theory (enable array1p compress1 make-into-array))))

;rename make-into-array-with-slack?
;LEN must exceed the largest key in ALIST; this allows for some slack space of empty slots
;todo: add an option to reuse existing array if large enough?
;todo: adapt this to use max-key like the one above?
(defund make-into-array-with-len (array-name alist len)
  (declare (type (integer 1 2147483646) len)
           (type symbol array-name)
           (xargs :guard (and (true-listp alist)
                              (bounded-natp-alistp alist len))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))))
  (compress1 array-name
             (acons-fast :header (list :dimensions (list len)
                                       ;;ffixme think about this:
                                       :maximum-length (min (* 2 len) *maximum-positive-32-bit-integer* ;the disassembled code was shorter with 2147483647 here than with *maximum-positive-32-bit-integer*
                                                            )
                                       :default nil ; ;fixme?
                                       :name array-name)
                         alist)))

(defthm dimensions-of-make-into-array-with-len
  (equal (dimensions array-name (make-into-array-with-len array-name alist len))
         (list len))
  :hints (("Goal" :in-theory (enable make-into-array-with-len))))

(defthm alen1-of-make-into-array-with-len
  (equal (alen1 array-name (make-into-array-with-len array-name alist len))
         len)
  :hints (("Goal" :in-theory (enable make-into-array-with-len))))

(defthm array1p-of-make-into-array-with-len
  (implies (and (symbolp array-name)
                (bounded-integer-alistp alist len)
                (posp len)
                (< len 2147483647))
           (array1p array-name (make-into-array-with-len array-name alist len)))
  :hints (("Goal" :in-theory (enable make-into-array-with-len array1p-rewrite))))

(defthm array1p-of-compress1
  (implies (array1p array-name l)
           (array1p array-name (compress1 array-name l)))
  :hints (("Goal" :in-theory (enable array1p compress1 header))))

(defthm array1p-of-make-into-array
  (implies (and (bounded-natp-alistp alist 2147483646)
                (true-listp alist)
                ;alist
                (symbolp array-name)
                )
           (equal (array1p array-name (make-into-array array-name alist))
                  t))
  :hints (("Goal" :in-theory (enable array1p compress1 make-into-array))))

;; (defthm assoc-equal-of-compress1
;;   (implies (and (natp index)
;; ;                (< index (car (dimensions name l)))
;;                 (array1p name l)
;;                 ;;fixme:
;;                 (or (equal '< (ARRAY-ORDER (HEADER NAME L)))
;;                     (equal '> (ARRAY-ORDER (HEADER NAME L)))))
;;            (equal (assoc-equal index (compress1 name l))
;;                   ;;improve this?
;;                   (if (equal (cdr (assoc-equal index l)) (default name l))
;;                       nil
;;                     (assoc-equal index l))))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable compress1 array1p header dimensions
;;                               assoc-equal-when-bounded-integer-alistp-out-of-bounds))))

(defthm array1p-of-cons-header
  (equal (ARRAY1P NAME2 (CONS (LIST :HEADER
                                    :DIMENSIONS (LIST dim)
                                    :MAXIMUM-LENGTH max
                                    :DEFAULT NIL
                                    :NAME NAME)
                              ALIST))
         (and (bounded-integer-alistp alist dim)
              (posp dim)
              (< dim max)
              (symbolp name2)
              (<= MAX 2147483647)
              (integerp max)))
  :hints (("Goal" :in-theory (enable ARRAY1P-rewrite))))

(defthm aref1-of-make-into-array
  (implies (and (bounded-natp-alistp alist 2147483646)
                (true-listp alist)
                alist
                (symbolp array-name)
                (natp index)
                (< index (max-key alist 0))
                )
           (equal (aref1 array-name (make-into-array array-name alist) index)
                  (cdr (assoc-equal index alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable array1p ;compress1
                              ARRAY-ORDER
                              make-into-array
                              aref1))))

(defthm aref1-of-make-empty-array-with-default
  (implies (and (symbolp array-name)
                (natp index) ;gen?
;                (< index len) ;we get nil if the index is out of bounds
		(posp len)
		(< len 2147483647)
                )
           (equal (aref1 array-name (make-empty-array-with-default array-name len default) index)
                  default))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable array1p ;compress1
                              array-order
                              make-empty-array-with-default
                              aref1))))

(defthm aref1-of-make-empty-array
  (implies (and (symbolp array-name)
                (natp index) ;gen?
;                (< index len) ;we get nil if the index is out of bounds
		(posp len)
		(< len 2147483647)
                )
           (equal (aref1 array-name (make-empty-array array-name len) index)
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable array1p ;compress1
                              array-order
			      make-empty-array
                              aref1))))

(in-theory (disable (:executable-counterpart break$))) ;keeps it from breaking when it's evaluted during a proof, e.g., proofs about aset1-safe

;this makes sure the index is in bounds, which prevents memory from getting trashed if this is called on bad arguments
(defund aset1-safe (name l n val)
  (declare (xargs :guard (and (array1p name l)
                              (integerp n)
                              (>= n 0)
                              (< n (alen1 name l)))))
  (if (< n (alen1 name l))
      (aset1 name l n val)
    (progn$ ;(print-list l)
            (cw "Bad index, ~x0, for array ~x1 with len ~x2." n name (alen1 name l))
            (break$) ;(car 7) ;this causes a crash and is better than a hard-error since it puts us into the debugger.
            ;;aset1-safe is logically just aset1
            (aset1 name l n val))))

(defthm aset1-safe-becomes-aset1
  (implies (< n (alen1 name l))
           (equal (aset1-safe name l n val)
                  (aset1 name l n val)))
  :hints (("Goal" :in-theory (enable aset1-safe))))

(defun valid-array-indexp (index array-name array)
  (declare (xargs :guard (array1p array-name array)))
  (and (natp index)
       (< index (alen1 array-name array))))

(defthmd assoc-equal-when-bounded-array1p-out-of-bounds
  (implies (and (<= (alen1 array-name array) index)
                (array1p array-name array)
                (natp index))
           (equal (assoc-equal index array)
                  nil))
  :hints (("Goal" :in-theory (e/d (assoc-equal-when-bounded-integer-alistp-out-of-bounds
                                   array1p-rewrite header)
                                  ()))))

(defthmd not-assoc-equal-when-bounded-integer-alistp
  (implies (and (bounded-integer-alistp alist bound)
                (natp bound)
                (natp n)
                (<= bound n))
           (not (assoc-equal n alist)))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp))))

;; Disabled since this can be expensive and is rarely needed.
(defthmd aref1-when-too-large
  (implies (and (<= (alen1 array-name array) n)
                (array1p array-name array)
                (natp n))
           (equal (aref1 array-name array n)
                  (default array-name array)))
  :hints (("Goal" :in-theory (e/d (AREF1 ARRAY1P-rewrite HEADER not-assoc-equal-when-bounded-integer-alistp)
                                  ()))))

(defthm aref1-when-too-large-cheap
  (implies (and (<= (alen1 array-name array) n)
                (array1p array-name array)
                (natp n))
           (equal (aref1 array-name array n)
                  (default array-name array)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable aref1-when-too-large))))

(local
 (defthm aref1-of-compress1-small
   (implies (and (< n (alen1 array-name array))
                 (natp n)
                 ;;(array1p array-name array)
                 (alistp array)
                 (integerp (ALEN1 ARRAY-NAME ARRAY))
                 )
            (equal (aref1 array-name (compress1 array-name array) n)
                   (aref1 array-name array n)))
   :hints (("Goal" :in-theory (e/d (aref1 compress1 header default) (default-intro))))))

(local
 (defthm aref1-of-compress1-too-large
   (implies (and (<= (alen1 array-name array) n)
                 (natp n)
                 (array1p array-name array)
                 ;;(alistp array)
                 ;;(integerp (ALEN1 ARRAY-NAME ARRAY))
                 )
            (equal (aref1 array-name (compress1 array-name array) n)
                   (default array-name array)))
   :hints (("Goal" :in-theory (e/d (default aref1-when-too-large aref1 compress1 header) (default-intro))))))

(defthm aref1-of-compress1
  (implies (and (natp n)
                (array1p array-name array))
           (equal (aref1 array-name (compress1 array-name array) n)
                  (if (< n (alen1 array-name array))
                      (aref1 array-name array n)
                    (default array-name array))))
  :hints (("Goal" :in-theory (e/d (aref1-when-too-large aref1 compress1 header default) (default-intro)))))

(defthm aref1-of-cons-of-cons-of-header
  (implies (natp n)
           (equal (aref1 array-name (cons (cons :header header) alist) n)
                  (if (assoc-equal n alist)
                      (aref1 array-name alist n)
                    (cadr (assoc-keyword :default header)))))
  :hints (("Goal" :in-theory (enable aref1 header))))

;; This one has no IF in the RHS
(defthm aref1-of-cons-of-cons-of-header-alt
  (implies (and (natp n)
                (equal (default array-name array)
                       (cadr (assoc-keyword :default header-args))))
           (equal (aref1 array-name (cons (cons :header header-args) array) n)
                  (aref1 array-name array n)))
  :hints (("Goal" :in-theory (enable aref1 header))))

(defthmd aref1-when-not-assoc-equal
  (implies (not (assoc-equal n alist))
           (equal (aref1 array-name alist n)
                  (default array-name alist)))
  :hints (("Goal" :in-theory (enable aref1))))

(defthm dimensions-of-make-into-array
  (equal (dimensions array-name (make-into-array array-name alist))
         (if (consp alist)
             (list (+ 1 (max-key alist 0)))
           (list 1)))
  :hints (("Goal" :in-theory (enable make-into-array))))

(defthm alen1-of-make-into-array
  (equal (alen1 array-name (make-into-array array-name alist))
         (if (consp alist)
             (+ 1 (max-key alist 0))
           1))
  :hints (("Goal" :in-theory (enable make-into-array))))

;; (defthm assoc-equal-of-header-of-compress1
;;   (equal (assoc-equal :header (compress1 array-name array))
;;          (assoc-equal :header array))
;;   :hints (("Goal" :in-theory (e/d (compress1) ()))))

(defthm header-of-aset1
  (implies (integerp n) ;gen?
           (equal (header name (aset1 name l n val))
                  (header name l)))
  :hints (("Goal" :in-theory (enable aset1))))

(defthm array1p-forward-to-<=-of-alen1
  (implies (array1p array-name array)
           (<= (alen1 array-name array)
               2147483646))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable array1p-rewrite))))

(defthm array1p-forward-to-<=-of-alen1-2
  (implies (array1p array-name array)
           (<= 1 (alen1 array-name array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable array1p-rewrite))))

(defthm dimensions-when-not-consp-of-header-cheap
  (implies (not (consp (header name l)))
           (equal (dimensions name l)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (dimensions) (dimensions-intro)))))

(defthm alen1-type
  (implies (array1p name l)
           (posp (alen1 name l)))
  :rule-classes :type-prescription)

(defthm natp-of-alen1
  (implies (array1p name l)
           (natp (alen1 name l))))

;; Not quite true...
;; (defthm aset1-of-aset1-same
;;   (implies (and (array1p array-name array)
;;                 (natp index)
;;                 (< index (alen1 array-name array)))
;;            (equal (aset1 array-name (aset1 array-name array index val1) index val2)
;;                   (aset1 array-name array index val2)))
;;   :hints (("Goal" :in-theory (e/d (array1p-rewrite
;;                                    compress1
;;                                    header
;;                                    default
;;                                    aset1
;;                                    dimensions
;;                                    alen1)
;;                                   (dimensions-intro
;;                                    alen1-intro
;;                                    alen1-intro2)))))

;; A simple theorem like aset1-of-aset1-same would not be true
(defthm aref1-of-aset1-of-aset1-same
  (implies (and (array1p array-name array)
                (natp index)
                (< index (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index val1) index val2) read-index)
                  (aref1 array-name (aset1 array-name array index val2) read-index)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-of-aset1-same-diff
  (implies (and (syntaxp (smaller-termp index2 index1))
                (not (equal index1 index2))
                (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index1 val1) index2 val2) read-index)
                  (aref1 array-name (aset1 array-name (aset1 array-name array index2 val2) index1 val1) read-index)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-of-aset1-same-both
  (implies (and (syntaxp (smaller-termp index2 index1)) ;prevent loops
                (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index1 val1) index2 val2) read-index)
                  (if (equal index1 index2)
                      (aref1 array-name (aset1 array-name array index2 val2) read-index)
                    (aref1 array-name (aset1 array-name (aset1 array-name array index2 val2) index1 val1) read-index)))))

(in-theory (disable (:e make-into-array-with-len))) ;blew up

(defthm array1p-of-cons-of-header-and-nil
  (equal (array1p array-name
                  (list (list :header
                              :dimensions dims
                              :maximum-length maximum-length
                              :default default
                              :name array-name)))
         (and (symbolp array-name)
              (equal 1 (len dims))
              (true-listp dims)
              (posp (car dims))
              (natp maximum-length)
              (< (car dims) maximum-length)
              (<= maximum-length 2147483647)))
  :hints (("Goal" :in-theory (enable array1p-rewrite))))
