; Array creation
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;Unlike heap.lisp, this one is in the JVM package

;; This book is about building array objects

(include-book "heap")
(include-book "arrays0")
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(include-book "tools/flag" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))

;; (defthm byte-p-list-of-repeat
;;   (implies (SIGNED-BYTE-P 8 item)
;;            (byte-p-list (repeat n item)))
;;   :hints (("Goal" :in-theory (enable repeat byte-p-list))))

;;;
;;; initial-array-contents
;;;

;; Compute the initial contents of a 1-d array of the given type and length.
(defund initial-array-contents (type length)
  (declare (xargs :guard (jvm::typep type))
           (type (integer 0 *) length))
  (acl2::repeat length (acl2::default-value type)))

; If we'll always open initial-array-contents we don't need these theorems about it:

(defthm acl2::len-of-initial-array-contents
  (equal (len (initial-array-contents type length))
         (nfix length))
  :hints (("Goal" :in-theory (enable initial-array-contents))))

(defthm acl2::consp-of-initial-array-contents
  (implies (and (< 0 count)
                (integerp count))
           (equal (consp (initial-array-contents type count))
                  t))
  :hints (("Goal" :in-theory (enable initial-array-contents))))

;; (defthm byte-p-list-of-initial-array-contents
;;   (byte-p-list (initial-array-contents ':byte numcols))
;;   :hints (("Goal" :in-theory (enable initial-array-contents))))

(defthm all-unsigned-byte-p-of-initial-array-contents-boolean
  (acl2::all-unsigned-byte-p 1 (initial-array-contents ':boolean len))
  :hints (("Goal" :in-theory (enable initial-array-contents))))

(defthm all-unsigned-byte-p-of-initial-array-contents-int
  (acl2::all-unsigned-byte-p 32 (initial-array-contents ':int len))
  :hints (("Goal" :in-theory (enable initial-array-contents))))

;todo: what about sign extending?
;todo: more like this?
(defthm all-unsigned-byte-p-of-initial-array-contents-byte
  (acl2::all-unsigned-byte-p 8 (initial-array-contents ':byte len))
  :hints (("Goal" :in-theory (enable initial-array-contents))))

;;;
;;; initialize-one-dim-array
;;;

;We now don't store a separate length field; we just calculate the length from the contents
;what values can element-type have?
;make separate versions for primitive arrays and arrays of ads?
;fixme: should element-type really be called component-type?
;todo: consider inlining this into build-new-array?
(defund initialize-one-dim-array (ad element-type contents heap)
  (declare (xargs :guard (typep element-type)))
  (acl2::set-field ad
                   (acl2::array-contents-pair)
                   contents
                   (acl2::set-class ad
                                    (make-one-dim-array-type element-type)
                                    heap)))

(defthm heapp-of-initialize-one-dim-array
  (implies (and (heapp heap)
                (addressp ad))
           (heapp (initialize-one-dim-array ad element-type contents heap)))
  :hints (("Goal" :in-theory (enable INITIALIZE-ONE-DIM-ARRAY))))

(defthm g-of-initialize-one-dim-array-irrel
  (implies (not (equal ad ad2))
           (equal (g ad (initialize-one-dim-array ad2 type contents heap))
                  (g ad heap)))
  :hints (("Goal" :in-theory (enable initialize-one-dim-array))))

;bozo yuck?
(defthm g-of-initialize-one-dim-array
  (equal (g ad (initialize-one-dim-array ad type contents heap))
         (s (acl2::array-contents-pair)
            contents
            (s (acl2::class-pair)
               (make-one-dim-array-type type)
               (g ad heap))))
  :hints (("Goal" :in-theory (enable initialize-one-dim-array))))

;bozo rename stuff like this
(defthm get-length-field-of-initialize-one-dim-array
  (equal (array-length ad (initialize-one-dim-array ad type contents heap))
         (len contents))
  :hints (("Goal" :in-theory (enable initialize-one-dim-array))))

(defthm get-field-contents-of-initialize-one-dim-array
  (equal (acl2::get-field ad (acl2::array-contents-pair) (initialize-one-dim-array ad type contents heap))
         contents)
  :hints (("Goal" :in-theory (enable initialize-one-dim-array))))

(defthm get-field-class-of-initialize-one-dim-array
  (equal (acl2::get-field ad (acl2::class-pair) (initialize-one-dim-array ad type contents heap))
         (make-one-dim-array-type type))
  :hints (("Goal" :in-theory (enable initialize-one-dim-array acl2::get-class))))

(defthm get-field-of-initialize-one-dim-array-irrel-ad
  (implies (not (equal ad1 ad2))
           (equal (acl2::get-field ad1 pair (initialize-one-dim-array ad2 type contents heap))
                  (acl2::get-field ad1 pair heap)))
  :hints (("Goal" :in-theory (enable initialize-one-dim-array))))

;this may change
(defthm get-field-of-initialize-one-dim-array-irrel-field
  (implies (not (memberp pair (acl2::array-object-fields)))
           (equal (acl2::get-field ad pair (initialize-one-dim-array ad2 type contents heap))
                  (acl2::get-field ad pair heap)))
  :hints (("Goal" :in-theory (enable initialize-one-dim-array))))

(defthm rkeys-of-initialize-one-dim-array
  (implies type
           (equal (acl2::rkeys (initialize-one-dim-array ad type contents heap))
                  (set::insert ad (acl2::rkeys heap))))
  :hints (("Goal" :in-theory (enable initialize-one-dim-array))))


;;;
;;; build-new-array
;;;

;; Allocates an address and builds a new 1-D array with the given component
;; type and containing the given values.  Returns (mv new-ad heap).  This is
;; used when we know the values (e.g., the addresses of sub-arrays) and can
;; skip writing in the default values.
(defun build-new-array (vals component-type heap)
  (declare (xargs :guard (typep component-type))) ;fixme
  (let* ((arrayref (acl2::new-ad (acl2::rkeys heap)))
         (heap (initialize-one-dim-array arrayref component-type vals heap)))
    (mv arrayref heap)))

;;;
;;; build-new-array-default
;;;

;Returns (mv arrayref heap)
;the values put into the array are generated using the default value for the indicated component-type
(defun build-new-array-default (length component-type heap)
  (declare (xargs :guard (and (natp length)
                              (typep component-type))))
  (build-new-array (initial-array-contents component-type length) component-type heap))

;;;
;;; build-multi-dim-array
;;;

;a count of 0 is handled naturally by this
(mutual-recursion
 ;; Initialize a multidimensional array and return its address and the new heap. There must be
 ;; at least one dimension.  Returns (mv ref heap). ;the first dim is for the outermost array.
 (defun build-multi-dim-array (counts array-type heap)
   (declare (xargs :measure (make-ord (+ 1 (nfix (len counts))) (+ 1 0) 1)
                   :guard (and (consp counts)
                               (typep array-type) ;yuck?
                               (is-array-typep array-type)
                               (<= (len counts)
                                   (number-of-array-dimensions array-type))
                               (acl2::nat-listp counts))))
   (let ((component-type (get-array-component-type array-type)))
     (if (endp (rest counts))
         ;;an array with a single dimension:
         (build-new-array-default (first counts) component-type heap)
       ;;an array with more than one dimension:
       (mv-let (ads heap)
         ;;first build the sub-arrays:
         (build-multi-dim-arrays (rest counts) component-type heap (first counts))
         ;;now build the parent array:
         (build-new-array ads component-type heap)))))

 ;; Initialize COUNT multidimensional arrays and return their addresses and the new heap. There must be
 ;; at least one dimension.  Returns (mv refs heap).
 (defun build-multi-dim-arrays (counts array-type heap count)
   (declare (xargs :measure (make-ord (+ 1 (nfix (len counts))) (+ 1 (nfix count)) 1)
                   :guard (and (consp counts)
                               (typep array-type) ;yuck?
                               (is-array-typep array-type)
                               (<= (len counts)
                                   (number-of-array-dimensions array-type))
                               (acl2::nat-listp counts)
                               (natp count))))
   (if (zp count)
       (mv nil heap)
     (mv-let (ad heap)
       (build-multi-dim-array counts array-type heap)
       (mv-let (ads heap)
         (build-multi-dim-arrays counts array-type heap (+ -1 count))
         (mv (cons ad ads)
             heap))))))

(acl2::make-flag build-multi-dim-array)

(defthm-flag-build-multi-dim-array
 (defthm heapp-of-mv-nth-1-of-build-multi-dim-array
   (implies (heapp heap)
            (heapp (mv-nth 1 (build-multi-dim-array counts array-type heap))))
   :flag build-multi-dim-array)
 (defthm heapp-of-mv-nth-1-of-build-multi-dim-arrays
   (implies (heapp heap)
            (heapp (mv-nth 1 (build-multi-dim-arrays counts array-type heap count))))
   :flag build-multi-dim-arrays))

(acl2::defopeners-mut-rec build-multi-dim-array)
(acl2::defopeners-mut-rec build-multi-dim-arrays)
