; A recognizer for lists of unsigned bytes.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; ALL-UNSIGNED-BYTE-P is like the function UNSIGNED-BYTE-LISTP from
;; std/typed-lists but does not require the list to be a true list.  Thus, it
;; may allow for better congruence rules.  It also may be more efficient, since
;; it only calls expt once.

(include-book "all-integerp")
(in-theory (disable unsigned-byte-p))

;;could rename to all-natp-less-than
(defund all-unsigned-byte-p-exec (bound lst)
  (declare (xargs :guard (natp bound)))
  (if (consp lst)
      (let ((item (first lst)))
        (and (natp item)
             (< item bound)
             (all-unsigned-byte-p-exec bound (rest lst))))
    t))

;; Test whether all elements of LST are unsigned-byte-ps of size SIZE.  This
;; does not require the list to be a true-list.  For speed, we compute the EXPT
;; once instead of per element.
(defund all-unsigned-byte-p (size lst)
  (declare (type t size lst)
           (xargs :normalize nil
                  :guard-hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P)))
                  :verify-guards nil))
  (mbe :exec
       (if (not (consp lst))
           t ;need to return t even if size is not a natp
         (and (natp size)
              (all-unsigned-byte-p-exec (expt 2 size) lst)))
       :logic
       (if (consp lst)
           (and (unsigned-byte-p size (first lst))
                (all-unsigned-byte-p size (rest lst)))
         t)))

(defthmd all-unsigned-byte-p-rewrite
  (implies (natp size)
           (equal (all-unsigned-byte-p size lst)
                  (all-unsigned-byte-p-exec (expt 2 size) lst)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p
                                     all-unsigned-byte-p-exec
                                     unsigned-byte-p))))

(verify-guards all-unsigned-byte-p :hints (("Goal" :expand ((all-unsigned-byte-p-exec 1 lst)
                                                             (unsigned-byte-p 0 (car lst))
                                                             (unsigned-byte-p size (car lst))
                                                             (all-unsigned-byte-p-exec (expt 2 size) lst))
                                             :in-theory (e/d (all-unsigned-byte-p-rewrite)
                                                             (natp)))))

(defthm all-unsigned-byte-p-of-cons
  (equal (all-unsigned-byte-p size (cons lst0 lst))
         (and (unsigned-byte-p size lst0)
              (all-unsigned-byte-p size lst)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

(defthm use-all-unsigned-byte-p-for-car
  (implies (and (all-unsigned-byte-p size lst)
                (consp (double-rewrite lst)))
           (unsigned-byte-p size (car lst)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-of-append
  (equal (all-unsigned-byte-p size (append lst lst0))
         (and (all-unsigned-byte-p size lst)
              (all-unsigned-byte-p size lst0)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-of-union-equal
  (equal (all-unsigned-byte-p size (union-equal lst lst0))
         (and (all-unsigned-byte-p size lst)
              (all-unsigned-byte-p size lst0)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p union-equal))))

(defthm all-unsigned-byte-p-when-not-consp
  (implies (not (consp (double-rewrite lst)))
           (equal (all-unsigned-byte-p size lst)
                  t))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-of-revappend
  (implies (and (all-unsigned-byte-p size lst)
                (all-unsigned-byte-p size lst0))
           (all-unsigned-byte-p size (revappend lst lst0))))

(defthm all-unsigned-byte-p-of-cdr
  (implies (all-unsigned-byte-p size lst)
           (equal (all-unsigned-byte-p size (cdr lst))
                  t)))

(defthm all-unsigned-byte-p-of-nthcdr
  (implies (all-unsigned-byte-p size lst)
           (equal (all-unsigned-byte-p size (nthcdr lst0 lst))
                  t))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p nthcdr))))


;; (defthm all-unsigned-byte-p-of-remove-1
;;   (implies (all-unsigned-byte-p size lst)
;;            (all-unsigned-byte-p size (bag::remove-1 lst0 lst)))
;;     :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-of-remove-equal
  (implies (all-unsigned-byte-p size lst)
           (all-unsigned-byte-p size (remove-equal lst0 lst))))

(defthm all-unsigned-byte-p-of-last
  (implies (all-unsigned-byte-p size lst)
           (all-unsigned-byte-p size (last lst))))

;; (defthmd all-unsigned-byte-p-when-perm
;;   (implies (bag::perm lst lst0)
;;            (equal (all-unsigned-byte-p size lst)
;;                   (all-unsigned-byte-p size lst0))))

(defthm all-unsigned-byte-p-of-true-list-fix
  (equal (all-unsigned-byte-p size (true-list-fix lst))
         (all-unsigned-byte-p size lst))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

;; (defcong bag::perm
;;   equal (all-unsigned-byte-p size lst)
;;   2
;;   :hints (("Goal" :use (:instance all-unsigned-byte-p-when-perm
;;                                   (lst0 bag::lst-equiv)))))

;rename
(defthm use-all-unsigned-byte-p
  (implies (and (all-unsigned-byte-p size free-lst)
                (member-equal x free-lst))
           (unsigned-byte-p size x)))

;rename
(defthm use-all-unsigned-byte-p-2
  (implies (and (member-equal x free-lst)
                (all-unsigned-byte-p size free-lst))
           (unsigned-byte-p size x)))

(defthm all-unsigned-byte-p-of-add-to-set-equal
  (equal (all-unsigned-byte-p size (add-to-set-equal lst0 lst))
         (and (unsigned-byte-p size lst0)
              (all-unsigned-byte-p size lst)))
  :hints (("Goal" :in-theory (enable add-to-set-equal))))

(defthm booleanp-of-all-unsigned-byte-p
  (booleanp (all-unsigned-byte-p a b)))

(defthm all-unsigned-byte-p-of-nil
  (all-unsigned-byte-p n nil)
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

(defthm unsigned-byte-p-of-nth
  (implies (and (all-unsigned-byte-p size lst)
                (<= 0 n) ;(integerp n)
                (< n (len lst)))
           (unsigned-byte-p size (nth n lst)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p nth))))

(defthm all-unsigned-byte-p-of-nthcdr-longer
  (implies (and (all-unsigned-byte-p size (nthcdr free x))
                (<= free n)
                (integerp n))
           (all-unsigned-byte-p size (nthcdr n x)))
  :hints (("Goal" :in-theory (e/d (all-unsigned-byte-p nthcdr)
                                  (;; for speed:
                                   use-all-unsigned-byte-p)))))

(defthm all-unsigned-byte-p-implies-all-integerp
  (implies (all-unsigned-byte-p free x)
           (all-integerp x))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p all-integerp))))

(defthm all-unsigned-byte-p-of-take
  (implies (all-unsigned-byte-p size lst)
           (equal (all-unsigned-byte-p size (take n lst))
                  (<= (nfix n) (len lst))))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p take))))
