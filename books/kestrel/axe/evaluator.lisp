; The main (old-style) Axe evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;clean this up!

;todo: reduce the amount of input that needs to be given to make the evaluator, also check that unguarded replacements are correct

;FIXME axe-evaluator-function-info does not include all of the ACL2 primitive functions.  should it?

;; TODO: To evaluate a function defined using MBE, we might prefer to evaluate the :exec part.

;try to include less (but we need the functions to eval them)
(include-book "ihs/basic-definitions" :dir :system) ; for logmaskp
(include-book "kestrel/utilities/terms" :dir :system) ;for GET-FNS-IN-TERM
(include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system)
(include-book "kestrel/booleans/booland" :dir :system)
(include-book "kestrel/booleans/boolor" :dir :system)
(include-book "kestrel/booleans/boolif" :dir :system)
(include-book "kestrel/bv/defs" :dir :system) ;reduce? gets us sbvdiv
(include-book "kestrel/bv/bool-to-bit-def" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/width-of-widest-int" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-write" :dir :system)
(include-book "kestrel/bv-lists/bv-array-clear" :dir :system)
(include-book "kestrel/bv-lists/bv-array-clear-range" :dir :system)
(include-book "kestrel/bv-lists/map-packbv" :dir :system) ;for map-packbv, map-reverse-list, etc.
(include-book "kestrel/bv-lists/map-unpackbv" :dir :system)
(include-book "kestrel/bv-lists/map-reverse-list" :dir :system)
(include-book "kestrel/bv-lists/bytes-to-bits" :dir :system)
(include-book "kestrel/bv-lists/all-signed-byte-p" :dir :system)
(include-book "kestrel/bv-lists/getbit-list" :dir :system)
(include-book "kestrel/bv-lists/map-slice" :dir :system)
(include-book "kestrel/bv-lists/bvxor-list" :dir :system)
(include-book "kestrel/bv-lists/bv-arrayp" :dir :system)
;(include-book "kestrel/bv-lists/nth2" :dir :system) ; todo: drop?
;(include-book "kestrel/bv-lists/list-patterns" :dir :system) ; for getbit-is-always-0 and getbit-is-always-1
(include-book "kestrel/lists-light/every-nth" :dir :system)
(include-book "kestrel/lists-light/add-to-end" :dir :system)
(include-book "kestrel/lists-light/group-def" :dir :system) ;drop?
(include-book "kestrel/lists-light/group2" :dir :system) ;drop?
(include-book "kestrel/lists-light/first-non-member" :dir :system)
(include-book "kestrel/lists-light/all-same" :dir :system)
(include-book "kestrel/lists-light/repeat-tail" :dir :system)
(include-book "kestrel/lists-light/update-subrange" :dir :system)
(include-book "kestrel/lists-light/update-subrange2" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/alists-light/pairlis-dollar-fast" :dir :system)
(include-book "kestrel/arrays-2d/arrays-2d" :dir :system) ;for array-elem-2d
(include-book "kestrel/maps/maps" :dir :system) ;for key-list, todo: brings in too much, like osets
(include-book "make-evaluator")
(include-book "unguarded-primitives")
(include-book "unguarded-built-ins")
(include-book "unguarded-defuns")
(include-book "supporting-functions")
(include-book "interpreted-function-alists") ; for make-interpreted-function-alist
(include-book "print-constant") ; drop from the evaluator?
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

;; Restricts ALIST to just the given KEYS.
(defund get-entries-eq (keys alist)
  (declare (xargs :guard (and (symbol-listp keys)
                              (symbol-alistp alist))))
  (if (endp keys)
      nil
    (let* ((key (car keys))
           (entry (assoc-eq key alist)))
      (cons entry
            (get-entries-eq (cdr keys) alist)))))

;; ;; only for lists, not strings
;; (defund reverse-fast (x)
;;   (declare (xargs :guard (true-listp x)))
;;   (revappend x nil))

;; (defund equal-lst-exec (val lst acc)
;;   (declare (xargs :guard (true-listp acc)))
;;   (if (atom lst)
;;       (reverse-fast acc)
;;     (equal-lst-exec val (cdr lst) (cons (equal val (car lst)) acc))))

;; ;without the max call this loops when n=0
;; (defund take-every-nth-aux (n lst acc)
;;   (declare (xargs :guard (and (true-listp lst)
;;                               (true-listp acc))))
;;    (if (endp lst)
;;        (reverse-fast acc) ;BOZO or is the built in reverse faster
;;      (take-every-nth-aux n (nthcdr (max 1 (nfix n)) lst) (cons (car lst) acc))))

;; (defund take-every-nth (n lst)
;;   (declare (xargs :guard (true-listp lst)))
;;   (take-every-nth-aux n lst nil))

;; (defund bvplus-lst (size val lst)
;;   (declare (type (integer 0 *) size))
;;   (if (atom lst)
;;       nil
;;     (cons (bvplus size val (car lst))
;;           (bvplus-lst size val (cdr lst)))))

;; ;reverses the order - not any more, that caused problems
;; (defund keep-items-less-than (bound lst acc)
;;   (declare (xargs :guard (true-listp acc)))
;;   (if (atom lst)
;;       (reverse-fast acc)
;;     (if (< (rfix (car lst)) (rfix bound))
;;         (keep-items-less-than bound (cdr lst) (cons (car lst) acc))
;;       (keep-items-less-than bound (cdr lst) acc))))

;; (defund keep-items-less-than-unguarded (bound lst acc)
;;   (declare (xargs :guard t))
;;   (keep-items-less-than bound lst (true-list-fix acc)))

;; (defthm keep-items-less-than-unguarded-correct
;;   (equal (keep-items-less-than-unguarded bound lst acc)
;;          (keep-items-less-than bound lst acc))
;;   :hints (("Goal" :in-theory (enable keep-items-less-than-unguarded
;;                                      keep-items-less-than
;;                                      REVERSE-FAST))))

;; (defund all-items-less-than (bound lst)
;;   (declare (xargs :guard t))
;;   (if (atom lst)
;;       t
;;     (and (< (rfix (car lst)) (rfix bound))
;;          (all-items-less-than bound (cdr lst)))))

;; (defun lookup-lst-equal (key-lst alist)
;;   (declare (xargs :guard (and (alistp alist)
;; ;                              (true-listp key-lst) ;bozo consider putting this back?
;;                               )
;;                   :guard-hints (("Goal" :in-theory (disable car-becomes-nth-of-0)))))
;;   (if (consp key-lst)
;;       (cons (lookup-equal (car key-lst) alist)
;;             (lookup-lst-equal (cdr key-lst) alist))
;;     nil))

;now using a scheme involving repeat-tail
;; (defun repeat-unguarded (n v)
;;   (declare (xargs :guard t))
;;   (repeat (nfix n) v))

;; (defthm repeat-unguarded-correct
;;   (equal (repeat-unguarded n v)
;;          (repeat n v)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund items-have-len-unguarded (n lst)
  (declare (xargs :guard t))
  (if (atom lst)
      t
    (and (equal n (len (car lst))) ;faster to walk down the list and decrement n simultaneously?
         (items-have-len-unguarded n (cdr lst)))))

(defthm items-have-len-unguarded-correct
  (equal (items-have-len-unguarded n lst)
         (items-have-len n lst))
  :hints (("Goal" :in-theory (enable items-have-len-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund strip-cars-unguarded (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        (t (cons (car-unguarded (car-unguarded x))
                 (strip-cars-unguarded (cdr-unguarded x))))))

(defthm strip-cars-unguarded-correct
  (equal (strip-cars-unguarded x)
         (strip-cars x))
  :hints (("Goal" :in-theory (enable strip-cars-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund strip-cdrs-unguarded (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        (t (cons (cdr-unguarded (car-unguarded x))
                 (strip-cdrs-unguarded (cdr-unguarded x))))))

(defthm strip-cdrs-unguarded-correct
  (equal (strip-cdrs-unguarded x)
         (strip-cdrs x))
  :hints (("Goal" :in-theory (enable strip-cdrs-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvnot-list-unguarded (size lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (cons (bvnot-unguarded size (car lst))
          (bvnot-list-unguarded size (cdr lst)))))

(defthm bvnot-list-unguarded-correct
  (equal (bvnot-list-unguarded size lst)
         (bvnot-list           size lst))
  :hints (("Goal" :in-theory (enable bvnot-list-unguarded bvnot-list BVNOT-UNGUARDED-CORRECT))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvxor-list-unguarded (size x y)
  (DECLARE (xargs :guard t))
  (if (atom x)
      nil
    (cons (bvxor-unguarded size (car x) (if (consp y) (car y) 0))
          (bvxor-list-unguarded size (cdr x) (if (consp y) (cdr y) nil)))))

(defthm bvxor-list-unguarded-correct
  (equal (bvxor-list-unguarded size x y)
         (bvxor-list size x y))
  :hints (("Goal" :in-theory (enable bvxor-list bvxor-list-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund set::in-unguarded (a x)
  (declare (xargs :guard t))
  (if (set::setp x)
      (set::in a x)
    nil))

(defthm set::in-unguarded-correct
  (equal (set::in-unguarded a x)
         (set::in a x))
  :hints (("Goal" :in-theory (enable set::in-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;TODO finish removing all guards!
(defund unpackbv-less-guarded (num size bv)
  (declare (type (integer 0 *) size)
           (type (integer 0 *) num))
  (unpackbv num size (ifix bv)))

(defthm unpackbv-less-guarded-correct
  (equal (unpackbv-less-guarded size x y)
         (unpackbv size x y))
:hints (("Goal" :in-theory (enable unpackbv unpackbv-less-guarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund no-duplicatesp-equal-unguarded (l)
  (declare (xargs :guard t))
  (cond ((atom l) t)
        ((member-equal-unguarded (car l) (cdr l)) nil)
        (t (no-duplicatesp-equal-unguarded (cdr l)))))

(defthm no-duplicatesp-equal-unguarded-correct
  (equal (no-duplicatesp-equal-unguarded l)
         (no-duplicatesp-equal l))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal-unguarded
                                     no-duplicatesp-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund map-reverse-list-unguarded (items)
  (declare (xargs :guard t))
  (if (atom items)
      nil
    (cons (reverse-list-unguarded (car items))
          (map-reverse-list-unguarded (cdr items)))))

(defthm map-reverse-list-unguarded-correct
  (equal (map-reverse-list-unguarded l)
         (map-reverse-list l))
  :hints (("Goal" :in-theory (enable map-reverse-list-unguarded
                                     map-reverse-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund intersection-equal-unguarded (l1 l2)
  (declare (xargs :guard t))
  (cond ((atom l1) nil)
        ((member-equal-unguarded (car l1) l2)
         (cons (car l1)
               (intersection-equal-unguarded (cdr l1) l2)))
        (t (intersection-equal-unguarded (cdr l1) l2))))

(defthm intersection-equal-unguarded-correct
  (equal (intersection-equal-unguarded l1 l2)
         (intersection-equal l1 l2))
  :hints (("Goal" :in-theory (enable intersection-equal-unguarded
                                     intersection-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund first-non-member-unguarded (items items-to-exclude)
  (declare (xargs :guard t))
  (if (atom items)
      nil
    (if (not (member-equal-unguarded (car items) items-to-exclude))
        (car items)
      (first-non-member-unguarded (cdr items) items-to-exclude))))

(defthm first-non-member-correct
  (equal (first-non-member-unguarded items items-to-exclude)
         (first-non-member items items-to-exclude))
  :hints (("Goal" :in-theory (enable first-non-member-unguarded
                                     first-non-member))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun update-nth-unguarded (key val l)
  (declare (xargs :guard t))
  (COND ((not (posp key)) (CONS VAL (CDR-unguarded L)))
        (T (CONS (CAR-unguarded L)
                 (UPDATE-NTH-unguarded (1- KEY) VAL (CDR-unguarded L))))))

(defthm update-nth-unguarded-correct
  (equal (update-nth-unguarded key val l)
         (update-nth key val l))
  :hints (("Goal" :in-theory (enable update-nth-unguarded
                                     update-nth))))

;; This justifies evaluating calls to EQL below by calling EQUAL.
(local
 (defthm eql-becomes-equal
   (equal (eql x y)
          (equal x y))))

;; This justifies evaluating calls to = below by calling EQUAL.
(local
 (defthm =-becomes-equal
   (equal (= x y)
          (equal x y))))

;; (defund getbit-is-always-0-unguarded (n items)
;;   (declare (xargs :guard t))
;;   (if (atom items)
;;       t
;;       (and (equal 0 (getbit (nfix n) (ifix (car items))))
;;            (getbit-is-always-0-unguarded n (cdr items)))))

;; (defthm getbit-is-always-0-unguarded-correct
;;   (equal (getbit-is-always-0-unguarded n items)
;;          (getbit-is-always-0 n items))
;;   :hints (("Goal" :in-theory (enable getbit-is-always-0-unguarded getbit-is-always-0))))

;; (defund getbit-is-always-1-unguarded (n items)
;;   (declare (xargs :guard t))
;;   (if (atom items)
;;       t
;;       (and (equal 1 (getbit (nfix n) (ifix (car items))))
;;            (getbit-is-always-1-unguarded n (cdr items)))))

;; (defthm getbit-is-always-1-unguarded-correct
;;   (equal (getbit-is-always-1-unguarded n items)
;;          (getbit-is-always-1 n items))
;;   :hints (("Goal" :in-theory (enable getbit-is-always-1-unguarded getbit-is-always-1))))


    ;; TODO: Consider having different evaluators for rewriting and for evaluating test cases when sweeping and merging
;we might like different orderings for doing proofs (syntax functions first) and evaluating test cases (bv functions first)
;is this same evaluator used for both?
;or use getprops (in which case the order won't matter)

;pairs each arity with an alist from fns to the terms to put in for them - fixme is the term ever more than a fn applied to arg1 arg2 ... ?
;todo: consider inlining some of the -unguarded functions for speed?
;fixme add a test that all of these are functions, not macros
;todo: adapt the simpler format of stuff like this that we use in evaluator-simple.  also generate check THMS like the ones that it generates
(defund axe-evaluator-function-info ()
  (declare (xargs :guard t))
  (acons 1
         ;fixme it would be nice to allow a single symbol in each spot of this list:
         '((quotep quotep arg1) ;unguarded ;fixme is this still used?
           (natp natp arg1)     ;unguarded
           (posp posp arg1)     ;unguarded
           (integerp integerp arg1)               ;unguarded, primitive
           (rationalp rationalp arg1)             ;unguarded, primitive
           (print-constant print-constant arg1)   ;unguarded
           (not not arg1)                         ;unguarded
           (power-of-2p power-of-2p arg1)         ;unguarded
           (lg lg-unguarded arg1)                 ;see lg-unguarded-correct
           (bool-to-bit bool-to-bit arg1)         ;unguarded
           (char-code char-code-unguarded arg1) ;see char-code-unguarded-correct
           (code-char code-char-unguarded arg1) ;see code-char-unguarded-correct
           (symbol-package-name symbol-package-name-unguarded arg1) ;see symbol-package-name-unguarded-correct
           (symbol-name symbol-name-unguarded arg1) ;see symbol-name-unguarded-correct
           (all-same all-same arg1)               ;unguarded
           (bool-fix$inline bool-fix$inline arg1) ;unguarded
           (booleanp booleanp arg1) ;unguarded
;;           (contiguousp contiguousp arg1)
           ;(bit-listp bit-listp arg1) ;unguarded
           ;; (bitnot-list bitnot-list arg1)
           (LIST::|2SET| LIST::|2SET| arg1)
;           (new-ad new-ad arg1)
           (rkeys rkeys arg1)
           (key-list key-list arg1)
           (true-list-fix true-list-fix arg1) ;unguarded
           (all-integerp all-integerp arg1) ;unguarded
           (no-duplicatesp-equal no-duplicatesp-equal-unguarded arg1) ; see no-duplicatesp-equal-unguarded-correct
           (strip-cdrs strip-cdrs-unguarded arg1) ;see strip-cdrs-unguarded-correct
           (strip-cars strip-cars-unguarded arg1) ;see strip-cars-unguarded-correct
           (stringp stringp arg1)       ;unguarded, primitive
           (true-listp true-listp arg1) ;unguarded
           (consp consp arg1)           ;unguarded, primitive
           (bytes-to-bits bytes-to-bits arg1) ;drop since we rewrite it? but that bytes-to-bits-rewrite seems gross
           (width-of-widest-int width-of-widest-int-unguarded arg1) ; see width-of-widest-int-unguarded-correct
           (all-natp all-natp arg1) ;unguarded
           (endp endp-unguarded arg1) ;see endp-unguarded-correct
           ;(int-fix-list int-fix-list arg1) ;unguarded
           (bitnot bitnot-unguarded arg1)   ;see bitnot-unguarded-correct
           (logmaskp logmaskp arg1)         ;drop? ; unguarded
           (integer-length integer-length-unguarded arg1) ;see INTEGER-LENGTH-UNGUARDED-CORRECT
           (ceiling-of-lg ceiling-of-lg-unguarded arg1) ; see ceiling-of-lg-unguarded-correct
           (unary-/ unary-/-unguarded arg1) ;see unary-/-unguarded-correct
           (nfix nfix arg1)                 ;unguarded
           (ifix ifix arg1)                 ;unguarded
           (len len arg1)                   ;unguarded
           (reverse-list reverse-list-unguarded arg1) ; see reverse-list-unguarded-correct
           (acl2-numberp acl2-numberp arg1) ;(primitive)
           (zp zp-unguarded arg1)           ;see zp-unguarded-correct
           (unary-- unary---unguarded arg1) ;see unary---unguarded-correct
           (atom atom arg1)                 ;unguarded
           (car car-unguarded arg1)         ; see car-unguarded-correct
           (cdr cdr-unguarded arg1)         ; see cdr-unguarded-correct
           ;; (EXTRACT-PACKAGE-NAME EXTRACT-PACKAGE-NAME arg1)
           (map-reverse-list map-reverse-list-unguarded arg1)
           (realpart realpart-unguarded arg1) ; see realpart-unguarded-correct
           (imagpart imagpart-unguarded arg1) ; see imagpart-unguarded-correct
           (symbolp symbolp arg1) ;unguarded
           (characterp characterp arg1) ;unguarded
           (complex-rationalp complex-rationalp arg1) ;unguarded
           (denominator denominator-unguarded arg1) ; see denominator-unguarded-correct
           (numerator numerator-unguarded arg1) ;see numerator-unguarded-correct
           )
         (acons 2
                '((mv-nth mv-nth-unguarded arg1 arg2)
                  (items-have-len items-have-len-unguarded arg1 arg2) ;see items-have-len-unguarded-correct
                  (all-all-unsigned-byte-p all-all-unsigned-byte-p arg1 arg2) ;unguarded
                  (add-to-end add-to-end arg1 arg2)
                  (coerce coerce-unguarded arg1 arg2) ;see coerce-unguarded-correct
                  (< <-unguarded arg1 arg2) ;see <-unguarded-correct
                  (equal equal arg1 arg2)   ;primitive, unguarded
                  (eql equal arg1 arg2)   ;to evaluate eql, just call equal (primitive, unguarded)
                  (= equal arg1 arg2)   ;to evaluate =, just call equal (primitive, unguarded)
                  (list-equiv list-equiv arg1 arg2) ;unguarded
                  (prefixp prefixp arg1 arg2) ;unguarded
                  (lookup-equal lookup-equal-unguarded arg1 arg2) ;or open to assoc-equal?
                  ;(lookup arg1 arg2) ;whoa! this is missing an argument - this is an error!
                  (lookup lookup arg1 arg2) ;or go to lookup-equal?
                  (bvnot bvnot-unguarded arg1 arg2) ;see bvnot-unguarded-correct
                  (bvuminus bvuminus-unguarded arg1 arg2) ;see bvuminus-unguarded-correct
                  (assoc-equal assoc-equal-unguarded arg1 arg2) ;see assoc-equal-unguarded-correct
                  (unsigned-byte-p-forced unsigned-byte-p-forced arg1 arg2) ;unguarded

                  (trim trim-unguarded arg1 arg2) ;see trim-unguarded-correct
                  (binary-+ binary-+-unguarded arg1 arg2) ;see binary-+-unguarded-correct

                  ;; (all-items-less-than all-items-less-than arg1 arg2)
                  (every-nth every-nth-unguarded arg1 arg2)
                  (intersection-equal intersection-equal-unguarded arg1 arg2)
;                  (push-bvchop-list push-bvchop-list arg1 arg2) ;do we need this?
                  (all-equal$ all-equal$-unguarded arg1 arg2)
                  (repeatbit repeatbit-unguarded arg1 arg2)
;                  (print-dag-expr print-dag-expr arg1 arg2)
                  ;; (binary-and binary-and arg1 arg2) ;unguarded
                  (implies implies arg1 arg2)       ;unguarded
                  (first-non-member first-non-member-unguarded arg1 arg2)
                  (booland booland arg1 arg2) ;unguarded
                  (boolor boolor arg1 arg2)   ;unguarded
                  (getbit-list getbit-list-unguarded arg1 arg2) ; see getbit-list-unguarded-correct
                  (set::union set::union arg1 arg2)
                  (leftrotate32 leftrotate32-unguarded arg1 arg2)
;                  (list::val list::val arg1 arg2) ;new Tue Jul 17 16:49:17 2012
;                  (n-new-ads2 n-new-ads2 arg1 arg2)
                  (set::insert set::insert arg1 arg2)
;                  (nth-new-ad nth-new-ad arg1 arg2)
                  (floor floor-unguarded arg1 arg2)
;                  (logext-list logext-list arg1 arg2)
;                  (list::memberp list::memberp arg1 arg2)
                  (member-equal member-equal-unguarded arg1 arg2)
;                  (member-eq member-eq arg1 arg2)
                  (g g arg1 arg2) ;unguarded
;                  (repeat repeat-unguarded arg1 arg2) ;see repeat-unguarded-correct ; can blow up!
                  (nthcdr nthcdr-unguarded arg1 arg2) ;see nthcdr-unguarded-correct
                  (take take-unguarded arg1 arg2) ;see take-unguarded-correct
                  (firstn firstn-unguarded arg1 arg2) ;see firstn-unguarded-correct
                  (binary-append binary-append-unguarded arg1 arg2) ;see binary-append-unguarded-correct
                  ;; (getbit-is-always-0 getbit-is-always-0-unguarded arg1 arg2) ;see getbit-is-always-0-unguarded-correct
                  ;; (getbit-is-always-1 getbit-is-always-1-unguarded arg1 arg2) ;see getbit-is-always-1-unguarded-correct
                  (signed-byte-p signed-byte-p arg1 arg2)     ;unguarded
                  (unsigned-byte-p unsigned-byte-p arg1 arg2) ;unguarded

                  (bvchop-list bvchop-list-unguarded arg1 arg2) ;see bvchop-list-unguarded-correct
                  (all-unsigned-byte-p all-unsigned-byte-p arg1 arg2) ;unguarded
                  (all-signed-byte-p all-signed-byte-p arg1 arg2) ;unguarded ; drop?
                  (bitor bitor-unguarded arg1 arg2) ;see bitor-unguarded-correct
                  (bitand bitand-unguarded arg1 arg2) ;see bitand-unguarded-correct
                  (bitxor bitxor-unguarded arg1 arg2) ;see bitxor-unguarded-correct
                  (expt expt-unguarded arg1 arg2) ;see expt-unguarded-correct
                  (min min-unguarded arg1 arg2) ;see min-unguarded-correct
                  (max max-unguarded arg1 arg2) ;see max-unguarded-correct
                  (mod mod-unguarded arg1 arg2)
                  (getbit getbit-unguarded arg1 arg2) ;see getbit-unguarded-correct
                  (cons cons arg1 arg2)               ;unguarded (primitive)
                  (bvchop bvchop-unguarded arg1 arg2) ;see bvchop-unguarded-correct
                  (logtail$inline logtail$inline-unguarded arg1 arg2) ;see logtail$inline-unguarded-correct
                  (logext logext-unguarded arg1 arg2) ;see logext-unguarded-correct
                  (nth nth-unguarded arg1 arg2) ;see nth-unguarded-correct
                  (binary-* binary-*-unguarded arg1 arg2) ;see binary-*-unguarded-correct
                  (bvnot-list bvnot-list-unguarded arg1 arg2) ;see bvnot-list-unguarded-correct
                  (eq equal arg1 arg2) ;eq is logically the same as equal
                  (ceiling ceiling-unguarded arg1 arg2)
                  (lookup-eq lookup-eq arg1 arg2) ;drop? call lookup-equal-unguarded
                  (lookup lookup arg1 arg2) ;drop? call lookup-equal-unguarded
                  (group group arg1 arg2)
                  (group2 group2 arg1 arg2)
                  (set::in set::in-unguarded arg1 arg2)
                  (symbol< symbol<-unguarded arg1 arg2))
                (acons 3
                       '((repeat-tail repeat-tail arg1 arg2 arg3) ;; can this blow up?
                         (negated-elems-listp negated-elems-listp-unguarded arg1 arg2 arg3)
                         (leftrotate leftrotate-unguarded arg1 arg2 arg3)
                         (acons acons-unguarded arg1 arg2 arg3)
                         ;; (map-slice map-slice arg1 arg2 arg3)
                         ;; (myif-nest-needs-bvchop-list myif-nest-needs-bvchop-list arg1 arg2 arg3)
                         ;; (EQUAL-LST-EXEC EQUAL-LST-EXEC arg1 arg2 arg3) ;Mon Mar  8 04:03:38 2010
                         (bvshr bvshr-unguarded arg1 arg2 arg3) ;see bvshr-unguarded-correct
                         (bvashr bvashr-unguarded arg1 arg2 arg3) ;see bvashr-unguarded-correct
                         ;; (bitxor-terms-should-be-reordered arg1 arg2 arg3)

                         (packbv packbv-unguarded arg1 arg2 arg3)
                         (unpackbv unpackbv-less-guarded arg1 arg2 arg3)
                         ;; (map-packbv map-packbv arg1 arg2 arg3)

                         ;many of these call bvchop, whose guard should be improved..
                         ;; (bvplus-lst bvplus-lst arg1 arg2 arg3)
                         (bvequal    bvequal-unguarded arg1 arg2 arg3)  ;see   bvequal-unguarded-correct
                         (bvlt      bvlt-unguarded arg1 arg2 arg3)  ;see    bvlt-unguarded-correct
                         (bvle      bvle-unguarded arg1 arg2 arg3)  ;see    bvle-unguarded-correct
                         (bvxor    bvxor-unguarded arg1 arg2 arg3)  ;see   bvxor-unguarded-correct
                         (bvor      bvor-unguarded arg1 arg2 arg3)  ;see    bvor-unguarded-correct
                         (bvand    bvand-unguarded arg1 arg2 arg3)  ;see   bvand-unguarded-correct
                         (bvmult  bvmult-unguarded arg1 arg2 arg3)  ;see  bvmult-unguarded-correct
                         (bvplus  bvplus-unguarded arg1 arg2 arg3)  ;see  bvplus-unguarded-correct
                         (bvminus bvminus-unguarded arg1 arg2 arg3) ;see bvminus-unguarded-correct

                         (bvmod bvmod-unguarded arg1 arg2 arg3) ;see bvmod-unguarded-correct
                         (bvdiv bvdiv-unguarded arg1 arg2 arg3) ;see bvdiv-unguarded-correct

                         (bvsx bvsx-unguarded arg1 arg2 arg3)
                         (sbvdiv sbvdiv-unguarded arg1 arg2 arg3)
                         (sbvdivdown sbvdivdown arg1 arg2 arg3)
                         (sbvrem sbvrem arg1 arg2 arg3)
                         (sbvmoddown sbvmoddown arg1 arg2 arg3)
                         (sbvlt sbvlt-unguarded arg1 (ifix arg2) (ifix arg3)) ;probably okay - may not be needed if guards for the defining functions were better
                         (sbvle sbvle-unguarded arg1 arg2 arg3)
                         (s s arg1 arg2 arg3) ;unguarded
;;                         (nth2 nth2 arg1 arg2 arg3)
                         (myif myif arg1 arg2 arg3)     ;unguarded
                         (boolif boolif arg1 arg2 arg3) ;unguarded
                         (array-elem-2d array-elem-2d arg1 arg2 arg3) ;drop?
                         (bv-arrayp bv-arrayp arg1 arg2 arg3)
                         (update-nth update-nth-unguarded arg1 arg2 arg3)
                         (if if arg1 arg2 arg3) ;unguarded
                         (slice slice-unguarded arg1 arg2 arg3)
                         (bvshl bvshl-unguarded arg1 arg2 arg3)
                         ;; (keep-items-less-than keep-items-less-than-unguarded arg1 arg2 arg3) ;see keep-items-less-than-unguarded-correct
                         (subrange subrange-unguarded arg1 arg2 arg3) ; see subrange-unguarded-correct
                         (bvxor-list bvxor-list-unguarded arg1 arg2 arg3))
                       (acons 4
                              '((update-subrange update-subrange arg1 arg2 arg3 arg4) ;new
                                ;(bv-array-write-nest-with-val-at-indexp-axe bv-array-write-nest-with-val-at-indexp-axe arg1 arg2 arg3 arg4)
                                (update-nth2 update-nth2 arg1 arg2 arg3 arg4)
                                (bv-array-clear bv-array-clear arg1 arg2 arg3 arg4)
                                (bvcat bvcat-unguarded arg1 arg2 arg3 arg4)
                                ;; (bvnth bvnth arg1 arg2 (nfix arg3) arg4)
                                (bv-array-read bv-array-read-unguarded arg1 arg2 arg3 arg4)
                                (bvif bvif-unguarded arg1 arg2 arg3 arg4))
                              (acons 5 '((update-subrange2 update-subrange2 arg1 arg2 arg3 arg4 arg5) ;new
                                         (bv-array-write bv-array-write-unguarded (nfix arg1) (nfix arg2) (nfix arg3) arg4 arg5) ; see bv-array-write-unguarded-correct
                                         (bv-array-clear-range bv-array-clear-range arg1 arg2 arg3 arg4 arg5)
                                         )
                                     nil))))))

;was a function, but it seemed to get recomputed each time!
;FFIXME maybe this should include the dag-val function, eval-dag function, etc.
(defconst *axe-evaluator-functions*
  (strip-cars-list (strip-cdrs (axe-evaluator-function-info))))


;think this stuff through
(make-evaluator axe-evaluator
                (axe-evaluator-function-info)
;                 :error    ;throw an error if we are given an unknown function
;                nil       ;don't quote result
                )

;ffffixme could lead to crashes?
(skip-proofs
(verify-guards apply-axe-evaluator
  :hints (("Goal" :in-theory (e/d (TRUE-LIST-FIX
                                   true-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
                                   symbol-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp)
                                  (INTERPRETED-FUNCTION-ALISTP ;todo
                                   ))
           :do-not '(generalize eliminate-destructors)
           ))))

(skip-proofs (verify-guards apply-axe-evaluator-to-quoted-args))

(make-event (add-tracing-to-evaluator 'axe-evaluator))

;fffixme could lead to crashes?
(skip-proofs (verify-guards apply-axe-evaluator-with-tracing))

;; ;;BBOZO, yikes i think the guards might sometimes fail to be satisfied, since we sometimes evaluate both branches of an if...
;; ;so the skip-proofs can lead to bad things...

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; ;hiding the bvplus should cause it to get sucked into the dag
;; (defthm hide-bvplus-constant-dag
;;   (implies (and (syntaxp (and (quotep k)
;;                               (quotep size)))
;;                 )
;;            (equal (BVPLUS size k (hide (DAG-VAL2-no-array dag alist)))
;;                   (hide (BVPLUS size k (hide (DAG-VAL2-NO-ARRAY dag alist))))))
;;   :hints (("Goal" :expand ((hide (BVPLUS size k (hide (DAG-VAL2-NO-ARRAY dag alist))))))))

;; ;hiding the bvplus should cause it to get sucked into the dag
;; (defthm hide-bvplus-dag-dag
;;   (implies (syntaxp (quotep size))
;;            (equal (BVPLUS size
;;                           (hide (DAG-VAL2-NO-ARRAY dag alist))
;;                           (hide (DAG-VAL2-NO-ARRAY dag2 alist2)))
;;                   (hide (BVPLUS size
;;                                 (hide (DAG-VAL2-NO-ARRAY dag alist))
;;                                 (hide (DAG-VAL2-NO-ARRAY dag2 alist2))))))
;;   :hints (("Goal" :expand ((hide (BVPLUS size
;;                                 (hide (DAG-VAL2-NO-ARRAY dag alist))
;;                                 (hide (DAG-VAL2-NO-ARRAY dag2 alist2))))))))

;; ;BOZO lots more like this!
;; (defthm integerp-hide-dag-val-bvplus
;;   (implies (equal (second (car dag)) 'bvplus)
;;            (integerp (hide (dag-val2-no-array dag alist))))
;;   :hints (("Goal" :in-theory (enable eval-fn eval-fn-ternary dag-val2-no-array
;;                                      )
;;            :expand ((hide (dag-val2-no-array dag alist))
;;                     (eval-dag2-no-array dag alist)))))

;; (local
;;  (defthm equal-of-true-list-fix-and-list-of-car
;;    (equal (equal (true-list-fix l)
;;                  (list (car l)))
;;           (equal 1 (len l)))
;;    :hints (("Goal" :in-theory (enable true-list-fix)))))

;(in-theory (disable LIST::LEN-EQUAL-1-REWRITE)) ;yuck

;; (local
;;  (defthm consp-of-lookup-equal-when-items-have-len-of-strip-cdrs
;;    (implies (and (items-have-len n (strip-cdrs l))
;;                  (lookup-equal key l)
;;                  (posp n))
;;             (consp (lookup-equal key l)))
;;    :hints (("Goal" :in-theory (enable lookup-equal
;;                                       ITEMS-HAVE-LEN
;;                                       assoc-equal)))))

;todo: generalize this (it has *axe-evaluator-functions* baked in)
;include the fns themselves if they are not base fns
;fixme do we need the ones called in nested dag-val calls?
;todo: compare to get-non-built-in-supporting-fns-list
(defund supporting-non-base-fns (count fns interpreted-function-alist throw-errorp acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp acc)
                              (interpreted-function-alistp interpreted-function-alist))
                  :measure (nfix (+ 1 count))
                  :guard-hints (("Goal" :in-theory (e/d (lookup-equal interpreted-function-alistp)
                                                        (interpreted-function-infop-of-lookup-equal-when-interpreted-function-alistp
                                                         member-equal ; for speed
                                                         ))
                                 :use (:instance interpreted-function-infop-of-lookup-equal-when-interpreted-function-alistp (fn (car fns)))
                                 ))))
  (if (not (natp count))
      (er hard? 'supporting-non-base-fns "count reached.")
    (if (endp fns)
        acc
      (let* ((fn (first fns)))
        (if (or (member-eq fn acc)
                (eq 'dag-val-with-axe-evaluator fn) ;what about eval-dag-with-axe-evaluator?
                (member-eq fn *axe-evaluator-functions*))
            (supporting-non-base-fns (+ -1 count) (cdr fns) interpreted-function-alist throw-errorp acc)
          (let* ((entry (if throw-errorp
                            (lookup-eq-safe fn interpreted-function-alist)
                          (lookup-eq fn interpreted-function-alist))))
            (if (not entry) ;fixme print a warning -or get rid of this case and always throw the error (once the decompiler passed in ifns for all jvm functions)
                (supporting-non-base-fns (+ -1 count)
                                         (cdr fns)
                                         interpreted-function-alist
                                         throw-errorp
                                         acc ;(cons fn acc)
                                         )
              (let* ((body (second entry))
                     (called-fns (get-fns-in-term body)))
                (supporting-non-base-fns (+ -1 count)
                                         (append called-fns (cdr fns))
                                         interpreted-function-alist
                                         throw-errorp
                                         (cons fn acc))))))))))

;fixme can we omit ones mentioned only in nested calls to dag-val (since they will be given values in those calls)?
(defund supporting-interpreted-function-alist (fns interpreted-function-alist throw-errorp)
  (let ((supporting-non-base-fns (supporting-non-base-fns 1000000000 fns interpreted-function-alist throw-errorp nil)))
    (get-entries-eq supporting-non-base-fns interpreted-function-alist)))

;fixme use this more?
;; interpreted-function-alist must give meaning to all non-built-in functions in DAG.
(defund wrap-dag-in-dag-val (dag interpreted-function-alist)
  (if (quotep dag)
      dag
    (let* ((dag-vars (dag-vars dag))
           (dag-fns (dag-fns dag)))
      `(dag-val-with-axe-evaluator ',dag
                                   ,(make-acons-nest dag-vars)
                                   ',(supporting-interpreted-function-alist dag-fns interpreted-function-alist
                                                                            nil ;fixme change this to t, or change the code to always throw an error
                                                                            )
                                   '0))))

;; Create a term equivalent to DAG, where the meaning of any non-built-in
;; functions that support DAG comes from WRLD.
;fixme use this more?
(defund embed-dag-in-term (dag wrld)
  (declare (xargs :guard (and (or (quotep dag)
                                  (weak-dagp dag))
                              (plist-worldp wrld))))
  (if (quotep dag)
      dag
    (let ((dag-vars (dag-vars dag))
          (dag-fns (dag-fns dag)))
      (if (not (function-symbolsp dag-fns wrld))
          (er hard? 'embed-dag-in-term "Some functions are not in the world: ~X01." dag-fns nil)
        (let* ((supporting-fns (get-non-built-in-supporting-fns-list dag-fns
                                                                     *axe-evaluator-functions* ;(append *acl2-primitives* *axe-evaluator-functions*) ;stops when it hits one of these..
                                                                     wrld))
               (supporting-interpreted-function-alist (make-interpreted-function-alist supporting-fns wrld)))
          `(dag-val-with-axe-evaluator ',dag
                                       ,(make-acons-nest dag-vars)
                                       ',supporting-interpreted-function-alist
                                       '0))))))
