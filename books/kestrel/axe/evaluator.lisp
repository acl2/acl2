; The main (old-style) Axe evaluator
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

;clean this up!

;todo: reduce the amount of input that needs to be given to make the evaluator, also check that unguarded replacements are correct

;FIXME axe-evaluator-function-info does not include all of the ACL2 primitive functions.  should it?

;; TODO: To evaluate a function defined using MBE, we might prefer to evaluate the :exec part.

;try to include less (but we need the functions to eval them)
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
(include-book "make-evaluator")
(include-book "unguarded-primitives")
(include-book "unguarded-built-ins")
(include-book "unguarded-defuns")
(include-book "kestrel/utilities/world" :dir :system) ;for fn-definedp
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/lists-light/add-to-end" :dir :system)
(include-book "kestrel/lists-light/group" :dir :system) ;drop?
(include-book "kestrel/lists-light/group2" :dir :system) ;drop?
(include-book "kestrel/lists-light/ungroup" :dir :system) ;drop?
(include-book "kestrel/lists-light/first-non-member" :dir :system)
(include-book "kestrel/bv/defs" :dir :system) ;reduce?
(include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/width-of-widest-int" :dir :system)
(include-book "kestrel/bv-lists/bv-arrays" :dir :system) ; for bv-array-clear, etc
(include-book "kestrel/bv-lists/map-packbv" :dir :system) ;for map-packbv, map-reverse-list, etc.
(include-book "kestrel/bv-lists/bytes-to-bits" :dir :system)
(include-book "kestrel/bv-lists/all-signed-byte-p" :dir :system)
(include-book "kestrel/bv-lists/getbit-list" :dir :system)
(include-book "kestrel/bv-lists/map-slice" :dir :system)
(include-book "kestrel/lists-light/all-same" :dir :system)
(include-book "kestrel/lists-light/repeat-tail" :dir :system)
(include-book "kestrel/lists-light/update-subrange" :dir :system)
(include-book "kestrel/lists-light/update-subrange2" :dir :system)
(include-book "kestrel/bv-lists/bvxor-list" :dir :system)
(include-book "kestrel/arrays-2d/arrays-2d" :dir :system) ;for array-elem-2d
(include-book "kestrel/bv-lists/list-patterns" :dir :system) ;why?
(include-book "safe-unquote")
(include-book "interpreted-function-alists") ; for make-interpreted-function-alist
(include-book "print-constant") ; drop?
(include-book "kestrel/maps/maps" :dir :system) ;for key-list
(include-book "kestrel/utilities/terms" :dir :system) ;for GET-FNS-IN-TERM
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

;;;
;;; lg-unguarded
;;;

(defund lg-unguarded (x)
  (declare (xargs :guard t))
  (lg (ifix x)))

;supports the correctness of the evaluator
(defthm lg-unguarded-correct
  (equal (lg-unguarded x)
         (lg x))
  :hints (("Goal" :in-theory (enable lg lg-unguarded integer-length))))

(defund bitnot-unguarded (x)
  (declare (xargs :guard t))
  (bitnot (ifix x)))

(defthm bitnot-unguarded-correct
  (equal (bitnot-unguarded x)
         (bitnot x))
  :hints (("Goal" :in-theory (enable bitnot-unguarded getbit-when-val-is-not-an-integer))))

(defund bitor-unguarded (x y)
  (declare (xargs :guard t))
  (bitor (ifix x) (ifix y)))

(defthm bitor-unguarded-correct
  (equal (bitor-unguarded x y)
         (bitor x y))
  :hints (("Goal" :in-theory (enable bitor-unguarded bitor bvor getbit-when-val-is-not-an-integer))))

(defund bitxor-unguarded (x y)
  (declare (xargs :guard t))
  (bitxor (ifix x) (ifix y)))

(defthm bitxor-unguarded-correct
  (equal (bitxor-unguarded x y)
         (bitxor x y))
  :hints (("Goal" :in-theory (e/d (bitxor-unguarded bitxor getbit-when-val-is-not-an-integer) (bvxor-1-becomes-bitxor)))))

(defund bitand-unguarded (x y)
  (declare (xargs :guard t))
  (bitand (ifix x) (ifix y)))

(defthm bitand-unguarded-correct
  (equal (bitand-unguarded x y)
         (bitand x y))
  :hints (("Goal" :in-theory (e/d (bitand-unguarded bitand bvand getbit-when-val-is-not-an-integer) ()))))

(defund logtail-unguarded (size i)
  (declare (xargs :guard t))
  (logtail (nfix size) (ifix i)))

(defthm logtail-unguarded-correct
  (equal (logtail-unguarded size i)
         (logtail size i))
  :hints (("Goal" :in-theory (enable logtail-unguarded))))

(defund getbit-unguarded (n x)
  (declare (xargs :guard t))
  (getbit (nfix n) (ifix x)))

(defthm getbit-unguarded-correct
  (equal (getbit-unguarded n x)
         (getbit n x))
  :hints (("Goal" :in-theory (e/d (getbit-unguarded getbit bitand getbit-when-val-is-not-an-integer slice) (BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defund bvnot-unguarded (size i)
  (declare (xargs :guard t))
  (bvnot (nfix size) (ifix i)))

(defthm bvnot-unguarded-correct
  (equal (bvnot-unguarded size i)
         (bvnot size i))
  :hints (("Goal" :in-theory (enable bvnot-unguarded bvnot))))

(defund bvuminus-unguarded (size i)
  (declare (xargs :guard t))
  (bvuminus (nfix size) i))

(defthm bvuminus-unguarded-correct
  (equal (bvuminus-unguarded size i)
         (bvuminus size i))
  :hints (("Goal" :in-theory (e/d (bvuminus-unguarded bvuminus bvminus) ()))))



;; Restricts ALIST to just the given KEYS.
(defun get-entries-eq (keys alist)
  (declare (xargs :guard (and (symbol-listp keys)
                              (symbol-alistp alist))))
  (if (endp keys)
      nil
    (let* ((key (car keys))
           (entry (assoc-eq key alist)))
      (cons entry
            (get-entries-eq (cdr keys) alist)))))
;fixme move
(defthm booleanp-of-in
  (booleanp (set::in a x)))

(defun reverse-fast (x)
  (declare (xargs :guard (true-listp x)))
  (revappend x nil))

(defun equal-lst-exec (val lst acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom lst)
      (reverse-fast acc)
    (equal-lst-exec val (cdr lst) (cons (equal val (car lst)) acc))))

;without the max call this loops when n=0
(defun take-every-nth-aux (n lst acc)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp acc))))
   (if (endp lst)
       (reverse-fast acc) ;BOZO or is the built in reverse faster
     (take-every-nth-aux n (nthcdr (max 1 (nfix n)) lst) (cons (car lst) acc))))

(defun take-every-nth (n lst)
  (declare (xargs :guard (true-listp lst)))
  (take-every-nth-aux n lst nil))

(defun bvplus-lst (size val lst)
  (declare (type (integer 0 *) size))
  (if (atom lst)
      nil
    (cons (bvplus size val (car lst))
          (bvplus-lst size val (cdr lst)))))

;reverses the order - not any more, that caused problems
(defun keep-items-less-than (bound lst acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom lst)
      (reverse-fast acc)
    (if (< (rfix (car lst)) (rfix bound))
        (keep-items-less-than bound (cdr lst) (cons (car lst) acc))
      (keep-items-less-than bound (cdr lst) acc))))

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

(defund keep-items-less-than-unguarded (bound lst acc)
  (declare (xargs :guard t))
  (keep-items-less-than bound lst (true-list-fix acc)))

(defthm keep-items-less-than-unguarded-correct
  (equal (keep-items-less-than-unguarded bound lst acc)
         (keep-items-less-than bound lst acc))
  :hints (("Goal" :in-theory (enable keep-items-less-than-unguarded))))

(defun all-items-less-than (bound lst)
  (declare (xargs :guard t))
  (if (atom lst)
      t
    (and (< (rfix (car lst)) (rfix bound))
         (all-items-less-than bound (cdr lst)))))

;; matches std
(defthm consp-of-assoc-equal
  (implies (alistp alist)
           (iff (consp (assoc-equal key alist))
                (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable alistp assoc-equal))))

;; (defun lookup-lst-equal (key-lst alist)
;;   (declare (xargs :guard (and (alistp alist)
;; ;                              (true-listp key-lst) ;bozo consider putting this back?
;;                               )
;;                   :guard-hints (("Goal" :in-theory (disable car-becomes-nth-of-0)))))
;;   (if (consp key-lst)
;;       (cons (lookup-equal (car key-lst) alist)
;;             (lookup-lst-equal (cdr key-lst) alist))
;;     nil))

;drop?
(defthmd alistp-consp-hack-equal
  (implies (and (alistp x)
                (assoc-equal v x))
           (consp (assoc-equal v x)))
  :hints (("Goal" :in-theory (enable alistp assoc-equal))))

;now using a scheme involving repeat-tail
;; (defun repeat-unguarded (n v)
;;   (declare (xargs :guard t))
;;   (repeat (nfix n) v))

;; (defthm repeat-unguarded-correct
;;   (equal (repeat-unguarded n v)
;;          (repeat n v)))

(defund realpart-unguarded (x)
  (declare (xargs :guard t))
  (if (acl2-numberp x)
      (realpart x)
    0))

(defthm realpart-unguarded-correct
  (equal (realpart-unguarded x)
         (realpart x))
  :hints (("Goal" :in-theory (enable realpart-unguarded realpart))))

(defund imagpart-unguarded (x)
  (declare (xargs :guard t))
  (if (acl2-numberp x)
      (imagpart x)
    0))

(defthm imagpart-unguarded-correct
  (equal (imagpart-unguarded x)
         (imagpart x))
  :hints (("Goal" :in-theory (enable imagpart-unguarded imagpart))))

(defund strip-cars-unguarded (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        (t (cons (car-unguarded (car-unguarded x))
                 (strip-cars-unguarded (cdr-unguarded x))))))

(defthm strip-cars-unguarded-correct
  (equal (strip-cars-unguarded x)
         (strip-cars x))
  :hints (("Goal" :in-theory (enable strip-cars-unguarded))))

(defund strip-cdrs-unguarded (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        (t (cons (cdr-unguarded (car-unguarded x))
                 (strip-cdrs-unguarded (cdr-unguarded x))))))

(defthm strip-cdrs-unguarded-correct
  (equal (strip-cdrs-unguarded x)
         (strip-cdrs x))
  :hints (("Goal" :in-theory (enable strip-cdrs-unguarded))))

(defund slice-less-guarded (topbit bottombit val)
  (declare (xargs :guard (and (natp topbit)
                              (natp bottombit))))
  (bvchop (nfix (+ 1 topbit (- bottombit))) ;prevents the first arg to bvchop from being negative
           (logtail (nfix bottombit) (ifix val))))

(defthm slice-less-guarded-correct
  (implies (and (natp high)
                (natp low))
           (equal (slice-less-guarded high low x)
                  (slice high low x)))
  :hints (("Goal" :in-theory (e/d (slice slice-less-guarded) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defund bvchop-list-unguarded (size lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (cons (bvchop-unguarded size (car lst))
          (bvchop-list-unguarded size (cdr lst)))))

(defthm bvchop-list-unguarded-correct
  (equal (bvchop-list-unguarded size lst)
         (bvchop-list           size lst))
  :hints (("Goal" :in-theory (enable bvchop-list-unguarded bvchop-list))))

(defund bvnot-list-unguarded (size lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (cons (bvnot-unguarded size (car lst))
          (bvnot-list-unguarded size (cdr lst)))))

(in-theory (disable bvnot-unguarded))

(defthm bvnot-list-unguarded-correct
  (equal (bvnot-list-unguarded size lst)
         (bvnot-list           size lst))
  :hints (("Goal" :in-theory (enable bvnot-list-unguarded bvnot-list BVNOT-UNGUARDED-CORRECT))))

(defund bvlt-unguarded (size x y)
  (declare (xargs :guard t))
  (bvlt (nfix size) (ifix x) (ifix y)))

(defthm bvlt-unguarded-correct
  (equal (bvlt-unguarded size x y)
         (bvlt size x y))
  :hints (("Goal" :in-theory (enable bvlt-unguarded bvlt))))

(defund bvle-unguarded (size x y)
  (declare (xargs :guard t))
  (bvle (nfix size) (ifix x) (ifix y)))

(defthm bvle-unguarded-correct
  (equal (bvle-unguarded size x y)
         (bvle size x y))
  :hints (("Goal" :in-theory (enable bvle bvle-unguarded bvlt))))

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


(defund bvor-unguarded (size x y)
  (declare (xargs :guard t))
  (bvor (nfix size) (ifix x) (ifix y)))

(defthm bvor-unguarded-correct
  (equal (bvor-unguarded size x y)
         (bvor size x y))
  :hints (("Goal" :in-theory (enable bvor bvor-unguarded))))

(defund bvand-unguarded (size x y)
  (declare (xargs :guard t))
  (bvand (nfix size) (ifix x) (ifix y)))

(defthm bvand-unguarded-correct
  (equal (bvand-unguarded size x y)
         (bvand size x y))
  :hints (("Goal" :in-theory (enable bvand bvand-unguarded))))

(defund bvmult-unguarded (size x y)
  (declare (xargs :guard t))
  (bvmult (nfix size) (ifix x) (ifix y)))

(defthm bvmult-unguarded-correct
  (equal (bvmult-unguarded size x y)
         (bvmult size x y))
  :hints (("Goal" :in-theory (enable bvmult bvmult-unguarded))))

(defund bvminus-unguarded (size x y)
  (declare (xargs :guard t))
  (bvminus (nfix size) (ifix x) (ifix y)))

(defthm bvminus-unguarded-correct
  (equal (bvminus-unguarded size x y)
         (bvminus size x y))
  :hints (("Goal" :in-theory (enable bvminus bvminus-unguarded))))

(defund bvmod-unguarded (size x y)
  (declare (xargs :guard t))
  (if (not (posp size))
      0
    (if (equal 0 (bvchop size (ifix y)))
        (bvchop size (ifix x))
      (bvmod size (ifix x) (ifix y)))))

(defthm bvmod-unguarded-correct
  (equal (bvmod-unguarded size x y)
         (bvmod size x y))
:hints (("Goal" :in-theory (enable bvmod bvmod-unguarded))))

(defund bvdiv-unguarded (size x y)
  (declare (xargs :guard t))
  (if (not (posp size))
      0
    (if (equal 0 (bvchop size (ifix y)))
        0
      (bvdiv size (ifix x) (ifix y)))))

(defthm bvdiv-unguarded-correct
  (equal (bvdiv-unguarded size x y)
         (bvdiv size x y))
:hints (("Goal" :in-theory (enable bvdiv bvdiv-unguarded))))

;TODO finish removing all guards!
(defund unpackbv-less-guarded (num size bv)
  (declare (type (integer 0 *) size)
           (type (integer 0 *) num))
  (unpackbv num size (ifix bv)))

(defthm unpackbv-less-guarded-correct
  (equal (unpackbv-less-guarded size x y)
         (unpackbv size x y))
:hints (("Goal" :in-theory (enable unpackbv unpackbv-less-guarded))))


;TODO Get these to work...
;; (defund bvsx-unguarded (new-size old-size val)
;;   (declare (xargs :guard t))
;;   (if (and (posp old-size)
;;            (<= (ifix old-size) (+ 1 (ifix new-size))))
;;       (bvsx (ifix new-size) (ifix old-size) (ifix val))
;;     0))

;; (defthm bvsx-unguarded-correct
;;   (equal (bvsx-unguarded new-size old-size val)
;;          (bvsx new-size old-size val))
;;   :hints (("Goal" :in-theory (enable bvsx bvsx-unguarded))))


;; (defund sbvlt-unguarded (size x y)
;;   (declare (xargs :guard t))
;;   (sbvlt (nfix size) (ifix x) (ifix y)))

;; (defthm sbvlt-unguarded-correct
;;   (equal (sbvlt-unguarded size x y)
;;          (sbvlt size x y))
;;   :hints (("Goal" :in-theory (enable sbvlt sbvlt-unguarded))))

(defund char-code-unguarded (x)
  (declare (xargs :guard t))
  (if (characterp x)
      (char-code x)
    0))

(defthm char-code-unguarded-correct
  (equal (char-code-unguarded x)
         (char-code x))
  :hints (("Goal" :in-theory (enable char-code-unguarded))))

(defund code-char-unguarded (x)
  (declare (xargs :guard t))
  (if (and (integerp x)
           (<= 0 x)
           (< x 256))
      (code-char x)
    (code-char 0)))

(defthm code-char-unguarded-correct
  (equal (code-char-unguarded x)
         (code-char x))
  :hints (("Goal" :in-theory (enable code-char-unguarded)
           :use ((:instance completion-of-code-char)))))

(defund coerce-unguarded (x y)
  (declare (xargs :guard t))
  (cond ((equal y 'list)
         (if (stringp x)
             (coerce x 'list)
           nil))
        (t (coerce (make-character-list x) 'string))))

(defthm coerce-unguarded-correct
  (equal (coerce-unguarded x y)
         (coerce x y))
  :hints (("Goal" :in-theory (enable coerce-unguarded)
           :use (:instance completion-of-coerce))))

(defund symbol-package-name-unguarded (x)
  (declare (xargs :guard t))
  (if (symbolp x)
      (symbol-package-name x)
    ""))

;why was this suddenly necessary?
(defthm symbol-package-name-unguarded-correct
  (equal (symbol-package-name-unguarded x)
         (symbol-package-name x))
  :hints (("Goal" :in-theory (enable symbol-package-name-unguarded))))

(defund symbol-name-unguarded (x)
  (declare (xargs :guard t))
  (if (symbolp x)
      (symbol-name x)
    ""))

;why was this suddenly necessary?
(defthm symbol-name-unguarded-correct
  (equal (symbol-name-unguarded x)
         (symbol-name x))
  :hints (("Goal" :in-theory (enable symbol-name-unguarded))))

(defund set::in-unguarded (a x)
  (declare (xargs :guard t))
  (if (set::setp x)
      (set::in a x)
    nil))

(defthm set::in-unguarded-correct
  (equal (set::in-unguarded a x)
         (set::in a x))
  :hints (("Goal" :in-theory (enable set::in-unguarded))))

(defund bvcat-unguarded (highsize highval lowsize lowval)
  (declare (xargs :guard t))
  (logapp (nfix lowsize)
          (ifix lowval) (bvchop (nfix highsize) (ifix highval))))

(defthm bvcat-unguarded-correct
  (equal (bvcat-unguarded highsize highval lowsize lowval)
         (bvcat highsize highval lowsize lowval))
  :hints (("Goal" :in-theory (e/d (bvcat bvcat-unguarded) ()))))

(defund bvif-unguarded (size test thenpart elsepart)
  (declare (xargs :guard t))
  (if test (bvchop-unguarded size thenpart)
      (bvchop-unguarded size elsepart)))

(defthm bvif-unguarded-correct
  (equal (bvif-unguarded highsize highval lowsize lowval)
         (bvif           highsize highval lowsize lowval))
  :hints (("Goal" :in-theory (enable bvif bvif-unguarded))))

;; This justifies evaluating calls to EQL below by calling EQUAL.
(local
 (defthm eql-becomes-eql
   (equal (eql x y)
          (equal x y))))

(defund negated-elems-listp-unguarded (width lst1 lst2)
  (declare (xargs :guard t))
  (negated-elems-listp (nfix width) lst1 lst2))

(defthm negated-elems-listp-unguarded-correct
  (equal (negated-elems-listp-unguarded width lst1 lst2)
         (negated-elems-listp width lst1 lst2))
  :hints (("Goal" :in-theory (enable negated-elems-listp-unguarded))))

(defund firstn-unguarded (n lst)
  (declare (xargs :guard t))
  (if (true-listp lst)
      (firstn (nfix n) lst)
    (firstn (nfix n) (true-list-fix lst))))

(defthm firstn-unguarded-correct
  (equal (firstn-unguarded n lst)
         (firstn n lst))
  :hints (("Goal" :in-theory (enable firstn-unguarded))))

(defund getbit-is-always-0-unguarded (n items)
  (declare (xargs :guard t))
  (if (atom items)
      t
      (and (equal 0 (getbit (nfix n) (ifix (car items))))
           (getbit-is-always-0-unguarded n (cdr items)))))

(defthm getbit-is-always-0-unguarded-correct
  (equal (getbit-is-always-0-unguarded n items)
         (getbit-is-always-0 n items))
  :hints (("Goal" :in-theory (enable getbit-is-always-0-unguarded getbit-is-always-0))))

(defund getbit-is-always-1-unguarded (n items)
  (declare (xargs :guard t))
  (if (atom items)
      t
      (and (equal 1 (getbit (nfix n) (ifix (car items))))
           (getbit-is-always-1-unguarded n (cdr items)))))

(defthm getbit-is-always-1-unguarded-correct
  (equal (getbit-is-always-1-unguarded n items)
         (getbit-is-always-1 n items))
  :hints (("Goal" :in-theory (enable getbit-is-always-1-unguarded getbit-is-always-1))))


    ;; TODO: Consider having different evaluators for rewriting and for evaluating test cases when sweeping and merging
;we might like different orderings for doing proofs (syntax functions first) and evaluating test cases (bv functions first)
;is this same evaluator used for both?
;or use getprops (in which case the order won't matter)

;pairs each arity with an alist from fns to the terms to put in for them - fixme is the term ever more than a fn applied to arg1 arg2 ... ?
;consider inlining some of the -unguarded functions for speed?
;fixme add a test that all of these are functions, not macros
;todo: get rid of set-field, set-fields, and get-field
;todo: see adapt the simpler format of stuff like this that we use in evaluator-simple.  also generate check THMS like the ones that it generates
;; TODO: The functions actually get checked in the reverse order of how they appear here -- change that
(defun axe-evaluator-function-info ()
  (declare (xargs :guard t))
  (acons 1
         ;fixme it would be nice to allow a single symbol in each spot of this list:
         '((quotep quotep arg1) ;unguarded ;fixme is this still used?
           (natp natp arg1)     ;unguarded
           (posp posp arg1)     ;unguarded
           (integerp integerp arg1)               ;(primitive)
           (rationalp rationalp arg1)             ;(primitive)
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
           (no-duplicatesp-equal no-duplicatesp-equal arg1)
           (strip-cdrs strip-cdrs-unguarded arg1) ;see strip-cdrs-unguarded-correct
           (strip-cars strip-cars-unguarded arg1) ;see strip-cars-unguarded-correct
           (stringp stringp arg1)       ;unguarded, primitive
           (true-listp true-listp arg1) ;unguarded
           (consp consp arg1)           ;unguarded, primitive
           (bytes-to-bits bytes-to-bits arg1) ;fixme drop since we rewrite it?
           (width-of-widest-int width-of-widest-int arg1)
           (all-natp all-natp arg1) ;unguarded
           (endp endp-unguarded arg1) ;see endp-unguarded-correct
           ;(int-fix-list int-fix-list arg1) ;unguarded
           (bitnot bitnot-unguarded arg1)   ;see bitnot-unguarded-correct
           (logmaskp logmaskp arg1)         ;drop?
           (integer-length integer-length-unguarded arg1) ;see INTEGER-LENGTH-UNGUARDED-CORRECT
           (ceiling-of-lg ceiling-of-lg arg1)
           (unary-/ unary-/-unguarded arg1) ;see unary-/-unguarded-correct
           (nfix nfix arg1)                 ;unguarded
           (ifix ifix arg1)                 ;unguarded
           (len len arg1)                   ;unguarded
           (reverse-list reverse-list-unguarded arg1)
           (acl2-numberp acl2-numberp arg1) ;(primitive)
           (zp zp-unguarded arg1)           ;see zp-unguarded-correct
           (unary-- unary---unguarded arg1) ;see unary---unguarded-correct
           (atom atom arg1)                 ;unguarded
           (car car-unguarded arg1)         ; see car-unguarded-correct
           (cdr cdr-unguarded arg1)         ; see cdr-unguarded-correct
           ;; (EXTRACT-PACKAGE-NAME EXTRACT-PACKAGE-NAME arg1)
           (map-reverse-list map-reverse-list arg1)
           (realpart realpart-unguarded arg1)
           (imagpart imagpart-unguarded arg1)
           (symbolp symbolp arg1) ;guard of t
           (characterp characterp arg1) ;guard of t
           (complex-rationalp complex-rationalp arg1) ;guard of t
           )
         (acons 2
                '((mv-nth mv-nth-unguarded arg1 arg2)
                  (items-have-len items-have-len-unguarded arg1 arg2) ;see items-have-len-unguarded-correct
                  (all-all-unsigned-byte-p all-all-unsigned-byte-p arg1 arg2)
                  (add-to-end add-to-end arg1 arg2)
                  (coerce coerce-unguarded arg1 arg2) ;see coerce-unguarded-correct
                  (< <-unguarded arg1 arg2) ;see <-unguarded-correct
                  (equal equal arg1 arg2)   ;primitive
                  (eql equal arg1 arg2)   ;to evaluate eql, just call equal (primitive)
                  (list-equiv list-equiv arg1 arg2) ;unguarded
                  (prefixp prefixp arg1 arg2) ;unguarded
                  (lookup-equal lookup-equal arg1 arg2) ;or open to assoc-equal?
                  ;(lookup arg1 arg2) ;whoa! this is missing an argument - this is an error!
                  (lookup lookup arg1 arg2) ;or go to lookup-equal?
                  (bvnot bvnot-unguarded arg1 arg2) ;see bvnot-unguarded-correct
                  (bvuminus bvuminus-unguarded arg1 arg2) ;see bvuminus-unguarded-correct
                  (assoc-equal assoc-equal-unguarded arg1 arg2) ;see assoc-equal-unguarded-correct
                  (unsigned-byte-p-forced unsigned-byte-p-forced arg1 arg2) ;unguarded

                  (trim trim-unguarded arg1 arg2) ;see trim-unguarded-correct
                  (binary-+ binary-+-unguarded arg1 arg2) ;see binary-+-unguarded-correct

                  (all-items-less-than all-items-less-than arg1 arg2)
                  (take-every-nth take-every-nth arg1 arg2)
                  (intersection-equal intersection-equal arg1 arg2)
;                  (push-bvchop-list push-bvchop-list arg1 arg2) ;do we need this?
                  (all-equal$ all-equal$ arg1 arg2) ;unguarded
                  (repeatbit repeatbit arg1 arg2)
;                  (print-dag-expr print-dag-expr arg1 arg2)
                  ;; (binary-and binary-and arg1 arg2) ;unguarded
                  (implies implies arg1 arg2)       ;unguarded
                  (first-non-member first-non-member arg1 arg2)
                  (booland booland arg1 arg2) ;unguarded
                  (boolor boolor arg1 arg2)   ;unguarded
                  (getbit-list getbit-list arg1 arg2)
                  (set::union set::union arg1 arg2)
                  (leftrotate32 leftrotate32-unguarded arg1 arg2)
;                  (list::val list::val arg1 arg2) ;new Tue Jul 17 16:49:17 2012
;                  (n-new-ads2 n-new-ads2 arg1 arg2)
                  (set::insert set::insert arg1 arg2)
;                  (nth-new-ad nth-new-ad arg1 arg2)
                  (floor floor arg1 arg2)
;                  (logext-list logext-list arg1 arg2)
;                  (list::memberp list::memberp arg1 arg2)
                  (member-equal member-equal arg1 arg2)
;                  (member-eq member-eq arg1 arg2)
                  (g g arg1 arg2) ;unguarded
;                  (repeat repeat-unguarded arg1 arg2) ;see repeat-unguarded-correct ; can blow up!
                  (nthcdr nthcdr-unguarded arg1 arg2) ;see nthcdr-unguarded-correct
                  (take take-unguarded arg1 arg2) ;see take-unguarded-correct
                  (firstn firstn-unguarded arg1 arg2) ;see firstn-unguarded-correct
                  (binary-append binary-append-unguarded arg1 arg2) ;see binary-append-unguarded-correct
                  (getbit-is-always-0 getbit-is-always-0-unguarded arg1 arg2) ;see getbit-is-always-0-unguarded-correct
                  (getbit-is-always-1 getbit-is-always-1-unguarded arg1 arg2) ;see getbit-is-always-1-unguarded-correct
                  (signed-byte-p signed-byte-p arg1 arg2)     ;unguarded
                  (unsigned-byte-p unsigned-byte-p arg1 arg2) ;unguarded

                  (bvchop-list bvchop-list-unguarded arg1 arg2) ;see bvchop-list-unguarded-correct
                  (all-unsigned-byte-p all-unsigned-byte-p arg1 arg2) ;unguarded
                  (all-signed-byte-p all-signed-byte-p arg1 arg2) ;unguarded
                  (bitor bitor-unguarded arg1 arg2) ;see bitor-unguarded-correct
                  (bitand bitand-unguarded arg1 arg2) ;see bitand-unguarded-correct
                  (bitxor bitxor-unguarded arg1 arg2) ;see bitxor-unguarded-correct
                  (expt expt-unguarded arg1 arg2) ;see expt-unguarded-correct
                  (min min-unguarded arg1 arg2) ;see min-unguarded-correct
                  (max max-unguarded arg1 arg2) ;see max-unguarded-correct
                  (mod mod arg1 arg2)
                  (getbit getbit-unguarded arg1 arg2) ;see getbit-unguarded-correct
                  (cons cons arg1 arg2)               ;primitive
                  (bvchop bvchop-unguarded arg1 arg2) ;see bvchop-unguarded-correct
                  (logtail$inline logtail-unguarded arg1 arg2) ;see logtail-unguarded-correct
                  (logext logext arg1 (ifix arg2))
                  (nth nth-unguarded arg1 arg2) ;see nth-unguarded-correct
                  (binary-* binary-*-unguarded arg1 arg2) ;see binary-*-unguarded-correct
                  (bvnot-list bvnot-list-unguarded arg1 arg2) ;see bvnot-list-unguarded-correct
                  (eq equal arg1 arg2) ;eq is logically the same as equal
                  (ceiling ceiling-unguarded arg1 arg2)
                  (lookup-eq lookup-eq arg1 arg2)
                  (lookup lookup arg1 arg2)
                  (group group arg1 arg2)
                  (group2 group2 arg1 arg2)
                  (set::in set::in-unguarded arg1 arg2)
                  (symbol-< symbol-<-unguarded arg1 arg2))
                (acons 3
                       '((repeat-tail repeat-tail arg1 arg2 arg3) ;; can this blow up?
                         (negated-elems-listp negated-elems-listp-unguarded arg1 arg2 arg3)
                         (leftrotate leftrotate arg1 arg2 arg3)
                         (acons acons arg1 arg2 arg3)
;                         (map-slice map-slice arg1 arg2 arg3)
                         ;(myif-nest-needs-bvchop-list myif-nest-needs-bvchop-list arg1 arg2 arg3)
;                         (EQUAL-LST-EXEC EQUAL-LST-EXEC arg1 arg2 arg3) ;Mon Mar  8 04:03:38 2010
                         (bvshr bvshr arg1 arg2 arg3)
                         (bvashr bvashr arg1 arg2 arg3) ;new
;    (bitxor-terms-should-be-reordered arg1 arg2 arg3)

                         (packbv packbv arg1 arg2 arg3)
                         (unpackbv unpackbv-less-guarded arg1 arg2 arg3)
;                         (map-packbv map-packbv arg1 arg2 arg3)

                         ;many of these call bvchop, whose guard should be improved..
                         (bvplus-lst bvplus-lst arg1 arg2 arg3)

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


                         (bvsx bvsx arg1 arg2 arg3)
                         (sbvdiv sbvdiv arg1 arg2 arg3)
                         (sbvdivdown sbvdivdown arg1 arg2 arg3)
                         (sbvrem sbvrem arg1 arg2 arg3)
                         (sbvmoddown sbvmoddown arg1 arg2 arg3)
                         (sbvlt sbvlt arg1 (ifix arg2) (ifix arg3)) ;probably okay - may not be needed if guards for the defining functions were better
                         (sbvle sbvle arg1 arg2 arg3)
                         (s s arg1 arg2 arg3) ;unguarded
                         (nth2 nth2 arg1 arg2 arg3)
                         (myif myif arg1 arg2 arg3)     ;unguarded
                         (boolif boolif arg1 arg2 arg3) ;unguarded
                         (array-elem-2d array-elem-2d arg1 arg2 arg3) ;drop?
                         (update-nth update-nth arg1 arg2 arg3)
                         (if if arg1 arg2 arg3) ;primitive
                         (slice slice-less-guarded arg1 arg2 arg3)
                         (bvshl bvshl arg1 arg2 arg3)
                         (keep-items-less-than keep-items-less-than-unguarded arg1 arg2 arg3) ;see keep-items-less-than-unguarded-correct
                         (subrange subrange (nfix arg1) (nfix arg2) arg3)
                         (bvxor-list bvxor-list-unguarded arg1 arg2 arg3))
                       (acons 4
                              '((update-subrange update-subrange arg1 arg2 arg3 arg4) ;new
                                ;(bv-array-write-nest-with-val-at-index bv-array-write-nest-with-val-at-index arg1 arg2 arg3 arg4)
                                (update-nth2 update-nth2 arg1 arg2 arg3 arg4)
                                (bv-array-clear bv-array-clear arg1 arg2 arg3 arg4)
                                (bvcat bvcat-unguarded arg1 arg2 arg3 arg4)
                                (bvnth bvnth arg1 arg2 (nfix arg3) arg4)
                                (bv-array-read bv-array-read-unguarded arg1 arg2 arg3 arg4)
                                (bvif bvif-unguarded arg1 arg2 arg3 arg4))
                              (acons 5 '((update-subrange2 update-subrange2 arg1 arg2 arg3 arg4 arg5) ;new
                                         (bv-array-write bv-array-write-unguarded (nfix arg1) (nfix arg2) (nfix arg3) arg4 arg5)
                                         (bv-array-clear-range bv-array-clear-range arg1 arg2 arg3 arg4 arg5)
                                         )
                                     (acons 6 '()
                                           nil)))))))

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
  :otf-flg t
;  :guard-debug t
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

;; ;fixme is this the complete list?
;; ;fixme does this list exist somewhere else?
;; (defconst *acl2-primitives*
;;   '(;;these don't have guards:
;;     equal stringp characterp acl2-numberp integerp rationalp complex-rationalp consp symbolp if cons
;;           ;;these do have guards:
;;           binary-+ binary-* < unary-- unary-/ car cdr realpart imagpart complex numerator denominator char-code code-char symbol-package-name symbol-name coerce bad-atom<= pkg-witness pkg-imports intern-in-package-of-symbol))

(mutual-recursion
 ;; This is dag-aware
 (defun get-called-fns-aux (term acc)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-listp acc))
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       acc
     (let* ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           acc
         (if (consp fn) ;tests for lambda
             (get-called-fns-aux (third fn) (get-called-fns-aux-lst (fargs term) acc))
           (if (and (eq 'dag-val-with-axe-evaluator fn)
                    (quotep (third (fargs term))) ;think about this
                    (symbol-alistp (unquote (third (fargs term)))))
               ;check for consistent definitions!  ffixme
               (union-equal (strip-cars (safe-unquote (third (fargs term)))) acc)
             (get-called-fns-aux-lst (fargs term) (add-to-set-eq fn acc))))))))

 ;; This is dag-aware
 (defun get-called-fns-aux-lst (terms acc)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-listp acc))))
   (if (endp terms)
       acc
     (get-called-fns-aux (car terms) (get-called-fns-aux-lst (cdr terms) acc)))))

(make-flag get-called-fns-aux)

;todo: see GET-FNS-IN-TERM
(defthm-flag-get-called-fns-aux
  (defthm symbol-listp-of-get-called-fns-aux
    (implies (and (pseudo-termp term)
                  (symbol-listp acc))
             (symbol-listp (get-called-fns-aux term acc)))
    :flag get-called-fns-aux)
  (defthm symbol-listp-of-get-called-fns-aux-lst
    (implies (and (pseudo-term-listp terms)
                  (symbol-listp acc))
             (symbol-listp (get-called-fns-aux-lst terms acc)))
    :flag get-called-fns-aux-lst))

(verify-guards get-called-fns-aux :hints (("Goal" :expand ((pseudo-termp term)))))

(defun get-called-fns (term)
  (declare (xargs :guard (pseudo-termp term)))
  (get-called-fns-aux term nil))

;ffixme what about primitives and recursion and mutual recursion and constrained functions?
;TODO Would be nice to track the call chain so we can report it in the error message.
(defund get-immediate-supporting-fns (fn-name throw-errorp wrld)
  (declare (xargs :guard (and (symbolp fn-name)
                              (plist-worldp wrld))))
  (if (member-eq fn-name *acl2-primitives*)
      (hard-error 'get-immediate-supporting-fns "Trying to get the body of the ACL2 primitive ~x0.  Consider adding it to the base evaluator.  Or investigate why a function that calls this function (transitively) is suddenly appearing."
                  (acons #\0 fn-name nil))
    (if (not (fn-definedp fn-name wrld))
        ;; an undefined function has no supporters
        (prog2$ (cw "(Note: Undefined function ~x0 is present in DAG.)~%" fn-name)
                nil)
      (let* ((body (fn-body fn-name throw-errorp wrld)))
        (get-called-fns body)))))

(defthm symbol-listp-of-get-immediate-supporting-fns
  (symbol-listp (get-immediate-supporting-fns fn-name throw-errorp wrld))
  :hints (("Goal" :in-theory (enable get-immediate-supporting-fns))))

;this is a worklist algorithm
(defund get-all-supporting-fns-aux (count ;for termination
                                    fns   ;the worklist
                                    done-list
                                    throw-errorp acc wrld)
  (declare (xargs :guard (and (natp count)
                              (symbol-listp fns)
                              (symbol-listp done-list)
                              (plist-worldp wrld)
                              (symbol-listp acc))))
  (if (zp count)
      (er hard? 'get-all-supporting-fns-aux "limit reached.")
    (if (endp fns)
        acc
      (let* ((fn (first fns)))
        (if (or (member-eq fn done-list)
                (eq fn 'bad-atom<=) ;new: Perhaps this can never actually be executed (we could still add it to the evaluator...)
                )
            (get-all-supporting-fns-aux (+ -1 count) (rest fns) done-list throw-errorp acc wrld)
          (get-all-supporting-fns-aux (+ -1 count)
                                      (append (get-immediate-supporting-fns fn throw-errorp wrld) (rest fns))
                                      (cons fn done-list)
                                      throw-errorp
                                      (add-to-set-eq fn acc)
                                      wrld))))))

(defthm symbol-listp-of-get-all-supporting-fns-aux
  (implies (and (symbol-listp acc)
                (symbol-listp fn-names))
           (symbol-listp (get-all-supporting-fns-aux count fn-names fn-names-to-stop-at throw-errorp acc wrld)))
  :hints (("Goal" :in-theory (enable get-all-supporting-fns-aux))))

;; ;this includes the function itself
;; (defun get-all-supporting-fns (fn-name wrld)
;;   (get-all-supporting-fns-aux (list fn-name) nil nil wrld))

;; (defun get-non-built-in-supporting-fns (fn-name wrld)
;;   (set-difference-eq (get-all-supporting-fns fn-name wrld) *acl2-primitives*))

;; (defun get-all-supporting-fns-list (fn-names wrld)
;;   (get-all-supporting-fns-aux fn-names nil nil wrld))

;; ;ffixme this will suck in stuff below the bv/array fns - redo the above code to stop when it hits such a fn!
;; (defun get-non-built-in-supporting-fns-list (fn-names wrld)
;;   (set-difference-eq (get-all-supporting-fns-list fn-names wrld) *acl2-primitives*))

;will include fn-names themselves, if they are not built-ins.
;now throws an error if any of the fns are supported by acl2 primitives not in *axe-evaluator-functions*
;ffffixme what about embedded dags?!
;todo: exclude the evaluator functions themselves?
(defun get-non-built-in-supporting-fns-list (fn-names wrld)
  (declare (xargs :guard (and (symbol-listp fn-names)
                              (plist-worldp wrld))))
  (get-all-supporting-fns-aux 1000000000
                              fn-names
                              *axe-evaluator-functions* ;(append *acl2-primitives* *axe-evaluator-functions*) ;stops when it hits one of these..
                              t                           ;throw-errorp
                              nil ;empty-acc
                              wrld))

;; (defun get-non-built-in-supporting-fns-list-tolerant (fn-names wrld)
;;   (declare (xargs :stobjs state :verify-guards nil))
;;   (get-all-supporting-fns-aux fn-names
;;                               (append *acl2-primitives* *axe-evaluator-functions*) ;stops when it hits one of these..
;;                               nil ;throw-errorp
;;                               nil
;;                               wrld))

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

;todo: rename to sound less general (make-alist-for-quoted-vars?)
(defun make-acons-nest (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (if (endp vars)
      *nil*
    `(acons ',(car vars) ,(car vars)
            ,(make-acons-nest (cdr vars)))))

(defthm equal-of-true-list-fix-and-list-of-car
  (equal (equal (true-list-fix l)
                (list (car l)))
         (equal 1 (len l)))
  :hints (("Goal" :in-theory (enable true-list-fix))))

;(in-theory (disable LIST::LEN-EQUAL-1-REWRITE)) ;yuck

(defthm consp-of-lookup-equal-when-items-have-len-of-strip-cdrs
  (implies (and (items-have-len n (strip-cdrs l))
                (lookup-equal key l)
                (posp n))
           (consp (lookup-equal key l)))
  :hints (("Goal" :in-theory (enable lookup-equal
                                     ITEMS-HAVE-LEN
                                     assoc-equal))))

;todo: generalize this (it has *axe-evaluator-functions* baked in)
;include the fns themselves if they are not base fns
;fixme do we need the ones called in nested dag-val calls?
;todo: compare to get-non-built-in-supporting-fns-list
(defun supporting-non-base-fns (count fns interpreted-function-alist throw-errorp acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp acc)
                              (interpreted-function-alistp interpreted-function-alist))
                  :measure (nfix (+ 1 count))
                  :guard-hints (("Goal" :in-theory (e/d (lookup-equal interpreted-function-alistp)
                                                        (interpreted-function-infop-of-lookup-equal-when-interpreted-function-alistp))
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
(defun supporting-interpreted-function-alist (fns interpreted-function-alist throw-errorp)
  (let ((supporting-non-base-fns (supporting-non-base-fns 1000000000 fns interpreted-function-alist throw-errorp nil)))
    (get-entries-eq supporting-non-base-fns interpreted-function-alist)))

;fixme use this more?
;; interpreted-function-alist must give meaning to all non-built-in functions in DAG.
(defun wrap-dag-in-dag-val (dag interpreted-function-alist)
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
(defun embed-dag-in-term (dag wrld)
  (declare (xargs :guard (and (or (quotep dag)
                                  (weak-dagp dag))
                              (plist-worldp wrld))))
  (if (quotep dag)
      dag
    (let* ((dag-vars (dag-vars dag))
           (dag-fns (dag-fns dag))
           (supporting-fns (get-non-built-in-supporting-fns-list dag-fns wrld))
           (supporting-interpreted-function-alist (make-interpreted-function-alist supporting-fns wrld))
           )
      `(dag-val-with-axe-evaluator ',dag
                                   ,(make-acons-nest dag-vars)
                                   ',supporting-interpreted-function-alist
                                   '0))))
