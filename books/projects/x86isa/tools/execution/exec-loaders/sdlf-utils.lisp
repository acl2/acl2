;; ORIGINAL AUTHORS:
;; Shilpi Goel         <shigoel@cs.utexas.edu>
;; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>

;; ======================================================================

(in-package "X86ISA")

(include-book "../x86-init-page-tables" :ttags
              (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "std/lists/nthcdr" :dir :system))

(local (include-book "std/lists/take" :dir :system))

;; ======================================================================

;; Some helper functions:

(defun take-till-zero (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (endp bytes)
      nil
    (if (equal (car bytes) 0)
        nil
      (cons (car bytes) (take-till-zero (cdr bytes))))))

(defthm byte-listp-take-till-zero
  (implies (force (byte-listp bytes))
           (byte-listp (take-till-zero bytes)))
  :rule-classes :type-prescription)

(in-theory (disable take-till-zero))

(defun firstn (n elements)
  (declare (xargs :guard (natp n)))
  (if (or (atom elements) (zp n))
      nil
    (cons (car elements)
          (firstn (1- n) (cdr elements)))))

(defthm byte-listp-firstn
  (implies (byte-listp x)
           (byte-listp (firstn n x)))
  :rule-classes :type-prescription)

(defthm len-firstn-equal-to-n
  (implies (and (byte-listp x)
                (natp n)
                (< n (len x)))
           (equal (len (firstn n x))
                  n)))

(defthm len-firstn-equal-to-len-x
  (implies (and (byte-listp x)
                (natp n)
                (<= (len x) n))
           (equal (len (firstn n x))
                  (len x))))

(in-theory (disable firstn))

(defthm byte-listp-nthcdr
  (implies (byte-listp x)
           (byte-listp (nthcdr n x)))
  :rule-classes :type-prescription)

(defthm byte-listp-take
  (implies (and (byte-listp bytes)
                (natp n)
                (< n (len bytes)))
           (byte-listp (take n bytes)))
  :rule-classes :type-prescription)

(defun-inline rnbni (n bytes)
  ;; Read n bytes as a number and increment file.
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (b* ((num  (combine-bytes (firstn n bytes)))
       (rest (nthcdr n bytes)))
      (mv num rest)))

(defthm natp-mv-nth-0-rnbni
  (implies (byte-listp bytes)
           (natp (mv-nth 0 (rnbni n bytes))))
  :rule-classes :type-prescription)

(defthm mv-nth-0-rnbni-linear-1
  (implies (and (byte-listp bytes)
                (natp n)
                (< n (len bytes)))
           (< (mv-nth 0 (rnbni n bytes)) (expt 2 (ash n 3))))
  :hints (("Goal" :in-theory (e/d ()
                                  (
                                   len-firstn-equal-to-n
                                   len-firstn-equal-to-len-x))
           :use ((:instance len-firstn-equal-to-n
                            (x bytes)
                            (n n)))))
  :rule-classes :linear)

(defthm mv-nth-0-rnbni-linear-2
  (implies (and (byte-listp bytes)
                (natp n)
                (<= (len bytes) n))
           (< (mv-nth 0 (rnbni n bytes)) (expt 2 (ash (len bytes) 3))))
  :hints (("Goal" :in-theory (e/d ()
                                  (len-firstn-equal-to-n
                                   len-firstn-equal-to-len-x))
           :use ((:instance len-firstn-equal-to-len-x
                            (x bytes)
                            (n n)))))
  :rule-classes :linear)

(defthm byte-listp-mv-nth-1-rnbni
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 1 (rnbni n bytes))))
  :rule-classes :type-prescription)

(defthm len-mv-nth-1-rnbni-1
  (implies (and (byte-listp bytes)
                (natp n)
                (<= n (len bytes)))
           (equal (len (mv-nth 1 (rnbni n bytes)))
                  (- (len bytes) n))))

(defthm len-mv-nth-1-rnbni-2
  (implies (and (byte-listp bytes)
                (natp n)
                (< (len bytes) n))
           (equal (len (mv-nth 1 (rnbni n bytes)))
                  0)))

(in-theory (disable rnbni))

(defun-inline rnbbi (n bytes)
  ;; Read n bytes and increment file.
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (b* ((first (firstn n bytes))
       (rest  (nthcdr n bytes)))
      (mv first rest)))

(defthm byte-listp-mv-nth-0-rnbbi
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 0 (rnbbi n bytes))))
  :rule-classes :type-prescription)

(defthm len-mv-nth-0-rnbbi-1
  (implies (and (byte-listp bytes)
                (natp n)
                (< n (len bytes)))
           (equal (len (mv-nth 0 (rnbbi n bytes)))
                  n)))

(defthm len-mv-nth-0-rnbbi-2
  (implies (and (byte-listp bytes)
                (natp n)
                (<= (len bytes) n))
           (equal (len (mv-nth 0 (rnbbi n bytes)))
                  (len bytes))))

(defthm byte-listp-mv-nth-1-rnbbi
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 1 (rnbbi n bytes))))
  :rule-classes :type-prescription)

(defthm len-mv-nth-1-rnbbi-1
  (implies (and (byte-listp bytes)
                (natp n)
                (<= n (len bytes)))
           (equal (len (mv-nth 1 (rnbbi n bytes)))
                  (- (len bytes) n))))

(defthm len-mv-nth-1-rnbbi-2
  (implies (and (byte-listp bytes)
                (natp n)
                (< (len bytes) n))
           (equal (len (mv-nth 1 (rnbbi n bytes)))
                  0)))

(in-theory (disable rnbbi))

;; ==================================================================-
