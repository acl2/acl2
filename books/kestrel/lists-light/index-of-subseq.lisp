; Finding a sequence within another sequence
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prefixp-def")
(local (include-book "prefixp"))

;; Returns the index (0-based) of the first occurrence of SEQ1 within SEQ2, or
;; nil if SEQ1 does not occur within SEQ2.  TODO: Could be made more efficient.
(defund index-of-subseq (seq1 seq2)
  (declare (xargs :guard (and (true-listp seq1)
                              (consp seq1)
                              (true-listp seq2))))
  (if (endp seq2)
      nil ; seq1 cannot occur, since seq1 is non-empty
    (if (prefixp seq1 seq2)
        0 ; seq1 is within seq2 at position 0
      (let ((res (index-of-subseq seq1 (rest seq2))))
        (and res
             (+ 1 res))))))

(defthm take-of-len-and-nthcdr-of-index-of-subseq
  (implies (index-of-subseq seq1 seq2) ; seq1 does occur
           (equal (take (len seq1) (nthcdr (index-of-subseq seq1 seq2) seq2))
                  (true-list-fix seq1)))
  :hints (("Goal" :in-theory (enable index-of-subseq
                                     take-of-len-when-prefixp))))

(defthm index-of-subseq-self
  (implies (consp seq)
           (equal (index-of-subseq seq seq)
                  0))
  :hints (("Goal" :in-theory (enable index-of-subseq))))

(defthm <-of-index-of-subseq-and-len
  (implies (index-of-subseq seq1 seq2)
           (< (index-of-subseq seq1 seq2) (len seq2)))
  :hints (("Goal" :in-theory (enable index-of-subseq))))

(defthm not-index-of-subseq-when-of-len-and-len
  (implies (< (len seq2) (len seq1))
           (not (index-of-subseq seq1 seq2)))
  :hints (("Goal" :in-theory (enable index-of-subseq))))
