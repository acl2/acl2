; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann, August, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun newline-before (s p n)
  (declare (type string s)
           (type (integer 0 *) p n)
           (xargs :guard (<= p (length s))))
  (cond ((zp p) 0)
        (t (let ((p-1 (1- p)))
             (cond ((eql (char s p-1) #\Newline)
                    (if (zp n)
                        p
                      (newline-before s p-1 (1- n))))
                   (t (newline-before s p-1 n)))))))

(defun newline-after (s p n len)
  (declare (type string s)
           (type (integer 0 *) p n len)
           (xargs :guard (and (= len (length s))
                              (<= p len))
                  :measure (if (and (natp p)
                                    (natp n)
                                    (natp len)
                                    (< p len))
                               (- (1+ len) p)
                             0)))
  (cond ((mbe :logic (not (and (natp p)
                               (natp n)
                               (natp len)
                               (< p len)))
              :exec (= p len))
         len)
        ((eql (char s p) #\Newline)
         (if (zp n)
             (1+ p)
           (newline-after s (1+ p) (1- n) len)))
        (t (newline-after s (1+ p) n len))))

(defthm newline-before-is-smaller
  (implies (natp p)
           (<= (newline-before s p n)
               p))
  :rule-classes :linear)

(defthm newline-after-is-bigger
  (implies (<= p len)
           (<= p
               (newline-after s p n len)))
  :rule-classes :linear)

(defthm newline-after-is-smaller
  (implies (<= p len)
           (<= (newline-after s p n len)
               len))
  :rule-classes :linear)

(defun surrounding-lines (s p n1 n2)

; Return substring of s including the line at position p as well as n1 lines
; before p and n2 lines after p.  For this purpose we consider a terminating
; newline to be part of the line; however, the final terminating newline is not
; included in the result.

  (declare (type string s)
           (type (integer 0 *) p n1 n2)
           (xargs :guard (<= p (length s))))
  (let* ((len (length s))
         (n1 (if (and (< p (length s))
                      (eql (char s p) #\Newline))
                 (1+ n1)
               n1)))
    (subseq s
            (newline-before s p n1)
            (newline-after s p n2 len))))
            
(defun first-diff-position-rec (s1 s2 p len1 len2)
  (declare (type string s1 s2)
           (type (integer 0 *) p len1 len2)
           (xargs :guard (and (equal len1 (length s1))
                              (equal len2 (length s2))
                              (<= p len1)
                              (<= p len2))
                  :measure (if (and (natp p)
                                    (natp len1)
                                    (< p len1))
                               (- len1 p)
                             0)))
  (cond ((mbe :logic (not (and (stringp s1)
                               (stringp s2)
                               (natp p)
                               (equal len1 (length s1))
                               (equal len2 (length s2))
                               (< p len1)
                               (< p len2)))
              :exec (or (= p len1)
                        (= p len2)))
         p)
        ((eql (char s1 p)
              (char s2 p))
         (first-diff-position-rec s1 s2 (1+ p) len1 len2))
        (t p)))

(defun first-diff-position (s1 s2)
  (declare (type string s1 s2))
  (first-diff-position-rec s1 s2 0 (length s1) (length s2)))

(defthm first-diff-position-is-small-weak-lemma
  (implies (and (<= p (length s1))
                (<= p (length s2)))
           (and (<= (first-diff-position-rec s1 s2 p (length s1) (length s2))
                    (length s1))
                (<= (first-diff-position-rec s1 s2 p (length s1) (length s2))
                    (length s2))))
  :rule-classes :linear)

(defthm first-diff-position-is-small-weak
  (and (<= (first-diff-position s1 s2)
           (length s1))
       (<= (first-diff-position s1 s2)
           (length s2)))
  :hints (("Goal" :in-theory (disable length)))
  :rule-classes :linear)
