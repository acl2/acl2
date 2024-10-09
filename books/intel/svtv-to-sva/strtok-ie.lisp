; Copyright (C) Intel Corporation
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

(in-package "SV")

(include-book "std/util/define" :dir :system)
(include-book "std/strings/cat-base" :dir :system)


(define strtok-ie-aux ((x stringp) (n natp) (xl natp)
                       (include character-listp)
                       (exclude character-listp)
                       (curr character-listp)
                       (acc string-listp))
  :guard (and (<= xl (length x))
              (<= n xl))
  :returns (r string-listp :hyp (string-listp acc))
  :measure (nfix (- xl n))
  (if (mbe :logic (zp (- xl n))
           :exec  (int= n xl))
      (if curr (cons (str::rchars-to-string curr) acc) acc)
    (b* ((char1 (char x n))
         (include-p (member char1 include))
         (exclude-p (member char1 exclude))
         (match-p   (or include-p exclude-p)))
      (strtok-ie-aux
       x (1+ n) xl include exclude
       (if match-p nil (cons char1 curr))
       (if (not match-p) acc
         (b* ((acc (if curr (cons (str::rchars-to-string curr) acc) acc))
              (acc (if include-p (cons (coerce (list char1) 'string) acc) acc)))
           acc))))))

(local (defthm string-list-is-true-list
         (implies (string-listp x) (true-listp x))))

(local (defthm stringp-when-string-listp
         (implies (string-listp x)
                  (not (stringp x)))))

(local (defthm string-listp-of-revappend
         (implies (and (string-listp x)
                       (string-listp y))
                  (string-listp (revappend x y)))))

(define strtok-ie ((x stringp) (include character-listp) (exclude character-listp))
  ;; An "include/exclude" strtok which adds individual tokens for the delimiters
  ;; that are either included in the list of tokens produced or not.
  :returns (r string-listp)
  (reverse (strtok-ie-aux x 0 (length x) include exclude nil nil)))

