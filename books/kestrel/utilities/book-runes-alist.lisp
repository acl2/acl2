; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc book-runes-alist
  :parents (kestrel-utilities)
  :short "Returns an alist associating book full pathnames with @(see rune)s introduced"
  :long "
 @({
 General Form:
 (book-runes-alist wrld) ; wrld an ACL2 logical world

 Typical Form:
 (book-runes-alist (w state))
 })

 <p>This utility returns an alist.  The keys are the full pathnames of books
 included in the given @(see world).  With such book is associated all @(see
 rune)s introduced in that book &mdash; directly introduced, rather than being
 introduced in an included sub-book.  The computation is made efficient by use
 of memoization (see @(see memoize)).</p>")

(defun intersectp-domains (a1 a2)

; Based on intersection-domains in ACL2 source code, which is for EQ.

  (declare (xargs :guard (and (alistp a1)
                              (alistp a2))))
  (if (consp a1)
      (or (assoc-equal (caar a1) a2)
          (intersectp-domains (cdr a1) a2))
    nil))

(defun append-disjoint-alists (a1 a2)
  (declare (xargs :guard (and (alistp a1)
                              (alistp a2))))
  (if (intersectp-domains a1 a2)
      (er hard? 'append-disjoint-alists
          "Implementation error: alists with non-disjoint keys:~|~x0~|~x1"
          a1 a2)
    (append a1 a2)))

(defun reverse-entries (alist)
  (declare (xargs :guard (true-list-listp alist)))
  (cond ((endp alist) nil)
        (t (cons (cons (caar alist) (reverse (cdar alist)))
                 (reverse-entries (cdr alist))))))

(program)

(mutual-recursion

(defun book-runes-alist-2 (wrld augmented-runes alist)
  (cond
   ((or (null wrld)
        (and (eq (caar wrld) 'command-landmark)
             (eq (cadar wrld) 'global-value)
             (equal (access-command-tuple-form (cddar wrld))
                    '(exit-boot-strap-mode))))
    alist)
   ((and (eq (caar wrld) 'include-book-path)
         (eq (cadar wrld) 'global-value))
    (cond ((null (cddar wrld))
           (append-disjoint-alists alist
                                   (book-runes-alist-1 wrld)))
          (t (book-runes-alist-2 (cdr wrld)
                                 nil
                                 (if augmented-runes
                                     (let ((book-name (car (cddar wrld))))
                                       (put-assoc-equal
                                        book-name
                                        (append? augmented-runes
                                                 (cdr (assoc-equal book-name
                                                                   alist)))
                                        alist))
                                   alist)))))
   ((eq (cadar wrld) 'runic-mapping-pairs)
    (book-runes-alist-2 (cdr wrld)
                        (append (cddar wrld) augmented-runes)
                        alist))
   (t (book-runes-alist-2 (cdr wrld) augmented-runes alist))))

(defun book-runes-alist-1 (wrld)
  (assert$ (equal (car wrld) '(INCLUDE-BOOK-PATH GLOBAL-VALUE))
           (book-runes-alist-2 (cdr wrld) nil nil)))
)

(defun scan-to-include-book-path (wrld)
  (cond
   ((or (null wrld)
        (and (eq (caar wrld) 'command-landmark)
             (eq (cadar wrld) 'global-value)
             (equal (access-command-tuple-form (cddar wrld))
                    '(exit-boot-strap-mode))))
    nil)
   ((and (eq (caar wrld) 'include-book-path)
         (eq (cadar wrld) 'global-value))
    (assert$ (null (cddar wrld))
             wrld))
   (t (scan-to-include-book-path (cdr wrld)))))

(defun book-runes-alist-top (wrld)
  (reverse-entries (book-runes-alist-1 wrld)))

(memoize 'book-runes-alist-1 :recursive t)

(memoize 'book-runes-alist-top)

(defun book-runes-alist (wrld)
  (cond
   ((global-val 'include-book-path wrld)
    (er hard 'book-runes-alist
        "Attempted to call book-runes-alist inside include-book! ~ ~
         Include-book-path is:~|~x0"
        (global-val 'include-book-path wrld)))
   (t (let ((wrld1 (scan-to-include-book-path wrld)))
        (cond ((null wrld1) nil)
              (t (assert$
                  (equal (car wrld1) '(INCLUDE-BOOK-PATH GLOBAL-VALUE))
                  (book-runes-alist-top wrld1))))))))
