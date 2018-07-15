; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defun extend-injections-1 (x range injection)
  (declare (xargs :guard (and (true-listp range)
                              (r-symbol-alistp injection))))
  (cond ((endp range) nil)
        ((rassoc-eq (car range) injection)
         (extend-injections-1 x (cdr range) injection))
        (t (cons (acons x (car range) injection)
                 (extend-injections-1 x (cdr range) injection)))))

(defun r-symbol-alistp-lst (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (r-symbol-alistp (car x))
                (r-symbol-alistp-lst (cdr x))))))

(defun extend-injections (x range injections)
  (declare (xargs :guard (and (true-listp range)
                              (r-symbol-alistp-lst injections))))
  (cond ((endp injections) nil)
        (t (append (extend-injections-1 x range (car injections))
                   (extend-injections x range (cdr injections))))))

(defun injections (domain range)

; Return a list of all one-to-one maps from domain to range (each represented
; as an alist).

  (declare (xargs :guard (and (true-listp domain)
                              (symbol-listp range))))
  (cond ((endp domain) (list nil))
        (t (extend-injections (car domain)
                              range
                              (injections (cdr domain) range)))))

(defun injection-count (from to acc)

; This is (at least approximately) a theorem:

;   (implies (natp acc)
;            (equal (injection-count (len dom) (len ran) acc)
;                   (* acc (len (injections dom ran)))))

  (declare (type (unsigned-byte 30) from to)
           (xargs :guard (and (<= from to)
                              (acl2-numberp acc))))
  (cond ((zp from) acc)
        (t (injection-count (1- from) (1- to) (* to acc)))))

(defun too-many-embeddings (len-domain len-range)

; The value 1000, below, is highly arbitrary.

  (and (<= 3 len-domain) ; quick filter; we always tolerate range * (range-1)
       (> (injection-count (the-fixnum! len-domain 'too-many-embeddings)
                           (the-fixnum! len-range 'too-many-embeddings)
                           1)
          1000)))

(defxdoc injections
  :parents (kestrel-utilities)
  :short "Set of all functions from a finite domain to a finite range"
  :long "
 @({
 General Form:

 (injections domain range)
 })

 <p>where @('domain') and range are true-lists of symbols (actually the members
 of @('domain') need not be symbols).  The result is a list of alists,
 representing all functions from @('domain') to @('range').  The following
 example illustrates this function: either</p>

 <ul>
 <li>@('b') maps to @('c') and @('a') maps to @('d') or @('e'), or</li>
 <li>@('b') maps to @('d') and @('a') maps to @('c') or @('e'), or</li>
 <li>@('b') maps to @('e') and @('a') maps to @('c') or @('d').</li>
 </ul>

 @({
 ACL2 !>(injections '(a b) '(c d e))
 (((A . D) (B . C))
  ((A . E) (B . C))
  ((A . C) (B . D))
  ((A . E) (B . D))
  ((A . C) (B . E))
  ((A . D) (B . E)))
 ACL2 !>
 })")
