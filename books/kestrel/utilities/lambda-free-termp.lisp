; Checking that a term contains no lambdas
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(mutual-recursion
 (defun lambda-free-termp (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (variablep term)
       t
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           t
         (and (symbolp fn) ;excludes a lambda application
              (lambda-free-termsp (fargs term)))))))
 (defun lambda-free-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
     (and (lambda-free-termp (first terms))
          (lambda-free-termsp (rest terms))))))

(defthm lambda-free-termp-of-cdr-of-assoc-equal
  (implies (lambda-free-termsp (strip-cdrs alist))
           (lambda-free-termp (cdr (assoc-equal form alist)))))

(defthm lambda-free-termsp-of-true-list-fix
  (equal (lambda-free-termsp (true-list-fix terms))
         (lambda-free-termsp terms)))

(defthmd lambda-free-termsp-when-symbol-listp
  (implies (symbol-listp terms)
           (lambda-free-termsp terms))
  :hints (("Goal" :in-theory (enable lambda-free-termsp))))

(defthm lambda-free-termsp-of-take
  (implies (lambda-free-termsp terms)
           (lambda-free-termsp (take n terms)))
  :hints (("Goal" :in-theory (enable lambda-free-termsp))))
