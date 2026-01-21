; A tool to clean up trivial lambdas (all formals mapped to themselves)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-lambda-with-hint")
(local (include-book "tools/flag" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; Gets rid of trivial lambdas (ones that bind all of their formals to themselves).
(mutual-recursion
 (defun drop-trivial-lambdas (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           term
         (let ((args (drop-trivial-lambdas-lst (fargs term))))
           (if (consp fn)
               ;; it's a lambda:
               (let* ((formals (lambda-formals fn))
                      (body (lambda-body fn))
                      (body (drop-trivial-lambdas body)))
                 (if (equal formals args)
                     ;; If the formals are the same as the args, we
                     ;; don't need a lambda at all:
                     body
                   ;; no change:
                   (cons-with-hint (make-lambda-with-hint formals body fn) args term)))
             ;; not a lambda:
             (cons-with-hint fn args term)))))))
 (defun drop-trivial-lambdas-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons-with-hint (drop-trivial-lambdas (first terms))
                     (drop-trivial-lambdas-lst (rest terms))
                     terms))))

(local (make-flag drop-trivial-lambdas))

(local
 (defthm len-of-drop-trivial-lambdas-lst
   (equal (len (drop-trivial-lambdas-lst terms))
          (len terms))
   :hints (("Goal" :induct (len terms)))))

(local
 (defthm-flag-drop-trivial-lambdas
   (defthm pseudo-termp-of-drop-trivial-lambdas
     (implies (pseudo-termp term)
              (pseudo-termp (drop-trivial-lambdas term)))
     :flag drop-trivial-lambdas)
   (defthm pseudo-termp-of-drop-trivial-lambdas-lst
     (implies (pseudo-term-listp terms)
              (pseudo-term-listp (drop-trivial-lambdas-lst terms)))
     :flag drop-trivial-lambdas-lst)
   :hints (("Goal" :in-theory (enable pseudo-term-listp-when-symbol-listp)))))

;; redundant and non-local
(defthm pseudo-termp-of-drop-trivial-lambdas
  (implies (pseudo-termp term)
           (pseudo-termp (drop-trivial-lambdas term))))

;; redundant and non-local
(defthm pseudo-term-listp-of-drop-trivial-lambdas-lst
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (drop-trivial-lambdas-lst terms))))

(verify-guards drop-trivial-lambdas :hints (("Goal" :expand ((pseudo-termp term)))))
