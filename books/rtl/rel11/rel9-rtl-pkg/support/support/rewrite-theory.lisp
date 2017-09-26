; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

; This little utility, rewrite-theory, was written by Matt Kaufmann.

(in-package "RTL")

(program)

(defun collect-rewrites (runes ans)
  (cond
   ((endp runes) (reverse ans))
   ((eq (caar runes) :rewrite)
    (collect-rewrites (cdr runes) (cons (car runes) ans)))
   (t
    (collect-rewrites (cdr runes) ans))))

(defun rewrite-theory-fn (from to wrld)
; Returns all rewrite rules introduced after FROM, up to and including TO.
  (let ((diff (acl2::set-difference-theories-fn
               (acl2::universal-theory-fn to wrld)
               (acl2::universal-theory-fn from wrld)
               t ;; Tue Oct 31 09:22:52 2006. Hanbing. changed to accomodate
                 ;; the changes in ACL2 3.0.1
               t ;; further change 9/2017 from Matt K
               wrld)))
    (collect-rewrites diff nil)))

(defmacro rewrite-theory (from &optional (to ':here))
  ; Returns all rewrite rules introduced after FROM up to and including TO.
  (list 'rewrite-theory-fn from to 'world))

