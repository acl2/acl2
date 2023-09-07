; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)

(defttag :acl2data)

(defun cached-augmented-useless-theory ()
  (cons nil nil))

(defun update-cached-augmented-useless-theory (wrld-tail aug-runes)
  (declare (ignore wrld-tail))
  aug-runes)

(progn!
 (set-raw-mode t)
 (defvar *cached-augmented-useless-theory* (cons nil nil))
 (defun cached-augmented-useless-theory ()
   *cached-augmented-useless-theory*)
 (defun update-cached-augmented-useless-theory (wrld lst)
   (setf (car *cached-augmented-useless-theory*)
         wrld
         (cdr *cached-augmented-useless-theory*)
         lst)))

(defun augmented-useless-runes-2 (augmented-runes ans)
  (cond ((endp augmented-runes) ans)
        ((member-eq (cadar augmented-runes) '(:CONGRUENCE :EQUIVALENCE))
         (augmented-useless-runes-2 (cdr augmented-runes) ans))
        (t (cons (car augmented-runes)
                 (augmented-useless-runes-2 (cdr augmented-runes) ans)))))

(defun augmented-useless-runes-1 (lst ans redefined)

; This is based on ACL2 source function universal-theory-fn1.  Here we exempt
; congruence and equivalence runes.

  (cond
   ((null lst)
    (reverse ans)) ; unexpected, but correct
   (t (let ((cached (cached-augmented-useless-theory)))
        (cond
         ((eq lst (car cached))
          (revappend ans (cdr cached)))
         ((eq (cadr (car lst)) 'runic-mapping-pairs)
          (cond
           ((eq (cddr (car lst)) *acl2-property-unbound*)
            (augmented-useless-runes-1 (cdr lst) ans
                                       (add-to-set-eq (car (car lst))
                                                      redefined)))
           ((member-eq (car (car lst)) redefined)
            (augmented-useless-runes-1 (cdr lst) ans redefined))
           (t (augmented-useless-runes-1 (cdr lst)
                                         (augmented-useless-runes-2
                                          (cddr (car lst))
                                          ans)
                                         redefined))))
         (t
          (augmented-useless-runes-1 (cdr lst) ans redefined)))))))

(defun augmented-useless-runes-0 (wrld)
  (let ((ans (augmented-useless-runes-1 wrld nil nil)))
    (update-cached-augmented-useless-theory wrld ans)))

(defun my-set-difference-augmented-theories (lst1 lst2 ans)

; This is closely based on ACL2 source function
; set-difference-augmented-theories-fn1, but unlike that function, this one
; returns an augmented runic theory rather than a runic theory.

  (cond ((null lst1) (revappend ans nil))
        ((null lst2) (revappend ans lst1))
        ((= (car (car lst1)) (car (car lst2)))
         (my-set-difference-augmented-theories (cdr lst1) (cdr lst2) ans))
        ((> (car (car lst1)) (car (car lst2)))
         (my-set-difference-augmented-theories
          (cdr lst1) lst2 (cons (car lst1) ans)))
        (t (my-set-difference-augmented-theories lst1 (cdr lst2) ans))))

(defun augmented-useless-runes (runes wrld)
  (my-set-difference-augmented-theories (augmented-useless-runes-0 wrld)
                                        (augment-theory runes wrld)
                                        nil))
