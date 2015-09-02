; This is an odd book.  Originally, I wanted to explore the idea of
; modifying an existing proof and using some of ACL2's debugging tools to
; figure out why it failed.  So I decided to modify qsort so that it
; eliminates duplicates on the fly.

; The resulting function, no-dups-qsort, does not have the perm property.
; But it does produce ordered output.

; So I set out to prove that and discovered that the original proof of
; orderedp-qsort relied crucially on the perm property!  So my proof
; of no-dups-qsort would be very different.

; Rather than abandon the effort (since I was trying to explore proof
; debugging tools) I finished it, but by a different route.

; Basically, I prove that no-dups-qsort is just the result of eliminating
; duplicates from qsort's output.  To prove that I need to move elim-dups
; through append.  To prove that the result is ordered, I have to show that
; elim-dups preserves that property -- and rely on qsort being ordered.

(in-package "ACL2")

(include-book "qsort")

(defun no-dups-cons (x y)
  (cond ((and (consp y)
              (equal x (car y)))
         y)
        (t (cons x y))))

(defun no-dups-qsort (x)
  (cond ((endp x)
         nil)
        ((endp (cdr x))
         (list (car x)))
        (t (append (no-dups-qsort (filter 'LT (cdr x) (car x)))
                   (no-dups-cons
                    (car x)
                    (no-dups-qsort (filter 'GTE (cdr x) (car x))))))))

(defun elim-dups (x)
  (cond ((endp x) nil)
        (t (no-dups-cons (car x)
                         (elim-dups (cdr x))))))

; In the failed proof of no-dups-qsort-is-elim-dups-qsort, I see a subgoal of
; the form (elim-dups (append ...)) and generate the first lemma I anticipated.

; How elim-dups moves through append:

(defthm elim-dups-append
  (implies (and (consp b)
                (all-rel 'LT (double-rewrite a) (car b)))
  (equal (elim-dups (append a b))
         (append (elim-dups a)
                 (elim-dups b)))))

; NOTE:  The double-rewrite is suggested by the system and if you don't
; use it, the rest of this proof fails!

; This next rule ought to be in the qsort.lisp file, although it isn't actually
; needed there.

(defthm all-rel-filter
  (all-rel fn (filter fn x e) e))

(defthm no-dups-qsort-is-elim-dups-qsort
   (equal (no-dups-qsort x) (elim-dups (qsort x))))

; The second lemma I anticipated:  how elim-dups preserves orderedp.

(defthm orderedp-elim-dups
  (implies (orderedp x)
           (orderedp (elim-dups x))))

(defthm orderedp-no-dups-qsort
  (orderedp (no-dups-qsort x)))