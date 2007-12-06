; This little utility, rewrite-theory, was written by Matt Kaufmann.

(in-package "ACL2")

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
  (let ((diff (set-difference-theories-fn
               (universal-theory-fn to wrld)
               (universal-theory-fn from wrld)
               t ;; Tue Oct 31 09:22:52 2006. Hanbing. changed to accomodate
                 ;; the changes in ACL2 3.0.1
               wrld)))
    (collect-rewrites diff nil)))

(defmacro rewrite-theory (from &optional (to ':here))
  ; Returns all rewrite rules introduced after FROM up to and including TO.
  (list 'rewrite-theory-fn from to 'world))

