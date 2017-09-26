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
; Returns all rewrite rules introduced after from, up to and including to.
  (let ((diff (set-difference-theories-fn
               (universal-theory-fn to wrld)
               (universal-theory-fn from wrld)
               t t wrld)))
    (collect-rewrites diff nil)))

(defmacro rewrite-theory (from &optional (to ':here))
  ; Returns all rewrite rules introduced after from, up to and including to.
  (list 'rewrite-theory-fn from to 'world))

