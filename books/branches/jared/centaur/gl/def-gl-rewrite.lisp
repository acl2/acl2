

(in-package "GL")

(include-book "tools/bstar" :dir :system)

(defun scan-lemmas-for-nume (lemmas nume)
  (declare (xargs :mode :program))
  (b* (((when (endp lemmas)) nil)
       (rule (car lemmas))
       ((when (eql (acl2::access acl2::rewrite-rule rule :nume) nume))
        rule))
    (scan-lemmas-for-nume (cdr lemmas) nume)))

(defun scan-props-for-nume-lemma (props nume)
  (declare (xargs :mode :program))
  (and (consp props)
       (or (and (eq (cadar props) 'acl2::lemmas)
                (scan-lemmas-for-nume (cddar props) nume))
           (scan-props-for-nume-lemma (cdr props) nume))))
    

(defun find-lemma-for-rune (rune world)
  (declare (xargs :mode :program))
  (b* ((nume (acl2::runep rune world))
       ((unless nume) nil)
       (segment (acl2::world-to-next-event
                 (cdr (acl2::decode-logical-name (cadr rune) world)))))
    (scan-props-for-nume-lemma (acl2::actual-props segment nil nil) nume)))

(defun add-gl-rewrite-fn (rune world)
  (declare (xargs :mode :program))
  (b* ((rune (if (symbolp rune) `(:rewrite ,rune) rune))
       (rule (find-lemma-for-rune rune world))
       ((unless rule)
        (cw "Failed to find a lemma for rune ~x0~%" rune))
       (fnsym (car (acl2::access acl2::rewrite-rule rule :lhs)))
       (entries (cdr (assoc fnsym (table-alist 'gl-rewrite-rules world))))
       ((when (member-equal rule entries))
        '(value-triple nil)))
    `(table gl-rewrite-rules ',fnsym '(,rune . ,entries))))

(defmacro add-gl-rewrite (rune)
  `(make-event
    (add-gl-rewrite-fn ',rune (w state))))

(defmacro def-gl-rewrite (name &rest args)
  `(progn (defthmd ,name . ,args)
          (add-gl-rewrite ,name)))
