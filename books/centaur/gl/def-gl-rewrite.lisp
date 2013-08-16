

(in-package "GL")

(include-book "tools/bstar" :dir :system)
(include-book "centaur/misc/beta-reduce-full" :dir :system)

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



(defun gl-set-uninterpreted-fn (fn val world)
  (b* ((formals (getprop fn 'formals :none 'current-acl2-world world))
       (fn (if (eq formals :none)
               (cdr (assoc fn (table-alist 'acl2::macro-aliases-table world)))
             fn))
       (formals (if (eq formals :none)
                    (getprop fn 'formals :none 'current-acl2-world world)
                  formals))
       ((when (eq formals :none))
        (er hard? 'gl-set-uninterpreted-fn
            "~x0 is neither a function nor a macro-alias for a function~%" fn)))
    `(table gl-uninterpreted-functions ',fn ,val)))

(defmacro gl-set-uninterpreted (fn)
  `(make-event
    (gl-set-uninterpreted-fn ',fn t (w state))))

(defmacro gl-unset-uninterpreted (fn)
  `(make-event
    (gl-set-uninterpreted-fn ',fn nil (w state))))
       


(defun gl-branch-merge-find-fnsym (name state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((thm (acl2::beta-reduce-full (acl2::meta-extract-formula name state)))
       (concl
        (if (eq (car thm) 'implies)
            (third thm)
          thm))
       (equiv (car concl))
       ((unless (and (symbolp equiv)
                     (getprop equiv 'acl2::coarsenings nil 'current-acl2-world
                              (w state))
                     (consp (second concl))
                     (eq (car (second concl)) 'if)
                     (consp (third (second concl)))
                     (symbolp (car (third (second concl))))))
        (er hard? 'gl-branch-merge-find-fnsym
            "The theorem ~x0 did not have the expected form for a branch ~
             merge rule: conclusion should be:~%  (equiv (if c (fn args) b) ~
             rhs)" name)))
    (car (third (second concl)))))

(defun def-gl-branch-merge-fn (name body hints otf-flg)
  `(progn
     (defthm ,name
       ,body
       :hints ,hints
       :otf-flg ,otf-flg
       :rule-classes nil)
     (make-event
      (let* ((fn (gl-branch-merge-find-fnsym ',name state))
             (rules (cons ',name (cdr (assoc fn (table-alist
                                                 'gl-branch-merge-rules
                                                 (w state)))))))
        `(table gl-branch-merge-rules ',fn ',rules)))))

(defmacro def-gl-branch-merge (name body &key hints otf-flg)
  (def-gl-branch-merge-fn name body hints otf-flg))
