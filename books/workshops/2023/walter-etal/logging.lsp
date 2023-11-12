(in-package :acl2s)

(defmethod v:format-message ((stream stream) (message v:message))
  (cond ((find :query (v:categories message) :test #'v::matching-tree-category)
         (format stream "~a" (v:content message)))
        ;; todo: only use multiline comment if message contents contain a newline
        ((find :status (v:categories message) :test #'v::matching-tree-category)
         (format stream "#| ~S |#" (v:content message)))
        ((find :may-fail-query.compute (v:categories message) :test #'v::matching-tree-category)
         (format stream "~a" (v:content message)))
        ((find :may-fail-query (v:categories message) :test #'v::matching-tree-category)
         (format stream "(mv-let (erp val state) ~a (declare (ignore erp)) (mv nil val state))" (v:content message)))
        (t (format stream "~&~a~%" (v:content message)))))

(defun setup-logger ()
  (v:restart-global-controller)
  (v:define-pipe ()
                 (v:level-filter :level :debug)
                 (v:category-tree-filter :categories '(:query :status :may-fail-query))
                 (v:file-faucet :file #p"debug-output.log"))
  (init-log))

(defconstant +acl2s-setup-contents+
             (let (eof-sym (gensym))
               (with-open-file (in "acl2s-setup.lisp") ;; TODO this depends on current directory (as do many file ops in here). Should change that.
                 (loop for c = (read in nil eof-sym)
                       while (not (equal c eof-sym))
                       collect c))))

(defun init-log ()
  (loop for line in +acl2s-setup-contents+
        do (v:debug :query.setup "~S" line))
  (v:debug :query.setup "~S" '(set-ld-redefinition-action '(:doit . :overwrite) state))
  (v:debug :query.setup "~S" '(set-ignore-ok t)))
