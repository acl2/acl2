#|$ACL2s-Preamble$;
(include-book "defcode" :ttags ((defcode)))
(include-book "redefun" :ttags ((defcode)))

(acl2::begin-book t :ttags ((defcode) (table-guard)));$ACL2s-Preamble$|#

(in-package "ACL2")

(defttag table-guard) ; need to do some evil stuff

; rewrite the table code to allow guard changes if a ttag is active
(progn+touchable
 :all
 (redefun+rewrite
  table-fn1
  (:pat (cond
         ((equal old-guard tterm)
          %redundant%)
         (old-guard
          %er1%)
         ((getpropc name 'table-alist nil %wrld%)
          %er2%)
         (t
          %rest%))
   :repl (cond
          ((equal old-guard tterm)
           %redundant%)
          ((and old-guard (not (ttag %wrld%)))
           %er1%)
          ((and (getpropc name 'table-alist nil %wrld%)
                (not (ttag %wrld%)))
           %er2%)
          (t
           %rest%))
   :vars (%redundant%
          %er1%
          %er2%
          %wrld%
          %rest%)
   :mult 1)))

(defttag nil) ; end of evil stuff


; name: name of table whose guard to rewrite
; rewrite-spec: like in redefun+rewrite (see rewrite-code.lisp)
; hints: for proving that old-guard implies new-guard
; skip-proof: t if you want to skip proving old-guard implies new-guard
;
; proof is used as a sanity check mostly.
(defmacro rewrite-table-guard (name rewrite-spec &key hints skip-proof)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (er-let* ((old-guard (table ,name nil nil :guard))
              (new-guard-cons (er-rewrite-form (list old-guard)
					       .,rewrite-spec)))
      (er-progn
       (if ',skip-proof
         (value nil)
         (thm-fn `(implies ,old-guard ,(car new-guard-cons))
                 state ',hints nil))
       (value `(table ,',name nil nil :guard ,(car new-guard-cons)))))))

; adds specified key to acl2-defaults-table with guard for its value.
; also defines a setter macro.
(defmacro add-acl2-defaults-table-key (name val-guard)
  (declare (xargs :guard (keywordp name)))
  (let* ((name-str (symbol-name name))
         (set-sym (intern (string-append "SET-" name-str) "ACL2")))
    `(progn
      (rewrite-table-guard
       acl2-defaults-table
       (:carpat %body%
	:vars %body%
        :repl (if (eq key ',name)
                ,val-guard
                %body%)))
      (defmacro ,set-sym (v)
        `(with-output :off summary
          (progn (table acl2-defaults-table ,',name ',v)
                 (table acl2-defaults-table ,',name)))))))


#| test case:
(defttag t)

(add-acl2-defaults-table-key :termination-method
                             (member-eq val '(:foo :bar :baz)))

(set-termination-method :foo)
|#
