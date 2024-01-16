(include-book "acl2s-setup")
:q

(load "try-load-quicklisp.lsp")
(load "prover.lsp")
(load "logging.lsp")

(in-package :acl2s)

(defun main (args)
  (cond ((< (len args) 3)
    (progn (print "Usage: prover-java <output fd> <message output fd>") 
           (sb-ext:quit)))
        ((= (len args) 3)
         (progn (print::set-print2-fd (parse-integer (second args)))
                (print::set-print3-fd (parse-integer (third args)))
                (setup-logger)))))

(in-package :acl2)

(set-macro-character
 #\`
 #'(lambda (stream char)
     (declare (ignore char))
     (let ((*backquote-counter* (1+ *backquote-counter*)))
       (backquote (read stream t nil t)))))

(set-macro-character
 #\,
 #'(lambda (stream char)
     (declare (ignore char))
     (let ((*backquote-counter* (1- *backquote-counter*)))
       (acl2-comma-reader stream))))

;; From Matt, to resolve proof-builder issue
(defun remove-?s (term abbreviations-alist ctx state)
  (let ((newterm (sublis-expr-non-quoteps abbreviations-alist term)))
    (er-progn (chk-?s newterm ctx state)
              (value newterm))))

(in-package :acl2s)

(unless (acl2::pc-command-type 'acl2-pc::claim-simple)
  (error "Looks like you don't have a new enough version of ACL2s to use the proof builder - please update your ACL2s build!"))

(save-exec "prover-java" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
           :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::main sb-ext:*posix-argv*)' --disable-debugger")
