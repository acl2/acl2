(include-book "acl2s-setup")
:q

(load "try-load-quicklisp.lsp")
(load "prover.lsp")
(load "logging.lsp")

(in-package :acl2s)

;; https://stackoverflow.com/a/4425671/1850564
(defun my-quit ()
  #+sbcl (sb-ext:quit)
  #+clisp (ext:exit)
  #+ccl (ccl:quit)
  #+allegro (excl:exit))

(defun main (args)
  (cond ((< (len args) 2)
    (progn (print "Usage: prover-debug <file>") 
           (sb-ext:quit)))
        ((= (len args) 2)
         (progn (print::set-print2-fd 1)
                (print::set-print3-fd 1)
                (setup-logger)
                (prove-file-read (second args))
                (my-quit)))))

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

(defun prove-file-read (path)
  (with-open-file (in path)
    (prover::check-proof-document (let ((*package* (find-package :acl2s)))
                                    (read in))
                                  :print-timings? nil))
  (loop for message in prover::*MESSAGES*
        do (when (not (string= (prover::ProofMessage-kind message) "timing"))
             (format t "~S~%" message))))

(unless (acl2::pc-command-type 'acl2-pc::claim-simple)
  (error "Looks like you don't have a new enough version of ACL2s to use the proof builder - please update your ACL2s build!"))

(save-exec "prover-debug" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
           :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::main sb-ext:*posix-argv*)' --disable-debugger")
