;; SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(make-event `(add-include-book-dir :acl2s-modes (:system . "acl2s/")))
(ld "acl2s-mode.lsp" :dir :acl2s-modes)
(acl2s-defaults :set verbosity-level 1)
(set-inhibit-warnings! "Invariant-risk" "theory")
(reset-prehistory t)
:q

(load "try-load-quicklisp.lsp")

(in-package "ACL2")
;; A few hacks to disable some printing
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
           (ignore val active-book-name include-bookp deferred-p))
  state)
(defun print-deferred-ttag-notes-summary (state)
  state)
(defun notify-on-defttag (val active-book-name include-bookp state)
  state)

(in-package "ACL2S")

;; We have to do this dance with readtables because usocket uses read
;;   macros that ACL2 doesn't support. We could alternatively get around
;;   this using include-raw with `:host-readtable t`.
(ql:quickload :named-readtables)
(named-readtables:defreadtable ACL2s (:merge :current))
(named-readtables:in-readtable :common-lisp)

;; Load simple-tcp-service (after setting up local-project-directories)
(pushnew (truename "../../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :simple-tcp-service)

;; Revert to the ACL2s readtable
(named-readtables:in-readtable ACL2s)

(load "handler.lsp")

(in-package "ACL2")
(defun main (args)
  (cond ((< (len args) 3)
         (progn (print "Usage: server output_fd seed")
                (sb-ext:quit)))
        ((= (len args) 3)
         (let ((out-fd (sb-sys:make-fd-stream (parse-integer (second args)) :output t :buffering :none))
               ;; Note that we don't use this argument here.
               (new-seed (parse-integer (third args))))
	   (server:run-tcp-server "0.0.0.0" #'server::handle-request :print-stream out-fd)))))

(save-exec "server" nil
           :init-forms '((value :q))
           :toplevel-args "--eval '(acl2::main sb-ext:*posix-argv*)' --disable-debugger")
