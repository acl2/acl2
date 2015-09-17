;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;; SMT-run writes to Z3, invoke Z3 and gets the result
(in-package "ACL2")

(include-book "./config")
(include-book "std/io/top" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(defttag :tshell)
(value-triple (tshell-ensure))

(set-state-ok t)
;;(set-print-case :downcase state)
(defttag :writes-okp)

;; princ$-list-of-strings
(defun princ$-list-of-strings (alist channel state)
  "princ$-list-of-strings: the real function to print the Z3 program."
  (if (consp alist)
    (let ((state (princ$-list-of-strings (car alist) channel state)))
      (princ$-list-of-strings (cdr alist) channel state))
    (if (and (not (equal alist nil))
	     (not (acl2-numberp alist)))   ;; if alist is a number, should be treated separately
      (princ$ (string alist) channel state)
      (if (acl2-numberp alist)
        (princ$ alist channel state)
        state))))

;; coerce a list of strings and characters into a string
(defun coerce-str-and-char-to-str (slist)
  "coerce-str-and-char-to-str: coerce a list of strings and characters into a string"
  (if (endp slist)
      nil
    (cond ((stringp (car slist))
	   (concatenate 'string
			(car slist)
			(coerce-str-and-char-to-str (cdr slist))))
	  ((characterp (car slist))
	   (concatenate 'string
			(coerce (list (car slist)) 'STRING)
			(coerce-str-and-char-to-str (cdr slist))))
	  (t (er hard? 'top-level "Error(run): Invalid list ~q0." (car slist))))))

;; write-head-simple
(defun write-head-simple (smt-config)
  (coerce-str-and-char-to-str
   (list "_SMT_ = "
         (smtlink-config->SMT-class smt-config)
         "()"
         #\Newline)))

;; write-head
(defun write-head (smt-config)
  "write-head: writes the head of a z3 file"
  (coerce-str-and-char-to-str
   (list "from sys import path"
	 #\Newline
	 "path.insert(0,\"" (smtlink-config->dir-interface smt-config) "\")"
	 #\Newline
	 "from " (smtlink-config->SMT-module smt-config) " import " (smtlink-config->SMT-class smt-config)
	 #\Newline
	 "_SMT_ = " (smtlink-config->SMT-class smt-config) "()"
	 #\Newline)))

;; write-SMT-file
(defun write-SMT-file (filename class-formula translated-formula smt-config custom-config state)
  "write-SMT-file: writes the translated formula into a python file, it opens and closes the channel and write the including of Z3 inteface"
  (mv-let
   (channel state)
   (open-output-channel! filename :character state)
   (let ((state (princ$-list-of-strings
                 class-formula channel state)))
     (let ((state (princ$-list-of-strings
                   (if (or (equal (smt-cnf) (default-smtlink-config))
                           (equal custom-config nil))
                       (write-head-simple smt-config)
                     (write-head smt-config))
                   channel state)))
     (let ((state (princ$-list-of-strings translated-formula channel state)))
       (close-output-channel channel state))))))

;; write-expander-file
(defun write-expander-file (filename expanded-term state)
  "write-expander-file: write expanded term to a file"
  (mv-let
   (channel state)
   (open-output-channel! filename :character state)
   (let ((state
	  (princ$-list-of-strings
	   expanded-term channel state)))
     (close-output-channel channel state))))

;; SMT-run
(defun SMT-run (filename smt-config)
  "SMT-run: run the external SMT procedure from ACL2"
  (let ((cmd (concatenate 'string (smtlink-config->smt-cmd smt-config) " " filename)))
    (time$ (tshell-call cmd
                        :print t
                        :save t)
           :msg "; Z3: `~s0`: ~st sec, ~sa bytes~%"
           :args (list cmd))))

