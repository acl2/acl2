;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
(include-book "str")

(defttag open-output-channel!)

(defun mangle-filename (name)
  ;; Some lisps complain about having certain characters in filenames.  When
  ;; you open a file, you should consider mangling its name.
  (declare (xargs :mode :program))
  (STR::string-replace-patterns name
                                '(("_" . "_usc_")
                                  ("[" . "_lbr_")
                                  ("]" . "_rbr_")
                                  ("{" . "_lcl_")
                                  ("}" . "_rcl_")
                                  ("(" . "_lp_")
                                  (")" . "_rp_")
                                  ("<" . "_lt_")
                                  (">" . "_gt_")
                                  ("'"  . "_apo_")
                                  ("\"" . "_quo_")
                                  ("`" . "_bquo_")
                                  ("*" . "_st_")
                                  (" " . "_sp_")
                                  ("/" . "_sl_")
                                  ("\\" . "_bsl_")
                                  ("?" . "_qmk_")
                                  ("%" . "_pct_")
                                  ("=" . "_eq_")
                                  (":" . "_col_")
                                  (";" . "_sem_")
                                  ("|" . "_bar_")
                                  )))

(defun open-output-channel$ (file-name typ state)
  ;; This is the same as open-output-channel!, except it can be used without
  ;; having to have an open trust tag.  I don't think the behavior discussed
  ;; in :doc open-output-channel! is a credible threat to soundness, and do
  ;; not want to be forced to add ttags everywhere.
  (declare (xargs :guard (and (stringp file-name)
                              (member-eq typ *file-types*)
                              (state-p state))
                  :stobjs state))
  (open-output-channel! file-name typ state))

;; (defun current-book-info (state)
;;   ;; If we are currently certifying a book, we return an alist that describes
;;   ;; the location of the book's file.  The alist will look like this:
;;   ;;
;;   ;;   ((:FULLPATH . "/home/jared/my-book.lisp")
;;   ;;    (:DIRNAME  . "/home/jared/")
;;   ;;    (:BASENAME . "my-book.lisp")
;;   ;;    (:ROOTNAME . "my-book")
;;   ;;    (:SUFFIX   . ".lisp"))
;;   ;;
;;   ;; Otherwise, e.g., if you call this function from an interactive session,
;;   ;; we return nil.
;;   (declare (xargs :mode :program :stobjs state))
;;   (let ((info
;;          ;; In previous versions of ACL2 this was just a string or nil,
;;          ;; but now it's a defrec or nil.
;;          (f-get-global 'certify-book-info state)))
;;     (if (not info)
;;         nil
;;       (let* ((fullpath       (access certify-book-info info :full-book-name))
;;              (fullpath-len   (length fullpath))
;;              (fullpath-chars (coerce fullpath 'list))
;;              (dirname        (f-get-global 'connected-book-directory state))
;;              (dirname-len    (length dirname))
;;              (dirname-chars  (coerce dirname 'list)))
;;         (if (or (not (< dirname-len fullpath-len))
;;                 (not (equal (take dirname-len fullpath-chars) dirname-chars)))
;;             (er hard 'current-book-info "Sanity check failed; aborting.")
;;           (let* ((basename-chars (nthcdr dirname-len fullpath-chars))
;;                  (basename       (coerce basename-chars 'string))
;;                  (suffix-chars   (member-equal #\. basename-chars))
;;                  (suffix         (coerce suffix-chars 'string)))
;;             (if (not (equal suffix ".lisp"))
;;                 (er hard 'current-book-info "Expected .lisp suffix; aborting.")
;;               (let* ((rootname-chars (take (- (length basename) (length suffix)) basename-chars))
;;                      (rootname       (coerce rootname-chars 'string)))
;;                 (list (cons :fullpath fullpath)
;;                       (cons :dirname  dirname)
;;                       (cons :basename basename)
;;                       (cons :rootname rootname)
;;                       (cons :suffix suffix))))))))))



(defun println (line channel state)
  ;; This is the same as princ$, but it prints a newline afterwards.  This is
  ;; useful since princ$ doesn't understand the ~% directive.
  (declare (xargs :mode :program :stobjs state))
  (princ$ (concatenate 'string line (coerce '(#\Newline) 'string)) channel state))



(defun multicons (a x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (cons a (car x))
            (multicons a (cdr x)))
    nil))

;; (defun cw!-fn (str alist)
;;   ;; Has an "under the hood" implementation
;;   (declare (ignore str alist)
;;            (xargs :guard (stringp str)))
;;   (cw "Error: cw!-fn has not been redefined."))

;; (defmacro cw! (str &rest args)
;;   ;; This is like ACL2's cw function, but it uses fmt1! instead of fmt under the
;;   ;; hood.
;;   `(cw!-fn ,str ,(cons 'list (multicons 'cons
;;                          (pairlis2 `(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
;;                                    (pairlis$ args nil))))))

;; (defttag cw!)

;; (progn!
;;  (set-raw-mode t)
;;  (defun cw!-fn (str alist)
;;    (progn
;;      (fmt1! str alist 0 *standard-co* *the-live-state* nil)
;;      nil))
;;  (set-raw-mode nil))





(defstub to-flat-string-aux (x) t)

(defun to-flat-string (x)
  ;; Logically, to-flat-string is just some uninterpreted function.  I think
  ;; this is sound, since it should satisfy functional equality.
  (declare (xargs :guard t))
  (prog2$ (cw "Error: to-flat-string has not been redefined.~%")
          (to-flat-string-aux x)))

(defttag to-flat-string)

(progn!
 (set-raw-mode t)
 (defun to-flat-string (x)
   (let ((*print-circle* nil)
         (*print-escape* t)
         #+DRAFT-ANSI-CL-2 (*print-lines* nil)
         #+DRAFT-ANSI-CL-2 (*print-miser-width* nil)
         #+DRAFT-ANSI-CL-2 (*print-pprint-dispatch* nil)
         #+DRAFT-ANSI-CL-2 (*print-readably* t)
         #+DRAFT-ANSI-CL-2 (*print-right-margin* nil)
         (*readtable* *acl2-readtable*)
         (*print-case* :upcase)
         (*print-pretty* nil)
         (*print-level* nil)
         (*print-length* nil))
     (prin1-to-string x))))
