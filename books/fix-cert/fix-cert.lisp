(in-package "ACL2")

; fix-cert.lisp - Written by Peter Dillinger
; Copyright (C) 2007-2009 Northeastern University

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

(program)
(set-state-ok t)


;==========================================================================
; Code to create empty packages from those in a .cert file, so that it can
; be read.

; ch is in the middle of reading portcullis commands
(defun create-pkgs-for-cert-file1 (file1 file2 ch
                                         known-pkgs new-pkgs-sofar
                                         ctx state)
  (mv-let
   (eofp cmd state)
   (state-global-let* ((infixp nil)) (read-object ch state))
   (cond (eofp
          (er soft ctx *ill-formed-certificate-msg* file1 file2))
         ((eq cmd :end-portcullis-cmds)
          (value new-pkgs-sofar))
         ((and (consp cmd)
               (eq (car cmd) 'defpkg)
               (consp (cdr cmd))
               (stringp (cadr cmd)))
          (let ((pkg (cadr cmd)))
            (if (member-equal pkg known-pkgs)
              (create-pkgs-for-cert-file1 file1 file2 ch known-pkgs
                                          new-pkgs-sofar ctx state)
              (er-progn
               (defpkg-fn pkg nil state nil nil
                 `(defpkg ,pkg nil))
               (create-pkgs-for-cert-file1 file1 file2 ch known-pkgs
                                           (cons pkg new-pkgs-sofar)
                                           ctx state)))))
         (t 
          (create-pkgs-for-cert-file1 file1 file2 ch known-pkgs
                                      new-pkgs-sofar ctx state)))))
  
(defun set-current-package1 (val state)
  (mv-let (erp v state)
          (set-current-package val state)
          (declare (ignore v erp))
          state))


(defconst *fix-cert-suspect-book-action-alist*
  '((:uncertified-okp . nil)
    (:defaxioms-okp . t)
    (:skip-proofs-okp . t)))

(defun create-pkgs-for-cert-file (file1 ctx state)
  (let ((file2 (convert-book-name-to-cert-name file1)))
    (mv-let
     (ch state)
     (open-input-channel file2 :object state)
     (if (null ch)
       (include-book-er file1 file2
                        "There is no certificate on file for ~x0."
                        :uncertified-okp
                        *fix-cert-suspect-book-action-alist*
                        ctx state)
       (er-let*
         ((pkg 
           (state-global-let*
            ((infixp nil))
            (chk-in-package ch file2 ctx state))))
         (if (not (equal pkg "ACL2"))
           (er soft ctx *ill-formed-certificate-msg* file1 file2)
           (state-global-let*
            ((current-package "ACL2" set-current-package1))
            (mv-let (error-flg val state)
                    (mv-let
                     (eofp version state)
                     (state-global-let* ((infixp nil))
                                        (read-object ch state))
                     (if (or eofp (not (stringp version)))
                       (er soft ctx *ill-formed-certificate-msg*
                           file1 file2)
                       (mv-let
                        (eofp key state)
                        (state-global-let* ((infixp nil))
                                           (read-object ch state))
                        (if (or eofp (not (eq key :begin-portcullis-cmds)))
                          (er soft ctx *ill-formed-certificate-msg*
                              file1 file2)
                          (create-pkgs-for-cert-file1
                           file1 file2 ch
                           (strip-cars (known-package-alist state))
                           nil ctx state)))))
                    (pprogn (close-input-channel ch state)
                            (mv error-flg val state))))))))))


;==========================================================================
; Code for actually fixing certificate files based on their new location.

(defun fix-cert-fn (user-book-name dir ctx state)
  ;; user-book-name and dir are as given by a user to include-book
  (er-let*
    ((dir-value
      (cond (dir (include-book-dir-with-chk soft ctx dir))
            (t (value (cbd))))))
    (mv-let
     (new-full-book-name new-directory-name-with-slash new-familiar-name)
     (parse-book-name
       dir-value
       (prog2$ (cw "~%Fixing .cert file for ~x0~%" user-book-name)
               user-book-name)
       ".lisp" state)
     (declare (ignorable new-directory-name-with-slash new-familiar-name))
     (er-let*
      ((new-pkg-lst (create-pkgs-for-cert-file new-full-book-name ctx state))
       (cert-obj (chk-certificate-file new-full-book-name t ctx state
                                       *fix-cert-suspect-book-action-alist* nil)))
      (let* ((portcullis (cons (access cert-obj cert-obj :cmds)
                               (access cert-obj cert-obj :pre-alist)))
             (post-alist (access cert-obj cert-obj :post-alist))
             (expansion-alist (access cert-obj cert-obj :expansion-alist))
             (old-full-book-name (caar post-alist))
             (old-directory-name (remove-after-last-directory-separator
                                  old-full-book-name))
             (new-directory-name (remove-after-last-directory-separator
                                  new-full-book-name)))
        (if (equal old-full-book-name new-full-book-name)
            (value :not-needed)
          (make-certificate-file-relocated
                 new-full-book-name portcullis
                 (convert-book-name-to-cert-name new-full-book-name)
                 post-alist expansion-alist
                 old-directory-name new-directory-name
                 ctx state)))))))

; Beware that in order to create packages before they are needed,
; the order of the books to be fixed needs to satisfy the dependencies.

(defun fix-certs-fn (user-book-names dir ctx state)
  (if (not (consp user-book-names))
    (if (stringp user-book-names)
      (fix-cert-fn user-book-names dir ctx state)
      (value :done))
    (mv-let (er-flag val state)
            (fix-cert-fn (car user-book-names) dir ctx state)
            (declare (ignore er-flag val))
            (fix-certs-fn (cdr user-book-names) dir ctx state))))

(defmacro fix-cert (user-book-name-or-lst &key dir)
  `(fix-certs-fn
    ,(if (quotep user-book-name-or-lst)
       user-book-name-or-lst
       `',user-book-name-or-lst)
    ',dir
    'fix-cert
    state))
