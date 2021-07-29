; Making the "becomes theorem"
;
; Copyright (C) 2014-2021 Kestrel Institute
; Copyright (C) 2015, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)

;; Generate the name of the "becomes" theorem that replaces OLD-FN with NEW-FN.
(defun becomes-theorem-name (old-fn new-fn)
  (declare (xargs :guard (and (symbolp old-fn)
                              (symbolp new-fn))))
  (pack$ old-fn '-becomes- new-fn))

;; Makes a theorem equating an arbitrary call of FN with a call of NEW-FN on the same arguments.
;; REC is either nil (function is non-recursive), :single, or :mutual.
;; TODO: Improve this to use the $not-normalized rules if indicated for fn and/or new-fn (add options for this)
(defun make-becomes-theorem (fn ; name of the old function
                             new-fn ; name of the new function (must have the same params)
                             rec ; nil (for non-recursive), :single, or :mutual
                             thm-enable ;whether the "becomes theorem" should be enabled
                             enables ; rules to always enable in the proof ; drop??
                             state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp fn)
                              (symbolp new-fn)
                              (member-eq rec '(nil :single :mutual))
                              (booleanp thm-enable)
                              (true-listp enables))))
  (let ((formals (fn-formals fn (w state)))
        (defthm-variant (if thm-enable 'defthm 'defthmd)))
    `(,defthm-variant ,(becomes-theorem-name fn new-fn)
       (equal (,fn ,@formals)
              (,new-fn ,@formals))
       :hints ,(if (eq rec :mutual) ;weird format for make-flag hints:
                   `('(:in-theory (append '(,fn ,new-fn ,@enables) (theory 'minimal-theory))
                                  :expand ((,fn ,@formals)
                                           (,new-fn ,@formals))))
                 (if (eq rec :single)
                     `(("Goal" :induct (,fn ,@formals)
                        :do-not '(generalize eliminate-destructors)
                        :in-theory (append '(,fn ,new-fn ,@enables) (theory 'minimal-theory))))
                   `(("Goal" :in-theory (append '(,fn ,new-fn ,@enables)
                                                (theory 'minimal-theory) ;TODO: use nil?
                                                )))))
       ,@(and (eq rec :mutual) (list :flag fn)))))
