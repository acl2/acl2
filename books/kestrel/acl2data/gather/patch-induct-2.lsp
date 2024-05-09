; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file induct.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun@par load-hint-settings-into-rcnst (hint-settings rcnst
                                                        incrmt-array-name-info
                                                        wrld ctx state)

; Certain user supplied hint settings find their way into the rewrite-constant.
; They are :expand, :restrict, :hands-off, and :in-theory.  Our convention is
; that if a given hint key/val is provided it replaces what was in the rcnst.
; Otherwise, we leave the corresponding field of rcnst unchanged.

; Incrmt-array-name-info is either a clause-id, a keyword, or nil.  If it is a
; clause-id and we install a new enabled structure, then we will use that
; clause-id to build the array name, rather than simply incrementing a suffix.
; Otherwise incrmt-array-name-info is a keyword.  A keyword value should be
; used for calls made by user applications, for example in community book
; books/tools/easy-simplify.lisp, so that enabled structures maintained by the
; ACL2 system do not lose their associated von Neumann arrays.

  (er-let*@par
   ((new-ens
     (cond
      ((assoc-eq :in-theory hint-settings)
       (let* ((theory0 (cdr (assoc-eq :in-theory hint-settings)))
              (theory1 (augment-runic-theory theory0 wrld))
              (active-useless-runes (active-useless-runes state))
              (old-ens (access rewrite-constant rcnst
                               :current-enabled-structure))
              (theory

;;; This modification was necessary because of how we call useless-runes-ens
;;; directly when updating with useless-runes; see the binding of
;;; global-enabled-structure in function remove-runes-val (file
;;; remove-runes-val.lisp).

               (if active-useless-runes ;patch;
#|
               (if (and active-useless-runes

; The following two conditions are just an optimization.  If old-ens is (ens
; state), then presumably active-useless-runes was already subtracted and we
; don't need to subtract that list again.  We check the name first since that
; should be fastest: when the names are EQ, very likely the two
; enabled-structures are EQ.

                        (eq (access enabled-structure old-ens
                                    :array-name)
                            (access enabled-structure (ens state)
                                    :array-name))
                        (equal old-ens (ens state)))
|#
                   (set-difference-augmented-theories theory1
                                                      active-useless-runes
                                                      nil)
                 theory1)))
         (load-theory-into-enabled-structure@par
          :from-hint
          theory
          t
          old-ens
          (or incrmt-array-name-info t)
          nil
          wrld ctx state)))
      (t (value@par (access rewrite-constant rcnst
                            :current-enabled-structure))))))
   (value@par (change rewrite-constant rcnst
                      :rw-cache-state
                      (cond
                       ((assoc-eq :rw-cache-state hint-settings)
                        (cdr (assoc-eq :rw-cache-state hint-settings)))
                       (t (access rewrite-constant rcnst :rw-cache-state)))
                      :expand-lst
                      (cond
                       ((assoc-eq :expand hint-settings)
                        (cdr (assoc-eq :expand hint-settings)))
                       (t (access rewrite-constant rcnst :expand-lst)))
                      :restrictions-alist
                      (cond
                       ((assoc-eq :restrict hint-settings)
                        (cdr (assoc-eq :restrict hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :restrictions-alist)))
                      :fns-to-be-ignored-by-rewrite
                      (cond
                       ((assoc-eq :hands-off hint-settings)
                        (cdr (assoc-eq :hands-off hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :fns-to-be-ignored-by-rewrite)))
                      :current-enabled-structure
                      new-ens
                      :nonlinearp
                      (cond
                       ((assoc-eq :nonlinearp hint-settings)
                        (cdr (assoc-eq :nonlinearp hint-settings)))
                       (t (access rewrite-constant rcnst :nonlinearp)))
                      :backchain-limit-rw
                      (cond
                       ((assoc-eq :backchain-limit-rw hint-settings)
                        (cdr (assoc-eq :backchain-limit-rw hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :backchain-limit-rw)))
                      :case-split-limitations
                      (cond
                       ((assoc-eq :case-split-limitations hint-settings)
                        (cdr (assoc-eq :case-split-limitations
                                       hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :case-split-limitations)))))))
