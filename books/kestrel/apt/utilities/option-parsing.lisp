; Utilities for handling transformation options
;
; Copyright (C) 2016-2020 Kestrel Institute
; Copyright (C) 2016-2017, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Matt Kaufmann

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/utilities/doublets2" :dir :system)
(include-book "kestrel/utilities/messages2" :dir :system)
(include-book "std/lists/list-defuns" :dir :system) ;for repeat
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; Build an alist whose keys are exactly KEYS, where each key is bound as it is
;; in ALIST.  This can be used to sort the keys of ALIST to match the order of
;; items in KEYS.  Returns (mv nil alist) or (mv error-context msg).
(defun alist-for-keys (keys alist ctx)
  (declare (xargs :guard (and ctx
                              (true-listp keys)
                              (alistp alist))))
  (if (endp keys)
      (value-cmp nil)
    (let* ((key (first keys))
           (pair (assoc-equal key alist)))
      (if (not pair)
          (er-cmp ctx
                  "No value for key ~x0 was found in the alist ~x1."
                  key alist)
        (er-let*-cmp ((alist (alist-for-keys (rest keys) alist ctx)))
                     (value-cmp (acons key (cdr pair) alist)))))))

;; Build an alist from function names in the clique to their values of the
;; option.  Returns (mv nil alist) or (mv error-context msg).
(defund elaborate-mut-rec-option-map (option-doublets clique-members-left option-name all-clique-members ctx)
  (declare (xargs :guard (and (symbol-listp clique-members-left)
                              (symbol-listp all-clique-members)
                              ;; no guard about option-doublets because this function checks them
                              (keywordp option-name)
                              ctx)))
  (if (atom option-doublets)
      (if (not (null option-doublets))
          (er-cmp ctx
                  "The ~x0 option is not a true list."
                  option-name)
        (if clique-members-left
            (er-cmp ctx
                    "The following functions were not given a value for the ~
                     ~x0 option: ~x1."
                    option-name clique-members-left)
          (value-cmp nil))) ;empty alist
    (b* ((doublet (first option-doublets))
         ((when (not (doubletp doublet)))
          (er-cmp ctx
                  "~x0 (supplied as part of the ~x1 option) is not a doublet."
                  doublet option-name))
         (key (car doublet))
         (value (cadr doublet))
         ((when (eq :otherwise key))
          (if (rest option-doublets)
              (er-cmp ctx
                      "Error in ~x0 option: :otherwise must come last in the map"
                      option-name)
            (value-cmp (pairlis$ clique-members-left (repeat (len clique-members-left) value)))))
         ((when (not (or (symbolp key)
                         (symbol-listp key))))
          (er-cmp ctx
                  "Error in ~x0 option: The map key ~x1 is not a symbol or list of symbols"
                  option-name key))
         (keys (if (symbolp key)
                   (list key)
                 key))
         ((when (not (subsetp-eq keys all-clique-members)))
          (er-cmp ctx
                  "The following (supplied as part of the ~x0 option) are not members of the clique: ~x1"
                  option-name
                  (set-difference-eq keys all-clique-members)))
         ((when (not (subsetp-eq keys clique-members-left)))
          (er-cmp ctx
                  "The following (supplied as part of the ~x0 option) have already been given a value in the map: ~x1"
                  option-name
                  (set-difference-eq keys clique-members-left)))
         ((mv ctx msg-or-rest)
          (elaborate-mut-rec-option-map (rest option-doublets)
                                        ;; remove these keys from the list of clique members et to be bound
                                        (set-difference-eq clique-members-left keys)
                                        option-name all-clique-members ctx))
         ((when ctx)
          (mv ctx msg-or-rest)))
      (value-cmp
       (append (pairlis$ keys (repeat (len keys) value)) ;map all the keys to this value
               msg-or-rest)))))

;todo: strengthen to symbol-alistp:
(defthm alistp-of-mv-nth-1-of-elaborate-mut-rec-option-map
  (implies (and ctx1
                ;;no error:
                (null (mv-nth 0 (elaborate-mut-rec-option-map option-doublets clique-members-left option-name all-clique-members ctx1))))
           (alistp (mv-nth 1 (elaborate-mut-rec-option-map option-doublets clique-members-left option-name all-clique-members ctx1))))
  :hints (("Goal" :in-theory (enable elaborate-mut-rec-option-map))))

;; Elaborate and check OPTION-VALUE, which is a :map option, yielding an alist
;; that binds all of the CLIQUE-MEMBERS, in order.  Returns (mv nil alist) or
;; (mv error-context msg).
(defun elaborate-mut-rec-map-option (option-value option-name clique-members ctx)
  (declare (xargs :guard (and (symbol-listp clique-members)
                              ;; very weak guard about option-value because this function checks it:
                              (consp option-value)
                              (eq :map (car option-value))
                              (keywordp option-name)
                              ctx)))
  ;; TODO: Use b* once we have a b* binder for context-message pairs.
  (er-let*-cmp ((alist (elaborate-mut-rec-option-map
                        (rest option-value) ;strip off :map
                        clique-members option-name clique-members ctx))
                (alist (alist-for-keys clique-members alist ctx)))
               (value-cmp alist)))

;; Builds an alist from function names in the clique to their values of the
;; option. Returns (mv nil alist) or (mv error-context msg).
(defun elaborate-mut-rec-option (option-value option-name clique-members ctx)
  (declare (xargs :guard (and (symbol-listp clique-members)
                              ;; no guard about option-value because this function checks it:
                              (keywordp option-name)
                              ctx)
;                  :mode :program ; error1 and silent-error
                  ))
  (if (and (consp option-value)
           (eq :map (car option-value)))
      ;; :map was used:
      (elaborate-mut-rec-map-option option-value option-name clique-members ctx)
    ;; No :map was used, so all functions get the same value (possibly the default):
    (value-cmp (pairlis$ clique-members (repeat (len clique-members) option-value)))))

;; Builds an alist from function names in the clique to their values of the
;; option.
;; TODO: deprecate the other version?
(defund elaborate-mut-rec-option2 (option-value option-name clique-members ctx)
  (b* (((mv erp alist-or-msg)
        (elaborate-mut-rec-option option-value option-name clique-members ctx))
       ((when erp)
        ;; alist-or-msg is a msgp:
        (hard-error ctx (message-string alist-or-msg)
                    (message-alist alist-or-msg))
        nil))
    alist-or-msg))

;; Returns an error triple.  (Needlessly takes and returns state.)
(defun elaborate-mut-rec-option-with-state (option-value option-name clique-members ctx state)
  (declare (xargs :guard (and (symbol-listp clique-members)
                              ;; no guard about option-value because this function checks it:
                              (keywordp option-name))
                  :mode :program ; error1 and silent-error
                  :stobjs state))
  (cmp-to-error-triple (elaborate-mut-rec-option option-value option-name clique-members ctx)))
