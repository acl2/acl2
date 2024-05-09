; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "kestrel/helpers/advice-code-only" :dir :system :ttags :all)

(program)
(set-state-ok t)

(table advice-server :leidos-run10.0
       '("https://proof.kestrel.edu/machine_interface"
         "Leidos_run10_0"))

;;; As per Eric Smith:
#|
;; Calpoly models:
(table advice-server :calpoly '("https://proof.kestrel.edu/machine_interface" "kestrel-calpoly"))
(table advice-server :calpoly-run10.0 '("https://proof.kestrel.edu/machine_interface" "calpoly-run10.0"))
(table advice-server :calpoly-run10.1 '("https://proof.kestrel.edu/machine_interface" "calpoly-run10.1"))
(table advice-server :calpoly-run10.0-with-goal '("https://proof.kestrel.edu/machine_interface" "calpoly-run10.0-with-goal"))
;; (table advice-server :calpoly-run10.1-with-goal '("https://proof.kestrel.edu/machine_interface" "calpoly-run10.1-with-goal"))
(table advice-server :plur '("http://osprey.kestrel.edu:80/machine_interface" "plur"))
(table advice-server :plur-ablated '("http://osprey.kestrel.edu:80/machine_interface" "plur-ablated"))
;; Leidos models:
(table advice-server :leidos '("https://proof.kestrel.edu/machine_interface" "Leidos")) ; note the capital L
(table advice-server :leidos-run10.0 '("https://proof.kestrel.edu/machine_interface" "Leidos_run10_0")) ; capital L and underscores
(table advice-server :leidos-run10.1 '("https://proof.kestrel.edu/machine_interface" "Leidos_run10_1")) ; capital L and underscores
(table advice-server :leidos-gpt '("https://proof.kestrel.edu/machine_interface" "leidos-gpt"))
|#

(defun advice-recs-1 (top-level-checkpoint-list
                      under-induction-checkpoint-list
                      ubody uhints otf-flg time-limit state)
  (help::all-successful-actions-for-checkpoints
   top-level-checkpoint-list
   under-induction-checkpoint-list
   ubody
   uhints
   otf-flg ; !! Maybe should be nil.
   10      ; num-recs-per-model
   (let ((info (f-get-global 'certify-book-info state)))
     (and info
          (sysfile-to-filename (access certify-book-info info :full-book-name)
                               state)))
   t   ; improve-recsp
   nil ; print
;  "https://proof.kestrel.edu/itueotwhskbfkjdgs/machine_interface" ; server-url
   (help::make-model-info-alist '(:LEIDOS-RUN10.0) (w state))
   nil ; debug
   nil ; step-limit
   time-limit
; disallowedrec-types:-
;  '(:add-hyp :exact-hints) ; disallowed-rec-types
;   '(:CALPOLY-RUN10.0) ; for one day, started when Eric says he's ready
;   '(:ENABLE :HISTORY) ; for one day
; Here is what was used for tests/results-advice/:
#+skip
   '(:ENABLE :HISTORY :CALPOLY :LEIDOS
             ;; :LEIDOS-GPT
             )
   nil
   state))

(defun extend-acl2data-alist-entry-with-recs (entry recs)
  (append entry (list recs)))

(defun deconstruct-broken-defthm (x)
  (case-match x
    (('defthm & ubody . rest)
     (assert$ (keyword-value-listp rest)
              (mv ubody
                  (cadr (assoc-keyword :hints rest))
                  (cadr (assoc-keyword :otf-flg rest)))))
    (& (mv (er hard 'deconstruct-broken-defthm
               "Unexpected form, ~x0"
               x)
           nil nil))))

(defun advice-recs-2 (tterm alist time-limit state)

; Tterm is the translated term whose various proofs are being attempted.  Alist
; is the alist associated with :HINT-SETTING-ALIST in a __acl2data.out file.
; Here is an example of an alist entry (for event APP-ASSOC-REWRITE from file
; test2__acl2data.out.saved in the PEARLS repository, directory
; acl2/acl2data/).

#|
 ((:ENABLE APPEND)
  (((EQUAL (BINARY-APPEND (BINARY-APPEND X Y) Z)
           (BINARY-APPEND X (BINARY-APPEND Y Z)))))
  ((EQUAL (APPEND (APPEND X Y) Z)
          (APPEND X Y Z)))
  NIL NIL
  (DEFTHM APP-ASSOC-REWRITE
    (EQUAL (APPEND (APPEND X Y) Z)
           (APPEND X Y Z))
    :HINTS (("Goal" :IN-THEORY (ENABLE CAR-CONS NTH)))))
|#

; This entry was produced by function remove-hint-setting-checkpoints from the
; book remove-hint-setting-checkpoints.lisp in that same directory.  Inspection
; of function rmh-checkpoints-2 in that book shows us that the entry above has
; the following form.

#|
 (removed-hint-representation
  top-level-clause-list/translated
  top-level-clause-list/untranslated
  under-induction-clause-list/translated
  under-induction-clause-list/untranslated
  broken-theorem)
|#

; But we see two other forms there, where the list is shorter and the cadr is
; either :FAIL or :REMOVE.

; We return an extension of alist that contains an extra field for
; recommendations, or :NONE when we don't get a result from the advice tool,
; generally because we don't ask for one in the case of :REMOVE.

; In other than the :REMOVE case, we use top-level checkpoints and the
; induction checkpoints, else the original term as a list of top-level checkpoints.
; A special case is when the top-level checkpoints, i.e., the top level list of
; checkpoint lists, is ((<GOAL>)).  We replace that with ((tterm)) where tterm
; is the translated term to be proved.

  (cond
   ((endp alist) (value nil))
   (t
    (b* (;; Avoid the following,  because b* is brought in by including
         ;; kestrel/helpers/advice-code-only, not the usual std/util/bstar, and
         ;; hence patbind-er isn't defined.
         ;; ((er rest) (advice-recs-2 tterm (cdr alist) time-limit state))
         ((mv erp rest state) (advice-recs-2 tterm (cdr alist) time-limit state))
         ((when erp) (mv erp rest state))
         (entry (car alist))
         (top-level-clause-list (cadr entry))
         ((when (eq top-level-clause-list :remove))
          (value (cons entry rest)))
         (top-level-clause-list (if (or (eq top-level-clause-list :fail)
                                        (equal top-level-clause-list '((<GOAL>))))
                                    (list (list tterm))
                                    top-level-clause-list))
         (under-induction-clause-list (cadddr entry))
         (broken-defthm (car (last entry)))
         ((mv ubody uhints otf-flg)
          (deconstruct-broken-defthm broken-defthm))
         ((mv erp recs state) ; (er recs) -- see comment above about patbind-er
          (advice-recs-1 top-level-clause-list
                         under-induction-clause-list
                         ubody uhints otf-flg time-limit state))
         ((when erp)
          (mv erp recs state)))
      (value (cons (extend-acl2data-alist-entry-with-recs entry recs)
                   rest))))))

(defun advice-recs (tterm alist time-limit state)

; See advice-recs-2.

  (mv-let (erp val state)
    (advice-recs-2 tterm alist time-limit state)
    (value (and (null erp) val))))
