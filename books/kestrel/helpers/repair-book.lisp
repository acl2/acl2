; A tool to suggest repairs for broken proofs
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: Working prototype

;; SETUP:
;;
;; 1. To enable repairs based on information saved during successful proofs,
;; turn on saving of event data during certification by setting the value of
;; the ACL2_WRITE_EVENT_DATA environment variable to "t".
;;
;; Example: export ACL2_WRITE_EVENT_DATA=t
;;
;; To maximize the benefit of this change, recertify all books after setting
;; ACL2_WRITE_EVENT_DATA.
;;
;; 2. To cause repairs to be attempted automatically whenever cert.pl fails to
;; certify a book, set the ON_FAILURE_CMD environment variable to the location
;; of the repair-book-from-cert-pl.sh script in this books/kestrel/helpers/
;; directory.
;;
;; Example: export ON_FAILURE_CMD=~/acl2/books/kestrel/helpers/repair-book-from-cert-pl.sh

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Add support for repairs that involve failures to translate
;; terms/hints/etc. possibly due to missing names.

;; TODO: Add support for determining what changed (e.g., by doing a git diff).

;; TODO: When searching for all failed books, handle cert.pl output that is directed to another dir.

;; TODO: Make a repair-book-code-only

(include-book "std/util/bstar" :dir :system)
(include-book "replay-book-helpers")
(include-book "find-failed-books")
(include-book "advice-code-only") ; or make a repair-book-code-only
;(include-book "system/pseudo-good-worldp" :dir :system) ;for pseudo-runep; reduce?
(include-book "kestrel/world-light/defthm-or-defaxiom-symbolp" :dir :system)
(include-book "kestrel/world-light/defined-functionp" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system) ; reduce?
(include-book "kestrel/utilities/ld-history" :dir :system)
(include-book "kestrel/utilities/maybe-add-dot-lisp-extension" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/split-path" :dir :system)
(include-book "kestrel/utilities/extend-pathname-dollar" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)

;dup in books/system/pseudo-good-worldp
(defun pseudo-runep (rune)
  (and (consp rune)
       (keywordp (car rune))
       (consp (cdr rune))
       (symbolp (cadr rune))
       (or (null (cddr rune))
           (natp (cddr rune)))))
(verify-guards pseudo-runep)

;; todo: what is :fake-rune-for-cert-data?
(defun fake-rule-classp (rule-class)
  (declare (xargs :guard (keywordp rule-class)))
  (member-eq rule-class (strip-cars *fake-rune-alist*)))

(defconst *high-confidence* 20)
(defconst *medium-confidence* 10)
(defconst *low-confidence* 5)
(defconst *very-low-confidence* 3)

;; Makes recommendations for a rune that fired only in the old proof.
;; TODO: Figure out which exact event failed (what if not at top level)?
;; TODO: Actually try the suggestions, and provide new hints for the event.
;; todo: look at other things about the proof, not just the runes...
;; todo: instead of printing here, accumulate a list of notes to print if no repair works
(defun recs-for-old-rune (rune counter state)
  (declare (xargs :guard (natp counter)
                  :verify-guards nil ; todo
                  :stobjs state))
  (if (not (pseudo-runep rune))
      (er hard? 'recs-for-old-rune "Bad old rune: ~x0." rune)
    (let ((rule-class (first rune))
          (name (second rune)) ; todo: consider corollaries (what if they have changed?)
          )
      (if (fake-rule-classp rule-class)
          nil ; not much to do here, I guess (e.g., if linear was used before but not now, what can we do?)
        (if (eq rule-class :induction)
            ;; An :induction rule was used in the old proof but not in the new proof.  The rule is very likely needed in the new proof.
            (if (not (or (function-symbolp name (w state)) ; todo think about this
                         (defthm-or-defaxiom-symbolp name (w state))))
                (prog2$ (cw "Note: Induction rule ~x0 is no longer present (was used for induction in old proof)!~%" name) ; todo: go find it
                        nil)
              (if (not (enabled-runep rune (ens state) (w state))) ;; todo: of course, a hint might enable the rune!  check for that
                  ;; todo: see if some other :induction was chosen instead
                  (prog2$ (cw "(Rune ~x0 did not fire.)~%" rune)
                          nil)
                ;; todo: maybe even put in and :induct hint?
                (list (help::make-rec (concatenate 'string "repair" (acl2::nat-to-string counter)) :add-enable-hint name *high-confidence* nil))))
          (if (eq rule-class :definition)
              (if (not (or (function-symbolp name (w state)) ; todo think about this
                           (defthm-or-defaxiom-symbolp name (w state))))
                  (prog2$ (cw "Note: Function or rule ~x0 is no longer present!~%" name)
                          nil)
                (if (not (enabled-runep rune (ens state) (w state))) ;; todo: of course, a hint might enable the rune!  check for that
                    (list (help::make-rec (concatenate 'string "repair" (acl2::nat-to-string counter)) :add-enable-hint name ; todo: would like to use rune, here and elsewhere
                                          *medium-confidence* nil))
                  ;; present and enabled but did not fire:
                  (prog2$ (cw "(Rune ~x0 did not fire.)~%" name)
                          nil)))
            (if (or (eq rule-class :rewrite)
                    (eq rule-class :linear)) ; todo: what else?!
                (if (not (defthm-or-defaxiom-symbolp name (w state))) ; todo: what about corollaries?
                    (prog2$ (cw "Note: Rule ~x0 is no longer present!~%" rune) ; todo: go find it
                            nil)
                  ;; It does exist:
                  (if (enabled-runep rune (ens state) (w state)) ;; todo: of course, a hint might enable the rune!  check for that
                      (prog2$ (cw "(Rune ~x0 did not fire.)~%" rune)
                              nil)
                    (list (help::make-rec (concatenate 'string "repair" (acl2::nat-to-string counter)) :add-enable-hint name *medium-confidence* nil))))
              (if (eq rule-class :executable-counterpart)
                  (if (not (or (function-symbolp name (w state)) ; todo think about this
                               (defthm-or-defaxiom-symbolp name (w state))))
                      (prog2$ (cw "Note: Function or rule ~x0 is no longer present!~%" name)
                              nil)
                    (if (not (enabled-runep rune (ens state) (w state))) ;; todo: of course, a hint might enable the rune!  check for that
                        (list (help::make-rec (concatenate 'string "repair" (acl2::nat-to-string counter)) :add-enable-hint name ; todo: would like to use rune, here and elsewhere
                                              *low-confidence* nil))
                      ;; present and enabled but did not fire:
                      (prog2$ (cw "(Rune ~x0 did not fire.)~%" name)
                              nil)))
                (if (eq rule-class :type-prescription)
                    (if (not (or (function-symbolp name (w state)) ; todo think about this
                                 (defthm-or-defaxiom-symbolp name (w state)))) ;todo: think about this
                        (prog2$ (cw "Note: Rule ~x0 is no longer present!~%" rune)
                                nil)
                      (if (not (enabled-runep rune (ens state) (w state))) ;; todo: of course, a hint might enable the rune!  check for that
                          (list (help::make-rec (concatenate 'string "repair" (acl2::nat-to-string counter)) :add-enable-hint name ; todo: would like to use rune, here and elsewhere
                                                *low-confidence* nil))
                        ;; present and enabled but did not fire:
                        (prog2$ (cw "(Rune ~x0 did not fire.)~%" name)
                                nil)))
                  nil)))))))))

;; Returns (mv recs counter).
(defun recs-for-old-runes (old-runes counter acc state)
  (declare (xargs :guard (and (true-listp old-runes)
                              (natp counter))
                  :verify-guards nil ; todo
                  :stobjs state))
  (if (endp old-runes)
      (mv (reverse acc) counter)
    (let ((recs-for-old-rune (recs-for-old-rune (first old-runes) counter state)))
      (recs-for-old-runes (rest old-runes) (+ counter (len recs-for-old-rune)) (append recs-for-old-rune acc) state))))

;todo: combine all the recs found by examining event-data
(defun recs-for-new-rune (rune counter)
  (declare (xargs :guard (natp counter)))
  (if (not (pseudo-runep rune))
      (er hard? 'recs-for-new-rune "Bad new rune: ~x0." rune)
    (let ((rule-class (first rune))
          (name (second rune)) ; todo: consider corollaries (what if they have changed?)
          )
      (if (or (eq rule-class :rewrite)
              (eq rule-class :linear)) ; todo: what else?!
          (list (help::make-rec (concatenate 'string "repair" (acl2::nat-to-string counter)) :add-disable-hint name *low-confidence* nil))
        (if (eq :definition rule-class)
            (list (help::make-rec (concatenate 'string "repair" (acl2::nat-to-string counter)) :add-disable-hint name *medium-confidence* nil))
          (if (eq :type-prescription rule-class)
              (list (help::make-rec (concatenate 'string "repair" (acl2::nat-to-string counter)) :add-disable-hint name *very-low-confidence* nil))
            ;todo: more rule-classes
            nil))))))

;; Returns (mv recs counter).
(defun recs-for-new-runes (new-runes counter acc)
  (declare (xargs :guard (and (true-listp new-runes)
                              (natp counter))
                  :verify-guards nil ; todo
                  ))
  (if (endp new-runes)
      (mv (reverse acc) counter)
    (let ((recs-for-new-rune (recs-for-new-rune (first new-runes) counter)))
      (recs-for-new-runes (rest new-runes) (+ counter (len recs-for-new-rune)) (append recs-for-new-rune acc)))))

;; Try to remove from the front of EVENT-DATA-FORMS all the forms corresponding to the NAMES.
(defun consume-event-data-forms (names event-data-forms)
  (if (endp names)
      event-data-forms
    (if (or (eq :none event-data-forms)
            (if (null event-data-forms)
              ;; we've been told to consume some forms but there are none left (perhaps there is a new theorem at the end of the book)
                (prog2$ (cw "Warning: No more event data forms.~%")
                        t)
              nil))
        event-data-forms
      (let ((name (first names)))
        (if (not (and (consp event-data-forms) (eq name (car (first event-data-forms)))))
          ;; todo: do something better here?  try to resychronize?
            (er hard? 'consume-event-data-forms "Bad event-data forms (expected forms for these names: ~X01): ~X23." names nil event-data-forms nil)
          (consume-event-data-forms (rest names) (rest event-data-forms)))))))

;; Tries to repair the failing EVENT.
;; Currently only for defthm events
;; Returns (mv remaining-event-data-forms state).
(defun repair-event-with-event-data (event new-event-data-alist event-data-forms state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* (((when (not (and (consp event) (member-eq (car event) '(defthm defthmd))))) ; todo: generalize
        (cw "WARNING: Can only repair defthms.  Skipping ~x0~%" event) ; todo: track whether we ignored anything
        ;; Even though we can't repair it, we consume any event-data-forms that came from this event, to
        ;; try to keep things in sync:
        (let ((names-with-event-data (strip-cars new-event-data-alist)))
          (mv (consume-event-data-forms names-with-event-data event-data-forms) state)))
       ;; It's a defthm (of some kind):
       (name (cadr event)) ;todo gen
       (body (caddr event)) ;todo gen
       (translated-theorem-body (acl2::translate-term body 'repair-event-with-event-data (w state)))
       ;; Grab the checkpoints (generated by the proof attempt already done):
       ((mv erp checkpoint-clauses-top checkpoint-clauses-non-top)
        (help::checkpoints-for-failed-proof name translated-theorem-body state))
       ((when erp) (let ((names-with-event-data (strip-cars new-event-data-alist)))
                     (mv (consume-event-data-forms names-with-event-data event-data-forms) state)))  ; todo: throw an error?
       (- (cw "~%(Failed Event: ~x0~%" name)) ; print better?
       ;; Get recommendations that come from the event-data:
       ((mv recs-from-event-data remaining-event-data-forms)
        (if (eq :none event-data-forms)
            (mv nil event-data-forms)
          (b* (((when (not (consp event-data-forms)))
                (cw "Error: No more event data.~%") ; todo: throw an error? ;todo: can still attempt some repairs (e.g., using advice)
                (mv nil nil))
               (event-data-form (first event-data-forms)) ; we assume they are in sync and also that this is not a compound event (todo)
               ((when (not (and (eq name (car event-data-form)))))
                (cw "Error: No event data for ~x0." name) ; todo: throw an error?
                ;; todo: do better: try to skip some forms while looking for name?
                (mv nil event-data-forms) ; maybe the theorem is brand new and there just is no event-data for it yet
                )
               ;; Normal case:
               (remaining-event-data-forms (consume-event-data-forms (list name) event-data-forms)) ; why not just cdr (since it was a defthm, we can consume a single event-data-form)?
               (new-event-data (car (cdr (assoc-equal name new-event-data-alist)))) ; why the car?
               (old-event-data (cdr event-data-form))
               ;; (- (cw "New event data: ~x0.~%" new-event-data))
               ;; (- (cw "Old event data: ~x0.~%" old-event-data))
               (new-runes (get-event-data-1 'rules new-event-data))
               (old-runes (get-event-data-1 'rules old-event-data))
               (new-only-runes (set-difference-equal new-runes old-runes))
               (old-only-runes (set-difference-equal old-runes new-runes))
               (counter 0)
               ((mv recs-for-old-runes counter) (recs-for-old-runes old-only-runes counter nil state))
               ((mv recs-for-new-runes & ;counter
                    ) (recs-for-new-runes new-only-runes counter nil)))
            (mv (append recs-for-old-runes recs-for-new-runes)
                remaining-event-data-forms))))
       (sorted-recs (help::merge-sort-recs-by-confidence recs-from-event-data))
       (max-wins 10)
       ;; (- (cw "Will try ~x0 recs: ~X12.~%" (len sorted-recs) sorted-recs nil))
       ((mv erp successful-recs extra-recs-ignoredp state)
        (help::try-recommendations sorted-recs
                                   nil ; no book to avoid (for now) ;todo: current-book-absolute-path
                                   nil ; avoid-current-bookp ; todo
                                   name body
                                   (cadr (assoc-keyword :hints (cdddr event)))
                                   (cadr (assoc-keyword :otf-flg (cdddr event)))
                                   nil ; todo step-limit
                                   nil ; todo time-limit
                                   max-wins
                                   t ;improve-recsp
                                   nil ; print
                                   nil state))
       (print t)
       ((when erp)
        (er hard? 'repair-event-with-event-data "Error trying recommendations: ~x0" erp)
        (mv nil state))
       ;; todo: this is copied from the advice tool (factor out?):
       ;; Remove duplicates:
       (successful-recs-no-dupes (help::merge-successful-recs-into-recs successful-recs nil))
       ;; (removed-count (- (len successful-recs) (len successful-recs-no-dupes)))
       ;; (- (and (posp removed-count)
       ;;         (acl2::print-level-at-least-tp print)
       ;;         (cw "~%NOTE: ~x0 duplicate ~s1 removed.~%" removed-count
       ;;             (if (< 1 removed-count) "successful recommendations were" "successful recommendation was"))))
       (num-successful-recs (len successful-recs-no-dupes))
       (- (and extra-recs-ignoredp ;;max-wins-reachedp
               (acl2::print-level-at-least-tp print)
               (cw "~%NOTE: Search stopped after finding ~x0 successful ~s1.~%" max-wins (if (< 1 max-wins) "recommendations" "recommendation"))))
       ;; Sort the recs:
       (sorted-successful-recs (help::merge-sort-recs-by-quality successful-recs-no-dupes))
       ;; Show the successful recs:
       ;todo: improve printing
       (state (if (posp num-successful-recs)
                  (if print
                      (progn$ (if (< 1 num-successful-recs)
                                  (cw "~%REPAIRS FOR ~x0:~%" name)
                                (cw "~%REPAIR FOR ~x0:~%" name))
                              (progn$ ;; (cw "~%SUCCESSFUL RECOMMENDATIONS:~%")
                                (let ((state (help::show-successful-recommendations sorted-successful-recs nil state))) ; why does this return state?
                                  state)))
                    state)
                (progn$ ; (and print (cw "~%NO REPAIR FOUND~%~%"))
                        state)))
       ;; If we found a repair based on event-data, stop:
       ((when (posp num-successful-recs))
        (cw ")~%")
        (mv remaining-event-data-forms state))
       ;; Now try the Proof Advice tool:
       ((mv erp successp
            & ; best-rec ; todo: use this? better yet, pass print nil to best-rec-for-checkpoints but have it return all successful recs, for printing
            state)
        (help::best-rec-for-checkpoints checkpoint-clauses-top
                                        checkpoint-clauses-non-top
                                        name
                                        body
                                        (cadr (assoc-keyword :hints (cdddr event)))
                                        (cadr (assoc-keyword :otf-flg (cdddr event)))
                                        event ;broken-theorem
                                        10 ; num-recs-per-model
                                        nil ; todo: current-book-absolute-path
                                        nil ; todo: avoid-current-bookp
                                        t ; improve-recsp
                                        t ; print ; todo: print nil is not fully respected
                                        (help::make-model-info-alist :all (w state))
                                        60 ; timeout
                                        nil ; debug
                                        help::*step-limit*
                                        help::*time-limit*
                                        nil ; disallowed-rec-types
                                        10 ;max-wins
                                        t ; start-and-return
                                        state))
       ((when erp) (mv remaining-event-data-forms state)) ; todo: throw a hard error?
       (- (and print (not successp) (cw "~%NO REPAIR FOUND~%~%")))
       (- (cw ")~%")))
    (mv remaining-event-data-forms state)))

;; todo: generalize and move
(defun name-already-definedp (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (or (function-symbolp name wrld)
      (defthm-or-defaxiom-symbolp name wrld)))

;; TODO: If event-data gets out of sync, look for any event data for the given name (perhaps count occurrences of each name as we go?)
;; Returns (mv erp state).  TODO: What does the ERP really mean here?
(defun repair-events-with-event-data (events event-data-forms
                                             book-path ; just used to print messages
                                             state)
  (declare (xargs :guard (and (true-listp events)
                              (or (true-listp event-data-forms)
                                  (or (eq :none event-data-forms)))
                              (stringp book-path))
                  :stobjs state
                  :mode :program))
  (if (endp events)
      (if (consp event-data-forms)
          (prog2$ (cw "Warning: Extra event-data forms: ~x0." event-data-forms)
                  (mv :extra-event-forms state))
        (progn$ nil ; todo: print warning if no failure found
                (mv nil state)))
    (b* ((event (first events))
         ((when (and (consp event)
                     (member-eq (car event) '(defthm defthmd defun defund defaxiom)) ; todo: generalize
                     (symbolp (cadr event))
                     (name-already-definedp (cadr event) (w state))))
          (cw "~%~%*** NAME CLASH on ~x0 in ~s1.  ABORTING REPAIR ATTEMPT.~%~%~%" (cadr event) book-path)
          (mv nil state))
         ;; Clear event-data:
         (state (f-put-global 'event-data-fal nil state))
         ;; Submit the event, saving event-data:
         ((mv erp state) (submit-event-core `(saving-event-data ,event) nil state)) ; todo: make this even quieter
         ;; Event-data for this event:
         (new-event-data-alist (reverse (true-list-fix (f-get-global 'event-data-fal state)))) ; true-list-fix needed because the final cdr is 'event-data-fal
         )
      (if erp
          ;; this event failed, so attempt a repair:
          (b* ((- (cw "Event ~x0 failed.~%" event))
               ;; TODO: Consider submitting it again with :print t.
               ((mv event-data-forms state) (repair-event-with-event-data event new-event-data-alist event-data-forms state))
               ;; Submit the event with skip-proofs so we can continue:
               ((mv erp state) (submit-event-core `(skip-proofs ,event) nil state)) ; todo: make this even quieter
               ((when erp) (mv erp state)))
            (repair-events-with-event-data (rest events) event-data-forms book-path state))
        ;; this event succeeded, so continue:
        (b* ((- (cw "Event ~x0 succeeded.~%" event))
             (names-with-event-data (strip-cars new-event-data-alist))
             ;; (- (cw "~x0 Event-data forms generated: ~x1.~%" (len names-with-event-data) names-with-event-data))
             ;; (- (cw "~x0 saved event-data forms left.~%" (len event-data-forms)))
             (event-data-forms (consume-event-data-forms names-with-event-data event-data-forms)))
          (repair-events-with-event-data (rest events) event-data-forms book-path state))))))

;todo: support :dir arg?
;; Returns (mv erp result state).
(defun repair-book-fn (book-path state)
  (declare (xargs :mode :program
                  :stobjs state))
  ;; Call LD on the book while saving event-data:
  (b* (;; Remove the .cert extension if present:
       (book-path (strip-suffix-from-string ".cert" book-path))
       ;; Add .lisp extension:
       (book-path (maybe-add-dot-lisp-extension book-path))
       ;; Check that the book exists:
       ((mv book-existsp state) (file-existsp book-path state))
       ((when (not book-existsp))
        (er hard? 'repair-book-fn "The book ~x0 does not exist." book-path)
        (mv :book-does-not-exist nil state))
       ;; We set the CBD so that the book is replayed in its own directory:
       ((mv dir &) (split-path book-path))
       ((mv erp & state) (set-cbd-fn dir state))
       ((when erp) (mv erp nil state))
       (state (widen-margins state))
       ;; Start repairing
       (- (cw "~%~%(REPAIRING ~s0~%" book-path))
       ;; Load the .port file (may be help resolve #. constants [and packages?] in read-objects-from-book):
       (state (load-port-file-if-exists (remove-lisp-suffix book-path t) state))
       ;; Read all the forms in the book:
       ((mv erp events state)
        (read-objects-from-book book-path state))
       ((when erp) (cw "Error: ~x0.~%" erp) (mv erp nil state))
       ;; (- (cw "Book contains ~x0 forms.~%" (len events)))
       ;; Read the saved event data:
       (event-data-file-path (concatenate 'string (remove-lisp-suffix book-path t) "@event-data.lsp"))
       ((mv event-data-existsp state) (file-existsp event-data-file-path state))
       ((mv erp event-data-forms state)
        (if event-data-existsp
            (read-objects-from-file-with-pkg event-data-file-path "ACL2" state)
          (prog2$ (cw "WARNING: ~s0 does not exist.  Skipping repairs based on saved event-data.~%" event-data-file-path)
                  (mv nil :none state))))
       ((when erp) (cw "Error (~x0) reading: ~x1.~%" erp event-data-file-path) (mv erp nil state))
       (- (cw "(~x0 event data forms for ~s1.)~%" (len event-data-forms) book-path))
       ;; Walk through the book and the event-data-forms in sync:
       ((mv erp state) (repair-events-with-event-data events event-data-forms book-path state))
       ((when erp) (mv erp nil state))
       (- (cw "Done repairing ~s0)~%" book-path))
       (state (unwiden-margins state))
       ;; ;; todo: this still print stuff:
       ;; (state (submit-event-quiet `(saving-event-data (ld ,book-path)) state)) ; todo: make this even quieter
       ;; (most-recent-failed-theorem (acl2::most-recent-failed-command acl2::*theorem-event-types* state))
       )
    (mv nil '(value-triple :invisible) state)
    ;; (prog2$
    ;;   (cw "~%~%Failure seems to be in ~x0.~%" most-recent-failed-theorem)
    ;;   ;; Compute the runes diffs for the failed event:
    ;;   (mv-let (erp old-and-new-runes state)
    ;;     (runes-diff-fn book-path nil nil nil 'runes-diff
    ;;                    state)
    ;;     (declare (ignore erp))
    ;;     (let ((old-runes (second (assoc-eq :old old-and-new-runes)))
    ;;           (new-runes (second (assoc-eq :new old-and-new-runes))))
    ;;       (progn$ (cw "~%~%BEST REPAIR SUGGESTIONS:~%") ; todo: figure out which event failed and print its name here?
    ;;               (print-info-on-old-runes old-runes :major state)
    ;;               (print-info-on-new-runes new-runes :major state)
    ;;               (cw "~%Other observations:~%") ; todo: make this shorter, so it doesn't distract from the best suggestions above
    ;;               (print-info-on-old-runes old-runes :minor state)
    ;;               (print-info-on-new-runes new-runes :minor state)
    ;;               (mv nil '(value-triple :invisible) state)))))
    ))

;; This attempts to repair the given book using information in an
;; @event-data.lsp file saved by a previous successful certification (see :doc
;; saving-event-data).
;; Example: (repair-book "../lists-light/append").
(defmacro repair-book (book-path)
  `(make-event-quiet (repair-book-fn ,book-path state)))

;; Examples:
;; (repair-book "expt.lisp")
;; (repair-book "expt")      ; equivalent to the above
;; (repair-book "expt.cert") ; equivalent to the above

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to repairs each of the books indicated by the BOOK-PATHS.
;; Returns (mv erp state).
(defun repair-books-fn-aux (book-paths state)
  (declare (xargs :guard (and (string-listp book-paths))
                  :mode :program
                  :stobjs state))
  (if (endp book-paths)
      (mv nil state)
    (b* ((book-path (first book-paths))
         ((mv erp & state) (repair-book-fn book-path state))
         ((when erp) (mv erp state)))
      (repair-books-fn-aux (rest book-paths) state))))

(defun repair-books-fn (state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((cbd (cbd-fn state))
       (- (cw "~%Looking for books to repair under ~s0.~%" cbd))
       (failed-books (find-failed-books))
       (failed-books (extend-pathnames$ cbd failed-books state))
       ((when (not (consp failed-books)))
        (cw "WARNING: Cannot find any books to repair (based on .cert.out files).")
        (mv t nil state))
       (- (cw "Will attempt to repair the following ~x0 books: ~X12~%" (len failed-books) failed-books nil))
       (state (widen-margins state))
       ((mv erp state) (repair-books-fn-aux failed-books state))
       (state (unwiden-margins state)))
    (mv erp '(value-triple :invisible) state)))

;; Attempts to repair all failed books in the current directory and its subdirectories.
(defmacro repair-books ()
  `(make-event-quiet (repair-books-fn state)))

;; Example (after CDing into the directory of interest):
;; (repair-books)
