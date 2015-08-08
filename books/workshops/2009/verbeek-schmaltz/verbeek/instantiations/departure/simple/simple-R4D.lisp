#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "make-event/defspec"  :dir :system)
(include-book "../../../generic-modules/GeNoC-departure")

;-----------------------------------------------------------------------
; R4D: all missives are ready for departure
;-----------------------------------------------------------------------
(defun simple-readyfordeparture (missives delayed departing time)
  (declare (ignore delayed departing time))
  (mv nil       ; delayed missives
      missives)); departing missives

(defthm not-in-1-0-ready-for-dept-inst
  (implies (tmissivesp m nodeset)
           (not-in (tm-ids (mv-nth 1 (simple-readyfordeparture m nil nil time)))
                   (tm-ids (mv-nth 0 (simple-readyfordeparture m nil nil time))))))

(defthm not-in-1-0-ready-for-dept-inst-inverted
  (implies (tmissivesp m nodeset)
           (not-in (tm-ids (mv-nth 0 (simple-readyfordeparture m nil nil time)))
                   (tm-ids (mv-nth 1 (simple-readyfordeparture m nil nil time))))))#|ACL2s-ToDo-Line|#


;-------------------------------------
; the instantiations used in this file
;------------------------------------
(defmacro inst-readyfordeparture (missives delayed departing time)
         (list 'simple-readyfordeparture missives delayed departing time))


(definstance GenericR4d R4D-simple
  :functional-substitution
  ((readyfordeparture simple-readyfordeparture)))