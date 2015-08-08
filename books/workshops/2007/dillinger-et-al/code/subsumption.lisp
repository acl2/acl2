#|$ACL2s-Preamble$;
(ld ;; Newline to fool dependency scanner
 "hacker-pkg.lsp")

(include-book ;; Newline to fool dependency scanner
 "defcode" :ttags ((defcode)))

(acl2::begin-book t :ttags ((defcode)));$ACL2s-Preamble$|#


(in-package "ACL2")

(program)
(set-state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; subsumption of ttags based on what's been done
;
; this should only be used in subsuming hacker stuff, like so:
;
#|
(include-book
 "hacker/hacker")
(progn+all-ttags-allowed ; see hacker.lisp
 (include-book
  "hacker/all" :ttags ((defcode) (table-guard))))
(subsume-ttags-since-defttag)
|#
;

(defun acl2-hacker::ttags-seen-at-defttag (name path wrld last)
  (if (endp wrld)
    (er hard 'subsume-ttags-since-defttag
        "Error retrieving old ttags-seen.")
    (if (and (consp (car wrld))
             (eq 'ttags-seen (caar wrld))
             (consp (cdar wrld))
             (eq 'global-value (cadar wrld)))
      (let ((c (assoc-eq name (cddar wrld))))
        (if (and (consp c)
                 (member-equal path (cdr c)))
          (acl2-hacker::ttags-seen-at-defttag name  path
                                              (cdr wrld) (cddar wrld))
          last))
      (acl2-hacker::ttags-seen-at-defttag name path (cdr wrld) last))))

(defun acl2-hacker::ttags-seen-at-current-defttag (state)
  (let ((wrld (w state)))
    (acl2-hacker::ttags-seen-at-defttag (ttag wrld)
                                        (active-book-name wrld state)
                                        wrld
                                        (global-val 'ttags-seen wrld))))


(defmacro subsume-ttags-since-defttag ()
  '(defcode
     :loop
     (progn!=touchable
      :fns install-event
      (let ((original-ttags-seen
             (acl2-hacker::ttags-seen-at-current-defttag state))
            (current-ttags-seen
             (global-val 'ttags-seen (w state))))
        (if (equal original-ttags-seen
                   current-ttags-seen)
          (value :redundant)
          (install-event ':invisible
                         '(subsume-ttags-since-defttag)
                         'subsume-ttags-since-defttag
                         0
                         nil
                         nil
                         nil
                         'subsume-ttags-since-defttag
                         (putprop 'ttags-seen
                                  'global-value
                                  original-ttags-seen
                                  (w state))
                         state))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; progn-based subsumption of ttags
;

(push-untouchable saved-ttags-seen nil)
(push-untouchable saved-ttag nil)

(defmacro restore-ttags-seen ()
  '(progn!-with-bindings
    ((temp-touchable-fns
      '(install-event)
      set-temp-touchable-fns))
    (if (implies (boundp-global 'saved-ttags-seen state)
                 (equal (@ saved-ttags-seen)
                        (global-val 'ttags-seen (w state))))
      (stop-redundant-event '(restore-ttags-seen) state)
      (install-event ':invisible
                     '(restore-ttags-seen)
                     'restore-ttags-seen
                     0
                     nil
                     nil
                     nil
                     'restore-ttags-seen
                     (putprop 'ttags-seen
                              'global-value
                              (@ saved-ttags-seen)
                              (w state))
                     state))))

(defmacro progn!+subsume-ttags (ttag-spec &rest form-lst)
  `(progn!-with-bindings
    ((progn!+subsume-ttags_saved-ttv (@ temp-touchable-vars))
     (temp-touchable-vars '(ttags-allowed
                            saved-ttag
                            saved-ttags-seen)
                          set-temp-touchable-vars))
    (progn!-with-bindings
     ((ttags-allowed (@ ttags-allowed))
      (saved-ttags-seen (global-val 'acl2::ttags-seen (w state)))
      (saved-ttag (ttag (w state))))
     (progn!
      (defcode
        :loop
        ((er-let*
           ((ttags (chk-well-formed-ttags ',ttag-spec
                                          (cbd)
                                          'progn!+subsume-ttags
                                          state)))
           (assign ttags-allowed ttags))
         (set-temp-touchable-vars (@ progn!+subsume-ttags_saved-ttv) state)))
      ,@ form-lst
      (defcode
        :loop
        ((if (eq (@ saved-ttag) (ttag (w state)))
           (value :invisible)
           (er soft 'progn!+subsume-ttags
               "Please do not change the currently active ttag within the ~
                body of ~x0." 'progn!+subsume-ttags))
         (restore-ttags-seen)))))))

; for export
(defmacro progn+subsume-ttags (ttag-spec &rest form-lst)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; execute some events, subsuming the specified ttags with the current ttag.~/

; ~bv[]
; Example:
; (progn+subsume-ttags
;   ((:foo) (:bar))
;   (include-book
;    \"foo\" :ttags ((:foo)))
;   (include-book
;    \"bar\" :ttags ((:bar))))
; ~ev[] ~/
;
; This is like ~ilc[progn] except that the first argument is a
; ttag-spec (~l[defttag]) to be authorized within the constituent
; events and then subsumed.  That is, an active ttag is required
; to use this form and that ttag is (first) used to allow the use of other
; ttags that may not already be authorized and (second) used to wipe
; the record that any extra ttags were used.  This is what is meant by
; subsumption.  If my book requires a ttag, I can then use this to
; include other books/forms requiring other ttags without those others
; needing specific prior authorization.
;
; An active ttag is required to use this form (~l[defttag]).
; ~/"
  `(progn!+subsume-ttags ,ttag-spec
                         (progn . ,form-lst)))


#|; some tests
(include-book
 "defcode" :ttags ((defcode)))
(defttag test1)
(acl2::ttags-seen)
(progn+subsume-ttags
 :all
 (defttag test2)
 (progn+touchable :all
                  (defun foo (x) (1+ x)))
 (progn! (cw "Hi!~%"))
 (defttag test1))
(ttag (w state))
(acl2::ttags-seen)
;|#

