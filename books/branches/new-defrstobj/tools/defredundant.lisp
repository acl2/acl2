

(in-package "ACL2")

(include-book "bstar")

;; DEFREDUNDANT -- redundantly introduces an event.


;; Hack to strip out doc strings, because they often depend on deflabels, which
;; can't be redundantly defined.
;; This function isn't strictly correct; for example, in
;; (defconst *my-doc-string*
;;      ":Doc-Section this is the constant's value, not a doc string")
;; it wrongly strips out the string.  Well, if someone tries to use this to
;; redundantly define an event that involves something that looks like a doc
;; string but isn't, maybe he/she will fix this.
(defun strip-doc-string (x)
  (declare (Xargs :mode :program))
  (cond ((atom x) x)
        ((and (stringp (car x))
              (<= (length ":doc-section") (length (car x)))
              (equal (string-downcase
                      (subseq (car x) 0 (length ":doc-section")))
                     ":doc-section"))
         (strip-doc-string (cdr x)))
        ((eq (car x) :doc)
         (strip-doc-string (cdr x)))
        (t (cons (car x)
                 (strip-doc-string (cdr x))))))


(defun get-event-form (name state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       ((er ev-wrld) (er-decode-logical-name name wrld 'get-event-form state))
       (form (access-event-tuple-form (cddar ev-wrld))))
    (value (strip-doc-string form))))

(defmacro defredundant (name)
  `(make-event (get-event-form ',name state)))


(defun collect-event-forms (names state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((when (atom names))
        (value nil))
       ((er first) (get-event-form (car names) state))
       ((er rest) (collect-event-forms (cdr names) state)))
    (value (cons first rest))))

(defun defredundant-events-fn (names state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((er events) (collect-event-forms names state)))
    (value `(progn . ,events))))

(defmacro defredundant-events (&rest names)
  `(make-event (defredundant-events-fn ',names state)))
