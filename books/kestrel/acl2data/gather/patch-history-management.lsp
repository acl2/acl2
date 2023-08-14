; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file history-management.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun chk-acceptable-ttag1 (val active-book-name ttags-allowed ttags-seen
                                 include-bookp ctx state)

; Val should be a keyword (else an error will occur when val is checked with
; ttag-allowed-p below).  Active-book-name is nil, representing the top level,
; or a full-book-name.

; An error triple (mv erp pair state) is returned, where if erp is nil then
; pair either is of the form (ttags-allowed1 . ttags-seen1), indicating a
; refined value for ttags-allowed (see ttag-allowed-p) and an extended value
; for ttags-seen, else is nil, indicating no such update.

; This function must be called if we are to add a ttag.  In particular, it
; should be called under table-fn; it would be a mistake to call this only
; under defttag, since then one could avoid this function by calling table
; directly.

; This function is where we call notify-on-defttag, which prints strings that
; provide the surest way for someone to check that functions requiring ttags
; are being called in a way that doesn't subvert the ttag mechanism.

; patch file: new declare form
  (declare (ignore include-bookp)) ;patch;
; patch file: ttags are allowed
#|
  (let* ((ttags-allowed0 (cond ((eq ttags-allowed :all)
                                t)
                               (t (ttag-allowed-p val ttags-allowed
                                                  active-book-name nil))))
         (ttags-allowed1 (cond ((eq ttags-allowed0 t)
                                ttags-allowed)
                               (t ttags-allowed0))))
|#
  (let* ((ttags-allowed0 t) ;patch;
         (ttags-allowed1 ttags-allowed0)) ;patch;
    (cond
     ((not ttags-allowed1)
      (er soft ctx
          "The ttag ~x0 associated with ~@1 is not among the set of ttags ~
           permitted in the current context, specified as follows:~|  ~
           ~x2.~|See :DOC defttag.~@3"
          val
          (if active-book-name
              (msg "file ~s0"
                   (book-name-to-filename active-book-name (w state) ctx))
            "the top level loop")
          ttags-allowed
          (cond
           ((null (f-get-global 'skip-notify-on-defttag state))
            "")
           (t
            (msg "  This error is unusual since it is occurring while ~
                  including a book that appears to have been certified, in ~
                  this case, the book ~x0.  Most likely, that book needs to ~
                  be recertified, though a temporary workaround may be to ~
                  delete its certificate (i.e., its .cert file).  Otherwise ~
                  see :DOC make-event-details, section ``A note on ttags,'' ~
                  for a possible explanation."
                 (f-get-global 'skip-notify-on-defttag state))))))
     (t
      (pprogn
; patch file: comment out as shown
#|
       (notify-on-defttag val active-book-name include-bookp state)
|#
       (let ((old-book-names (cdr (assoc-eq val ttags-seen))))
         (cond
          ((member-equal active-book-name old-book-names)
           (value (cons ttags-allowed1 ttags-seen)))
          (t
           (value (cons ttags-allowed1
                        (put-assoc-eq val
                                      (cons active-book-name old-book-names)
                                      ttags-seen)))))))))))
