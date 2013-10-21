(in-package "ACL2")
(include-book "acl2-doc")

#!XDOC
(defun change-topic-origins
  (from    ; new origin string to use, e.g., "ACL2 Sources"
   topics  ; list of xdoc topics to modify
   )
  (if (atom topics)
      nil
    (cons (acons :from from (delete-assoc :from (car topics)))
          (change-topic-origins from (cdr topics)))))

(make-event
 (let* ((topics (xdoc::get-xdoc-table (w state)))
        (topics (xdoc::change-topic-origins "ACL2 Sources" topics)))
   `(defconst *acl2-doc-topics-only*
      ',topics)))

;; Load in XDOC support books and XDOC documentation
(include-book "xdoc/all" :dir :system)
(include-book "xdoc/defxdoc-raw" :dir :system)
(include-book "oslib/mkdir" :dir :system)

;; Remove any documentation from XDOC and just get the ACL2 topics.
(table xdoc::xdoc 'xdoc::doc
       *acl2-doc-topics-only*)

(defttag :smash-raw)
(progn!
 (set-raw-mode t)
 ;; Remove any defxdoc-raw documentation
 (setq xdoc::*raw-xdoc-list* nil))

(value-triple
 (len (xdoc::get-xdoc-table (w state))) ;; 1555, as expected
 )

(defxdoc top
  :short "ACL2 manual (not including documentation for the community books)"
  :long "<p>This manual is generated from ACL2 documentation only; it excludes documentation from the community books.</p>")

(xdoc::save "./manual"
            :import nil)

