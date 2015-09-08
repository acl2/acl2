(in-package "ACL2")
(include-book "acl2-doc-wrap")

;; Load in XDOC support books and XDOC documentation
(include-book "xdoc/all" :dir :system)
(include-book "xdoc/defxdoc-raw" :dir :system)
(include-book "oslib/mkdir" :dir :system)

(include-book "centaur/misc/tshell" :dir :system)
(value-triple (acl2::tshell-ensure))

;; Remove any documentation from XDOC and just get the ACL2 topics.
(table xdoc::xdoc 'xdoc::doc *acl2-sources-xdoc-topics*)

(defttag :smash-raw)
(progn!
 (set-raw-mode t)
 ;; Remove any defxdoc-raw documentation
 (setq xdoc::*raw-xdoc-list* nil))

(value-triple
 (len (xdoc::get-xdoc-table (w state))) ;; 1555, as expected
 )

(defxdoc top
  :short "ACL2 User's Manual (not including documentation for the community books)"

  :long "<p>This manual is generated from ACL2 documentation only; it excludes
  documentation from the community books.</p>")

(xdoc::save "../../../doc/manual"
            ; :import nil ; no longer supported
            )

