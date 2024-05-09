(in-package "ACL2S-HOOKS")

(defconst *acl2s-hooks-version* "1.4.0.0")

; Needed as of 2021-01-19 to avoid a build error
(set-slow-alist-action :warning)

(include-book "hacking/hacker" :dir :system)
(include-book "hacking/defcode" :dir :system :ttags :all)
(include-book "hacking/redefun" :dir :system)
(include-book "hacking/rewrite-code" :dir :system)
(include-book "hacking/raw" :dir :system)
;(include-book "contentassist" :load-compiled-file :comp)

; do not inline this one; we reuse it
(include-book "canonical-print" :load-compiled-file :comp)
(include-book "acl2s-book-support" :load-compiled-file :comp)

(include-book "categorize-input" :load-compiled-file :comp)

(include-book "super-history"
  :load-compiled-file :comp
  :ttags ((:acl2s-super-history)
          (defcode)))

(include-book "protection-hooks"
  :load-compiled-file :comp
  :ttags ((:acl2s-protection)
          (:acl2s-super-history)
          (defcode)))

(include-book "interaction-hooks"
  :load-compiled-file :comp
  :ttags ((:acl2s-protection)
          (:acl2s-super-history)
          (:acl2s-interaction)
          (defcode)))

(include-book "markup-hooks"
  :load-compiled-file :comp
  :ttags ((:acl2s-markup)
          (defcode)))

(program)
(set-state-ok t)

(defun acl2s-begin (secret state)
  (declare (ignorable secret))
  (er-progn
   (acl2s-interaction-begin state)
   (acl2s-markup-begin state)
   (acl2s-protection-begin secret state)
   ))


; Suppress printing of TTAG Notes in ACL2s session modes
(acl2::redef+)
(defun acl2::print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
           (ignore val active-book-name include-bookp deferred-p))
  state)
(acl2::redef-)
