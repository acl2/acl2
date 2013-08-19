(defvar *acl2-interface-dir*
  "/projects/acl2/v2-x/interface/emacs/")

(setq *acl2-user-map-interface*
  '((global keys)))

(let ((load-path (cons *acl2-interface-dir* load-path)))
  (load "load-shell-acl2"))
