(defvar *acl2-interface-dir*
  "/slocal/src/acl2/v1-8/interface/emacs/")

(setq *acl2-user-map-interface*
  '((inferior-acl2-mode-map menu-bar popup-menu keys)
    (shell-mode-map         menu-bar popup-menu keys)
    (acl2-mode-map          menu-bar popup-menu keys)
    (prooftree-mode-map     menu-bar popup-menu keys)))

(let ((load-path (cons *acl2-interface-dir* load-path)))
  (load "load-inferior-acl2"))
