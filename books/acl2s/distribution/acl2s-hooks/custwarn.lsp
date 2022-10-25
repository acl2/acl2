; to warn about not loading customization
(acl2::assign acl2::save-current-package-name (acl2::current-package acl2::state))
(acl2::in-package "ACL2")
(mv-let
 (chan1 state)
 (open-input-channel (string-append (@ connected-book-directory)
                                    "acl2-customization.lisp")
                     :object state)
 (mv-let
  (chan2 state)
  (open-input-channel (string-append (@ user-home-dir)
                                     "/acl2-customization.lisp")
                      :object state)
 
  (if (or chan1 chan2)
    (pprogn
     (prog2$ (cw "~@0" #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup "")
             state)
     (prog2$ (cw "(Not loading acl2-customization file because of session mode.)~%")
             state)
     (if chan1
       (close-input-channel chan1 state)
       state)
     (if chan2
       (close-input-channel chan2 state)
       state)
     (prog2$ (cw "~@0" #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")
             (value :invisible)))
    (value :invisible))))
 (make-event
  '(value-triple `(in-package ,(@ acl2::save-current-package-name))))
