; to load acl2-customization after other stuff
(acl2::assign acl2::save-current-package-name (acl2::current-package acl2::state))
(acl2::in-package "ACL2")
(let ((wrld (w state)))
  (acl2::mv-let
   (chan state)
   (open-input-channel (string-append (@ connected-book-directory)
                                      "acl2-customization.lisp")
                       :object state)
   (if chan
     (pprogn
      (prog2$ (cw "~@0" #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup "")
              state)
      (prog2$ (cw "Customizing with ~x0.~%" (string-append (@ connected-book-directory)
                                                           "acl2-customization.lisp"))
              state)
      (mv-let (erp v state)
              (ld chan)
              (declare (ignore erp v))
              state)
      (prog2$ (if (not (equal wrld (w state)))
                (cw "~%##############################################################################~%~
                     Warning: Acl2-customization has modified the world, but ~
                     will not be loaded for book certification.  Any ~
                     functionality you depend on in a book should go in the preamble.~
                     ~%##############################################################################~%~%")
                nil) state)
      (close-input-channel chan state)
      (prog2$ (cw "~@0" #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")
              (value :invisible)))
     (let ((saved-cbd (@ connected-book-directory)))
       (er-progn
        (set-cbd (@ user-home-dir))
        (mv-let
         (chan state)
         (open-input-channel (string-append (@ connected-book-directory)
                                            "acl2-customization.lisp")
                             :object state)
         (if chan
           (pprogn
            (prog2$ (cw "~@0" #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup "")
                    state)
            (prog2$ (cw "Customizing with ~x0.~%" (string-append (@ connected-book-directory)
                                                                 "acl2-customization.lisp"))
                    state)
            (mv-let (erp v state)
                    (ld chan)
                    (declare (ignore erp v))
                    state)
            (prog2$ (if (not (equal wrld (w state)))
                      (cw "~%##############################################################################~%~
                           Warning: Acl2-customization has modified the world, but ~
                           will not be loaded for book certification.  Any ~
                           functionality you depend on in a book should go in the preamble.~
                           ~%##############################################################################~%~%")
                      nil) state)
            (close-input-channel chan state)
            (value (cw "~@0" #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")))
           (value nil)))
        (set-cbd saved-cbd)
        (value :invisible))))))
  (make-event
  '(value-triple `(in-package ,(@ acl2::save-current-package-name))))

