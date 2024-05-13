(defttag :unmonitor-all)
#!acl2
(progn! (defun acl2::unmonitor-all-fn (state)
          (declare (xargs :stobjs (state)))
          (progn$
            (acl2::semi-initialize-brr-wormhole state)
            (prog2$
              (wormhole-eval
                'brr
                '(lambda (acl2::whs)
                   (prog2$ (cw "~y01~|"
                               (change acl2::brr-status acl2::whs
                                       :brr-monitored-runes
                                       nil)
                               nil)
                           acl2::whs))
                nil)
              (pprogn (sync-ephemeral-whs-with-persistent-whs 'brr
                                                              state)
                      (value :invisible)))))

        (defmacro unmonitor-all ()
          `(unmonitor-all-fn state)))
