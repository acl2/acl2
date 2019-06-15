(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "WC_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     ((mv & val state)
      (getenv$ "WC_INPUT" state))
     ((mv nl nw nc exit-status) (wc-1 fat32-in-memory val))
     ((unless (equal exit-status 0)) (mv fat32-in-memory state (good-bye 1)))
     ((mv argv state)              (oslib::argv))
     ((mv errmsg opts ?extra-args) (parse-wc-opts argv))
     ((wc-opts opts) opts)
     (state
      (if errmsg state
        (if opts.bytes
            (princ$
             nc
             channel state)
          (if opts.lines
              (princ$
               nl
               channel state)
            (if opts.words
                (princ$
                 nw
                 channel state)
              state)))))
     (state (newline channel state))
     (state (close-output-channel channel state)))
  (mv fat32-in-memory state (good-bye 0)))
