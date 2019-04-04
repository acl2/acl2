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
     (fat32-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     ((mv fs &)
      (lofat-to-hifat fat32-in-memory))
     ((mv val error-code &)
      (hifat-lstat fs fat32-pathname))
     ((unless (equal error-code 0))
      (mv fat32-in-memory state))
     (file-length (struct-stat->st_size val))
     ((mv fd-table file-table fd &)
      (hifat-open fat32-pathname fs nil nil))
     ((mv file-text file-read-length &)
      (hifat-pread
       fd file-length 0 fs fd-table file-table))
     ((unless (equal file-read-length file-length))
      (mv fat32-in-memory state))
     ((mv nl nw nc)
      (wc-helper file-text 0 0 0 t 0))
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
  (mv fat32-in-memory state))
