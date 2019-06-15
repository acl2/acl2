(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg opts extra-args) (parse-truncate-opts argv))
     ;; Either a parsing error, or no files provided on the command line.
     ((when (or errmsg (atom extra-args)))
      (mv (good-bye 1) fat32-in-memory state))
     ((truncate-opts opts) opts)
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv fat32-in-memory exit-status)
      (truncate-list fat32-in-memory extra-args opts.size 0))
     ((mv & val state)
      (getenv$ "TRUNCATE_OUTPUT" state))
     ;; Will take the exit status from lofat-to-disk-image later.
     ((mv state &)
      (lofat-to-disk-image
       fat32-in-memory val state)))
  (mv
   (good-bye exit-status)
   fat32-in-memory
   state))
