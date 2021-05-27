(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg & extra-args) (parse-rm-opts argv))
     ;; Either a parsing error, or no files provided on the command line.
     ((when (or errmsg (atom extra-args)))
      (mv (good-bye 1) fat32$c state))
     ((mv & disk-path state)
      (getenv$ "DISK" state))
     ((mv & output-path state)
      (getenv$ "RM_OUTPUT" state))
     ((mv fat32$c state exit-status)
      (rm-2 fat32$c state disk-path output-path extra-args)))
  (mv (good-bye exit-status) fat32$c state))
