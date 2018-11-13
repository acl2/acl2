(include-book "../file-system-m2")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(defoptions rm-opts
  :parents (demo2)
  :tag :demo2

  ((recursive    "Recursively delete a directory"
                 booleanp
                 :rule-classes :type-prescription
                 :alias #\r)))

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-fat32-in-memory
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "RM_OUTPUT" state))
     ((mv channel state)
       (open-output-channel val :character state))
     ((mv & val state)
      (getenv$ "RM_INPUT" state))
     (fat32-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv & error-code &)
      (m1-lstat fs fat32-pathname))
     ((unless (equal error-code 0))
      (mv fat32-in-memory state))
     ((mv fs & &)
      (m1-unlink fs fat32-pathname))
     (fat32-in-memory
      (m1-fs-to-fat32-in-memory fat32-in-memory fs))
     ;; ((mv errmsg opts ?extra-args) (parse-rm-opts argv))
     (state
      (princ$
       (fat32-in-memory-to-string fat32-in-memory)
       channel state))
     (state
      (close-output-channel channel state)))
  (mv fat32-in-memory state))
