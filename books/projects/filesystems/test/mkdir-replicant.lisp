(include-book "../file-system-m2")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(defoptions mkdir-opts
  :parents (demo2)
  :tag :demo2

  ((parents    "no error if existing, make parent directories as needed"
               booleanp
               :rule-classes :type-prescription
               :alias #\p)))

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-fat32-in-memory
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "MKDIR_OUTPUT" state))
     ((mv channel state)
       (open-output-channel val :character state))
     ((mv & val state)
      (getenv$ "MKDIR_INPUT" state))
     (fat32-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     ((mv fs &)
      (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv fs & &)
      (m1-mkdir fs fat32-pathname))
     ((mv fat32-in-memory &)
      (m1-fs-to-fat32-in-memory fat32-in-memory fs))
     ;; ((mv errmsg opts ?extra-args) (parse-rm-opts argv))
     (state
      (princ$
       (fat32-in-memory-to-string fat32-in-memory)
       channel state))
     (state
      (close-output-channel channel state)))
  (mv fat32-in-memory state))
