(include-book "../file-system-m2")
(include-book "centaur/getopt/top" :dir :system)
(include-book "oslib/argv" :dir :system)

(b*
    (((mv & val state)
      (getenv$ "REF_INPUT" state))
     ((mv fat32-in-memory &)
      (disk-image-to-fat32-in-memory
       fat32-in-memory val state))
     (fs-ref (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv & val state)
      (getenv$ "INPUT" state))
     ((mv fat32-in-memory &)
      (disk-image-to-fat32-in-memory
       fat32-in-memory val state))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory)))
  (mv
       (good-bye
        (if (m1-dir-equiv fs-ref fs)
            0
          1))
       fat32-in-memory
       state))
