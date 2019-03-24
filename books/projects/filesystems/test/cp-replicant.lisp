(include-book "../test-stuff")

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-fat32-in-memory
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "CP_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     ((mv & val state)
      (getenv$ "CP_INPUT" state))
     (fat32-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     ((mv fs &)
      (fat32-in-memory-to-m1-fs fat32-in-memory))
     ((mv val error-code &)
      (m1-lstat fs fat32-pathname))
     ((unless (equal error-code 0))
      (mv fat32-in-memory state))
     (file-length (struct-stat->st_size val))
     ((mv fd-table file-table fd &)
      (m1-open fat32-pathname fs nil nil))
     ((mv file-text file-read-length &)
      (m1-pread
       fd file-length 0 fs fd-table file-table))
     ((unless (equal file-read-length file-length))
      (mv fat32-in-memory state))
     (state
      (princ$
       file-text
       channel state))
     (state (close-output-channel channel state)))
  (mv fat32-in-memory state))
