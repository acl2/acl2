(include-book "../test-stuff")

(b*
    (((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv & val state)
      (getenv$ "CP_OUTPUT" state))
     ((mv channel state)
      (open-output-channel val :character state))
     ((mv & val state)
      (getenv$ "CP_INPUT" state))
     (fat32-pathname (pathname-to-fat32-pathname (coerce val 'list)))
     ((mv val error-code &)
      (lofat-lstat fat32-in-memory fat32-pathname))
     ((unless (equal error-code 0))
      (mv fat32-in-memory state))
     (file-length (struct-stat->st_size val))
     ((mv fd-table file-table fd &)
      (lofat-open fat32-pathname nil nil))
     ((mv file-text file-read-length &)
      (lofat-pread
       fd file-length 0 fat32-in-memory fd-table file-table))
     ((unless (equal file-read-length file-length))
      (mv fat32-in-memory state))
     (state
      (princ$
       file-text
       channel state))
     (state (close-output-channel channel state)))
  (mv fat32-in-memory state))
