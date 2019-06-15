(include-book "../lofat")

(b*
    (((mv & image-path state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (time$
       (disk-image-to-lofat
        fat32-in-memory image-path state)))
     ((mv state &)
      (time$
       (lofat-to-disk-image
        fat32-in-memory image-path state))))
  (mv fat32-in-memory state))
