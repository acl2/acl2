(include-book "../lofat")

(b*
    (((mv & image-path state)
      (getenv$ "DISK" state))
     ((mv fat32$c &)
      (time$
       (disk-image-to-lofat
        fat32$c image-path state)))
     ((mv state &)
      (time$
       (lofat-to-disk-image
        fat32$c image-path state))))
  (mv fat32$c state))
