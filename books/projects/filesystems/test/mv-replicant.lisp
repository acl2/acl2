(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(b*
    (((mv argv state)
      (oslib::argv))
     ((unless (>= (len argv) 2))
      (mv (good-bye 1) fat32-in-memory state))
     ((mv & val state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (disk-image-to-lofat
       fat32-in-memory val state))
     ((mv fs &)
      (lofat-to-hifat fat32-in-memory))
     (oldpathname (pathname-to-fat32-pathname (coerce (nth 0 argv) 'list)))
     (newpathname (pathname-to-fat32-pathname (coerce (nth 1 argv) 'list)))
     ((mv fs exit-status &)
      (m1-rename fs oldpathname newpathname))
     ((mv fat32-in-memory &)
      (hifat-to-lofat fat32-in-memory fs))
     ((mv & val state)
      (getenv$ "MV_OUTPUT" state))
     (state
      (lofat-to-disk-image
       fat32-in-memory val state)))
  (mv (good-bye exit-status) fat32-in-memory state))
