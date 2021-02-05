(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")

(defconst *syscall-pwrite* 1)
(defconst *syscall-pread* 2)
(defconst *syscall-open* 3)
(defconst *syscall-lstat* 4)
(defconst *syscall-unlink* 5)
(defconst *syscall-rmdir* 6)
(defconst *syscall-truncate* 7)
(defconst *syscall-mkdir* 8)
(defconst *syscall-opendir* 9)

(fty::defprod lofat-st
              ((fd natp)
               (buf stringp)
               (offset natp)
               (count natp)
               (retval integerp)
               (errno natp)
               (path fat32-filename-list-p)
               (stat struct-stat-p)
               (statfs struct-statfs-p)
               (dirp natp)
               (fd-table fd-table-p)
               (file-table file-table-p)
               (dirstream-table dirstream-table-p)))

;; We aren't going to put statfs in this. It'll just make things pointlessly
;; complicated.
(defund lofat-oracle-single-step (fat32$c syscall-num st)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (lofat-st-p st))
                  :guard-debug t
                  :verify-guards nil))
  (b*
      ((st (lofat-st-fix st))
       ((when (equal syscall-num *syscall-pwrite*))
        (b*
            (((mv fat32$c retval errno)
              (lofat-pwrite
               (lofat-st->fd st)
               (lofat-st->buf st)
               (lofat-st->offset st)
               fat32$c
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (equal syscall-num *syscall-pread*))
        (b*
            (((mv buf retval errno)
              (lofat-pread
               (lofat-st->fd st)
               (lofat-st->count st)
               (lofat-st->offset st)
               fat32$c
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :buf buf :retval retval :errno errno))))
       ((when (equal syscall-num *syscall-open*))
        (b*
            (((mv fd-table file-table fd retval)
              (lofat-open
               (lofat-st->path st)
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :fd fd :retval retval :errno 0 :file-table file-table
               :fd-table fd-table))))
       ((when (equal syscall-num *syscall-lstat*))
        (b*
            (((mv stat retval errno)
              (lofat-lstat
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :stat stat :retval retval :errno errno))))
       ((when (equal syscall-num *syscall-unlink*))
        (b*
            (((mv fat32$c retval errno)
              (lofat-unlink
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (equal syscall-num *syscall-truncate*))
        (b*
            (((mv fat32$c retval errno)
              (lofat-unlink
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (equal syscall-num *syscall-mkdir*))
        (b*
            (((mv fat32$c retval errno)
              (lofat-mkdir
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (equal syscall-num *syscall-opendir*))
        (b*
            (((mv dirstream-table dirp retval)
              (lofat-opendir
               fat32$c
               (lofat-st->dirstream-table st)
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :dirstream-table dirstream-table :dirp dirp
               :retval retval :errno 0)))))
    (mv fat32$c st)))
