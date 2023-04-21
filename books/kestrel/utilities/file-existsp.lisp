; A tool to tell whether a file or directory exists
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns (mv existsp state) according to whether PATH exists (as a file or
;; directory or link).  If PATH is a relative path, it is interprted relative
;; to the cbd (connected book directory).
;; Other options for doing this would include making a system call (slow
;; because it forks the ACL2 process), calling oslib::regular-file-p, or
;; calling oslib::path-exists-p.  This calls file-write-date$ and so assumes
;; that a file has a write date if and only if it exists.
(defund file-existsp (path state)
  (declare (xargs :stobjs state
                  :guard (stringp path)))
  (mv-let (file-date state)
    (file-write-date$ path state)
    (mv (if file-date t nil)
        state)))
