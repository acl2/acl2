; A tool to tell whether a file exists
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns (mv existsp state).  Other options for doing this would include
;; making a system call (slow because it forks the ACL2 process), calling
;; oslib::regular-file-p, or calling oslib::path-exists-p.  This seems to also
;; work for relative paths, but I am not sure what they are relative to (seems
;; to not be the CBD, perhaps it's the directory in which ACL2 was started).
;; This calls file-write-date$ and so assumes that a file has a write date if
;; and only if it exists.
(defund file-existsp (absolute-path state)
  (declare (xargs :stobjs state
                  :guard (stringp absolute-path)))
  (mv-let (file-date state)
    (file-write-date$ absolute-path state)
    (mv (if file-date t nil)
        state)))
