(include-book "../file-system-m2")

;; This event is redundant; the original event is in ../file-system-m2.lisp.
(defund
  fat32-in-memory-to-string
  (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (compliant-fat32-in-memoryp fat32-in-memory)))
  (b* ((reserved-area-string
        (reserved-area-string fat32-in-memory))
       (fat-string
        (make-fat-string-ac (bpb_numfats fat32-in-memory)
                            fat32-in-memory ""))
       (data-region-string
        (coerce (data-region-string-helper
                 fat32-in-memory
                 (data-region-length fat32-in-memory)
                 nil)
                'string)))
    (concatenate 'string
                 reserved-area-string
                 fat-string data-region-string)))

;; This event is redundant; the original event is in ../file-system-m2.lisp.
(defun
  fat32-in-memory-to-disk-image
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :stobjs (fat32-in-memory state)
    :guard (and (state-p state)
                (stringp image-path)
                (compliant-fat32-in-memoryp fat32-in-memory))))
  (b*
      (((mv channel state)
        (open-output-channel image-path
                             :character state))
       ((when (null channel)) state)
       (state
        (mbe
         :logic (princ$ (fat32-in-memory-to-string fat32-in-memory)
                        channel state)
         :exec
         (b*
             ((state (princ$ (reserved-area-string fat32-in-memory)
                             channel state))
              (state
               (princ$
                (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                    fat32-in-memory "")
                channel state))
              (state (princ$-data-region-string-helper
                      fat32-in-memory
                      (data-region-length fat32-in-memory)
                      channel state)))
           (princ$ "" channel state))))
       (state (close-output-channel channel state)))
    state))

(b*
    (((mv & image-path state)
      (getenv$ "DISK" state))
     ((mv fat32-in-memory &)
      (time$
       (disk-image-to-fat32-in-memory
        fat32-in-memory image-path state)))
     (state
      (time$
       (fat32-in-memory-to-disk-image
        fat32-in-memory image-path state))))
  (mv fat32-in-memory state))
