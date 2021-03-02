(include-book "../test-stuff")
(include-book "oslib/argv" :dir :system)

(defun ls-output (prefix ls-list channel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if
      (atom ls-list)
      state
    (b*
        ((state (princ$ (concatenate 'string prefix (car ls-list)) channel state))
         (state (newline channel state)))
      (ls-output prefix (cdr ls-list) channel state))))

(b*
    (((mv argv state)
      (oslib::argv))
     ((mv errmsg & extra-args) (parse-ls-opts argv))
     ;; Parsing error.
     ((when errmsg)
      (mv (good-bye 1) fat32$c state))
     ((mv & disk-path state)
      (getenv$ "DISK" state))
     ((mv & prefix state)
      (getenv$ "LS_PREFIX" state))
     ((mv & output-path state)
      (getenv$ "LS_OUTPUT" state))
     ((mv fat32$c &)
      (disk-image-to-lofat
       fat32$c disk-path state))
     ((mv fat32$c ls-list exit-status)
      (ls-2 fat32$c state extra-args disk-path))
     ((mv channel state)
      (open-output-channel output-path :character state))
     (state (ls-output prefix ls-list channel state))
     (state (close-output-channel channel state)))
  (mv (good-bye exit-status) fat32$c state))
