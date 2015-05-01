
(in-package "ACL2")

(include-book "memory-mgmt-logic")
(include-book "tools/include-raw" :dir :system)

; (depends-on "hons-analyze-memory-raw.lsp")

(defttag memory-mgmt)

(progn!
 (set-raw-mode t)

 (defmacro pkc (pkg fn &rest args)
   (cons (intern (symbol-name fn) (symbol-name pkg))
         args))

 ;; Use defvar so these aren't clobbered.
 (defvar *gc-min-threshold* (expt 2 30))

 (defvar *max-mem-usage* (expt 2 32))

 (defvar *last-chance-threshold*
   ;; We'll automatically wash if we get within 1/400 of the max memory usage.
   ;; Examples:
   ;;   If *max-mem-usage* is   8 GB, the cushion is  ~21 MB.
   ;;   If *max-mem-usage* is  16 GB, the cushion is  ~42 MB.
   ;;   If *max-mem-usage* is  32 GB, the cushion is  ~85 MB.
   ;;   If *max-mem-usage* is  64 GB, the cushion is ~171 MB.
   ;;   If *max-mem-usage* is  96 GB, the cushion is ~257 MB.
   ;;   If *max-mem-usage* is 128 GB, the cushion is ~343 MB.
   (ceiling *max-mem-usage* 400))

 (defun set-max-mem-usage (max)
   (setf *max-mem-usage* max)
   (setf *last-chance-threshold* (ceiling *max-mem-usage* 400))
   (setf *gc-min-threshold* (floor *max-mem-usage* 5))
   (set-and-reset-gc-thresholds))

 (defun print-quick-memory-summary ()
   (multiple-value-bind
    (dynamic-used static-used library-used frozen-size)
    (pkc ccl %usedbytes)
    (let ((free (pkc ccl %freebytes))
          (used (+ dynamic-used static-used library-used frozen-size))
          (max  *max-mem-usage*))
      (format t "Max:            ~15:D bytes~%" max)
      (format t "Free:           ~15:D bytes~%" free)
      (format t "Used:           ~15:D bytes~%" used)
      (format t "  - Dynamic:    ~15:D bytes~%" dynamic-used)
      (format t "  - Static:     ~15:D bytes~%" static-used)
      (format t "  - Library:    ~15:D bytes~%" library-used)
      (format t "  - Frozen:     ~15:D bytes~%" frozen-size)
      (format t "Dynamic+Frozen: ~15:D bytes~%" (+ dynamic-used frozen-size))
      (hons-summary)
      (hons-analyze-memory nil)
      (finish-output))))

 (defun maybe-wash-memory-fn (n clear)
   (declare (ignorable clear))
   (when (or (eq n t)
             (< (pkc ccl %freebytes) (nfix n)))
     (format t "********** maybe-wash-memory started ***********~%~%")
     (format t "Pre-wash memory usage.~%")
     (print-quick-memory-summary)
     (hons-wash)
     (format t "Post-wash memory usage:~%")
     (print-quick-memory-summary)

     (format t "********** maybe-wash-memory finished **********~%"))

   nil)

 (defun last-chance-wash-memory-fn ()
   (when (< (pkc ccl %freebytes) *last-chance-threshold*)
     (format t "*********** last-chance-wash-memory ************~%")
     (format t "~:D free bytes < ~:D last chance threshold~%"
             (pkc ccl %freebytes)
             *last-chance-threshold*)
     (maybe-wash-memory-fn t nil)))

 (defun set-max-mem (max)
   (set-max-mem-usage max)
   nil)

 (defun print-rwx-size ()
   (cw "~x0~%" (rwx-size))))

(include-raw "hons-analyze-memory-raw.lsp")



