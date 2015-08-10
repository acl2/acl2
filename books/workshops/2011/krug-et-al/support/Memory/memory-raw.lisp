
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; memory-raw.lisp
;;;
;;; An implementation of fast memory (mapping 32 bit addresses to 8
;;; bit values, both unsigned), using raw Lisp.  This is mostly Alan
;;; Dunn's work, with minor modifications.  He based his work on ideas
;;; and sample code from Jared Davis.
;;;
;;; The only functions that should be called from outside this file
;;; are read-mem-byte and write-mem-byte.
;;;
;;; Before this file is loaded, read-mem-byte and write-mem-byte
;;; should be defined in ACL2 and have (verified) guards of T (or at
;;; least not mention memory).
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defttag memory)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We do no error checking here!

;;; Speed could probably be improved further with the appropriate use
;;; of type declarations.

(progn!

;;; We start by escaping to raw lisp.

 (set-raw-mode t)

;;; We do not want to have to instantiate the entire memory --- this
;;; would be much to large.  Rather, we imitate Intel's 10 10 12
;;; paging structure.  Assuming the memory was fully instantiated, we
;;; would have an 1024 x 1024 x 4096 element array, where each element
;;; contained a single byte.  But, if the element(s) below an entry
;;; have not been instantiated, the element will be zero.

 (defun first-level-address (address)
   ;; The top 10 bits.
   (ash address -22))

 (defun second-level-address (address)
   ;; the second 10 bits
   (logand (ash address -12) (1- (expt 2 10))))

 (defun offset (address)
   ;; the final 12 bits
   (logand address (1- (expt 2 12))))

 (defun read-mem-byte-impl (address mem)
   ;; Note the 10 10 12 paging structure
   (let* ((fl-address (first-level-address address))
	  (fl (aref mem fl-address)))
     (if (not (equal fl 0))
         ;; address potentially instantiated, so we descend to the
         ;; second level of the paging structure.
	 (let* ((sl-address (second-level-address address))
		(sl (aref fl sl-address)))
	   (if (not (equal sl 0))
               ;; address instantiated, so we read
		 (aref sl (offset address))
             ;; address not instantiated
	     0))
       ;; address not instantiated
       0)))

 (defun write-mem-byte-impl (address val mem)
   ;; Note the 10 10 12 paging structure
   (let* ((fl-address (first-level-address address))
	  (fl (aref mem fl-address))
          (fl-exists (not (equal fl 0)))
          ;; If the first-level sub-array does not exist, we create
          ;; it --- 1024 bytes for another 10-bit portion.
	  (fl (if fl-exists
                  fl
                (make-array 1024 :initial-element 0))))
     (let* ((sl-address (second-level-address address))
            (sl (aref fl sl-address))
            (sl-exists (not (equal sl 0)))
            ;; If the second-level sub-array does not exist, we create
            ;; it --- 4096 bytes for a page.
            (sl (if sl-exists
                    sl
                  (make-array 4096 :initial-element 0))))
       ;; We write val into the second-level (page) array
       (setf (aref sl (offset address)) val)
       ;; If the second-level arrray was newly created, we stuff it
       ;; into the first-level array
       (unless sl-exists
         (setf (aref fl sl-address) sl))
       ;; If the first-level array was newly created, we stuff it into
       ;; the memory.
       (unless fl-exists
         (setf (aref mem fl-address) fl))
       mem)))

 (defun maybe-init-memory (memory)
   ;; If we do not have something that at least looks vaguely like
   ;; memory, we create one.
   (if (arrayp memory)
       memory
     (progn
       (cw "Memory: Initializing memory. ~x0~%" memory)
       (make-array 1024 :initial-element 0))))

 (defun read-mem-byte (address memory)
   (let ((memory (maybe-init-memory memory)))
     (read-mem-byte-impl address memory)))

 (defun write-mem-byte (address val memory)
   (let ((memory (maybe-init-memory memory)))
     (write-mem-byte-impl address val memory)
     memory))

)
