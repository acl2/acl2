; To execute in :logic mode, first do one of these before including this book:
; (include-book "tiny-manual")
; (include-book "tiny-logic")

(in-package "ACL2")

(include-book "tiny")

(program)

(defun show-dm-rec (n default st$ acc)
  (declare (xargs :stobjs st$))
  (cond ((zp n) acc)
        (t (let* ((n (1- n))
                  (v (dmi n st$)))
             (show-dm-rec n default st$
                          (cond ((eql v default) acc)
                                (t (cons (list n v) acc))))))))

(defun show-dm (default st$)
  (declare (xargs :stobjs st$))
  (show-dm-rec 1024 default st$ nil))

(defun show-im-rec (n default st$ acc)
  (declare (xargs :stobjs st$))
  (cond ((zp n) acc)
        (t (let* ((n (1- n))
                  (v (imi n st$)))
             (show-im-rec n default st$
                          (cond ((eql v default) acc)
                                (t (cons (list n v) acc))))))))

(defun show-im (default st$)
  (declare (xargs :stobjs st$))
  (show-im-rec 1024 default st$ nil))

(defun show-indata (st$)
  (declare (xargs :stobjs st$))
  (indata st$))

(defun show-inrdy (st$)
  (declare (xargs :stobjs st$))
  (inrdy st$))

(defun show-outstrobe (st$)
  (declare (xargs :stobjs st$))
  (outstrobe st$))

(defun show-pctr (st$)
  (declare (xargs :stobjs st$))
  (pctr st$))

(defun show-r-rec (n default st$ acc)
  (declare (xargs :stobjs st$))
  (cond ((zp n) acc)
        (t (let* ((n (1- n))
                  (v (ri n st$)))
             (show-r-rec n default st$
                         (cond ((eql v default) acc)
                               (t (cons (list n v) acc))))))))

(defun show-r (default st$)
  (declare (xargs :stobjs st$))
  (show-r-rec 128 default st$ nil))

(defun show-exception (st$)
  (declare (xargs :stobjs st$))
  (exception st$))

(defun show-st$ (st$)
  (declare (xargs :stobjs st$))
  (list (let ((default 0))
          (list :DM
                :DEFAULT default
                (show-DM default st$)))
        (let ((default (encode 'RESERVEDINSTR)))
          (list :IM
                :DEFAULT default
                (show-IM default st$)))
        (list :INDATA (show-INDATA st$))
        (list :INRDY (show-INRDY st$))
        (list :OUTSTROBE (show-OUTSTROBE st$))
        (list :PCTR (show-PCTR st$))
        (let ((default 0))
          (list :R
                :DEFAULT default
                (show-R default st$)))
        (list :EXCEPTION (show-EXCEPTION st$))))

; Running with output.

(defun next-output (st$ chan state)
  (declare (xargs :stobjs (st$ state)))
  (let ((old-strobe (outstrobe st$)))
    (pprogn (fms "~x0"
                 (list (cons #\0 (pctr st$)))
                 chan state nil)
            (mv-let (unit-val st$)
                    (next st$)
                    (declare (ignore unit-val))
                    (pprogn (let ((new-strobe (outstrobe st$)))
                              (cond ((eql old-strobe new-strobe)
                                     state)
                                    (t (fms " [~x0]"
                                            (list (cons #\0 new-strobe))
                                            chan state nil))))
                            (mv st$ state))))))

(defun run-loop-output (n st$ chan state)
  (declare (xargs :stobjs (st$ state)))
  (let ((pc (pctr st$)))
    (mv-let
     (st$ state)
     (next-output st$ chan state)
     (cond ((eql pc (pctr st$))
            (pprogn (fms "Final state (~x0 steps):~|~X12~|"
                         (list (cons #\0 n)
                               (cons #\1 (show-st$ st$))
                               (cons #\2 nil))
                         chan state nil)
                    (close-output-channel chan state)
                    (mv st$ state)))
           (t (run-loop-output (1+ n) st$ chan state))))))

(defun run-output (st$ state)
  (declare (xargs :stobjs (st$ state)))
  (mv-let (unit-val st$)
          (initialize *test_prog* st$)
          (declare (ignore unit-val))
          (mv-let
           (chan state)
           (open-output-channel "run-check.txt" :character state)
           (cond (chan (run-loop-output 0 st$ chan state))
                 (t (pprogn
                     (fms "ERROR: Unable to open file ~x0 for output.~|"
                          (list (cons #\0 "run-check.txt"))
                          *standard-co* state nil)
                     (mv st$ state)))))))

; Running for timing (no output).

(defun run-loop-timing (st$)
  (declare (xargs :stobjs st$))
  (let ((pc (pctr st$)))
    (mv-let (unit-val st$)
            (next st$)
            (declare (ignore unit-val))
            (cond ((eql pc (pctr st$))
                   st$)
                  (t (run-loop-timing st$))))))

(defun run-timing (st$)
  (declare (xargs :stobjs st$))
  (mv-let (unit-val st$)
          (initialize *test_prog* st$)
          (declare (ignore unit-val))
          (run-loop-timing st$)))

(defun run-timing* (k st$)
  (declare (xargs :stobjs st$))
  (declare (type (unsigned-byte 28) k))
  (cond ((eql k 0) st$)
        (t (let ((st$ (run-timing st$)))
             (run-timing* (1- k) st$)))))

(defun run-init* (k st$)
  (declare (xargs :stobjs st$))
  (declare (type (unsigned-byte 28) k))
  (cond ((eql k 0) st$)
        (t (mv-let (unit-val st$)
                   (initialize *test_prog* st$)
                   (declare (ignore unit-val))
                   (run-init* (1- k) st$)))))

; (time$ (run-timing* 10000 st$))
; (time$ (run-init* 10000 st$))
; ips: (/ 350000 (- time1 time2))
