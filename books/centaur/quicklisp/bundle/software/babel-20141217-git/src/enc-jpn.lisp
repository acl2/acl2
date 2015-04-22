;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; enc-jpn.lisp --- Japanese encodings.
;;;

(in-package #:babel-encodings)

;;;; helper functions
(defvar *eucjp-to-ucs-hash* (make-hash-table))
(defvar *ucs-to-eucjp-hash* (make-hash-table))
(defvar *cp932-to-ucs-hash* (make-hash-table))
(defvar *ucs-to-cp932-hash* (make-hash-table))

(dolist (i `((,*cp932-only*
              ,*cp932-to-ucs-hash*
              ,*ucs-to-cp932-hash*)
             (,*eucjp-only*
              ,*eucjp-to-ucs-hash*
              ,*ucs-to-eucjp-hash*)
             (,*eucjp*
              ,*eucjp-to-ucs-hash*
              ,*ucs-to-eucjp-hash*)))
  (dolist (j (first i))
    (setf (gethash (car j) (second i)) (cadr j))
    (setf (gethash (cadr j) (third i)) (car j))))

(flet ((euc-cp932 (x)
         (let ((high (ash x -16))
               (mid (logand (ash x -8) 255))
               (low (logand x 255)))
           (cond ((not (zerop high))
                  nil)
                 ((= mid #x8e)
                  (logand x 255))
                 ((zerop mid)
                  x)
                 ((decf mid #xa1)
                  (decf low #x80)
                  (incf low (if (zerop (logand mid 1)) #x1f #x7e))
                  (incf low (if (<= #x7f low #x9d) 1 0))
                  (setq mid (ash mid -1))
                  (incf mid (if (<= mid #x1e) #x81 #xc1))
                  (+ (ash mid 8) low))))))
  (dolist (i *eucjp*)
    (let ((cp932 (euc-cp932 (first i))))
      (setf (gethash cp932 *cp932-to-ucs-hash*) (second i))
      (setf (gethash (second i) *ucs-to-cp932-hash*) cp932))))

;ascii
(loop for i from #x00 to #x7f do
      (setf (gethash i *cp932-to-ucs-hash*) i)
      (setf (gethash i *eucjp-to-ucs-hash*) i)
      (setf (gethash i *ucs-to-eucjp-hash*) i)
      (setf (gethash i *ucs-to-cp932-hash*) i))

;half-width katakana
(loop for i from #xa1 to #xdf do
      (setf (gethash i *cp932-to-ucs-hash*) (+ #xff61 #x-a1 i))
      (setf (gethash (+ #xff61 #x-a1 i) *ucs-to-cp932-hash*) i)
      (setf (gethash (+ #x8e00 i) *eucjp-to-ucs-hash*) (+ #xff61 #x-a1 i))
      (setf (gethash (+ #xff61 #x-a1 i) *ucs-to-eucjp-hash*) (+ #x8e00 i)))

(defun eucjp-to-ucs (code)
  (values (gethash code *eucjp-to-ucs-hash*)))

(defun ucs-to-eucjp (code)
  (values (gethash code *ucs-to-eucjp-hash*)))

(defun cp932-to-ucs (code)
  (values (gethash code *cp932-to-ucs-hash*)))

(defun ucs-to-cp932 (code)
  (values (gethash code *ucs-to-cp932-hash*)))

;;;; EUC-JP

(define-character-encoding :eucjp
    "An 8-bit, variable-length character encoding in which
character code points in the range #x00-#x7f can be encoded in a
single octet; characters with larger code values can be encoded
in 2 to 3 bytes."
  :max-units-per-char 3
  :literal-char-code-limit #x80)


(define-octet-counter :eucjp (getter type)
  `(named-lambda eucjp-octet-counter (seq start end max)
     (declare (type ,type seq) (fixnum start end max))
     (loop with noctets fixnum = 0
           for i fixnum from start below end
           for code of-type code-point = (,getter seq i)
           do (let* ((c (ucs-to-eucjp code))
                     (new (+ (cond ((< #xffff c) 3)
                                   ((< #xff c) 2)
                                   (t 1))
                             noctets)))
                (if (and (plusp max) (> new max))
                    (loop-finish)
                    (setq noctets new)))
           finally (return (values noctets i)))))

(define-code-point-counter :eucjp (getter type)
  `(named-lambda eucjp-code-point-counter (seq start end max)
     (declare (type ,type seq) (fixnum start end max))
     (loop with nchars fixnum = 0
           with i fixnum = start
           while (< i end) do
             (let* ((octet (,getter seq i))
                    (next-i (+ i (cond ((= #x8f octet) 3)
                                       ((or (< #xa0 octet #xff)
                                            (= #x8e octet)) 2)
                                       (t 1)))))
               (declare (type ub8 octet) (fixnum next-i))
               (cond ((> next-i end)
                      ;; Should we add restarts to this error, we'll have
                      ;; to figure out a way to communicate with the
                      ;; decoder since we probably want to do something
                      ;; about it right here when we have a chance to
                      ;; change the count or something.  (Like an
                      ;; alternative replacement character or perhaps the
                      ;; existence of this error so that the decoder
                      ;; doesn't have to check for it on every iteration
                      ;; like we do.)
                      ;;
                      ;; FIXME: The data for this error is not right.
                      (decoding-error (vector octet) :eucjp seq i
                                      nil 'end-of-input-in-character)
                      (return (values (1+ nchars) end)))
                     (t
                      (setq nchars (1+ nchars)
                            i next-i)
                      (when (and (plusp max) (= nchars max))
                        (return (values nchars i))))))
           finally (progn (assert (= i end))
                     (return (values nchars i))))))

(define-encoder :eucjp (getter src-type setter dest-type)
  `(named-lambda eucjp-encoder (src start end dest d-start)
     (declare (type ,src-type src)
              (type ,dest-type dest)
              (fixnum start end d-start))
     (loop with di fixnum = d-start
           for i fixnum from start below end
           for code of-type code-point = (,getter src i)
           for eucjp of-type code-point
             = (ucs-to-eucjp code) do
               (macrolet ((set-octet (offset value)
                            `(,',setter ,value dest (the fixnum (+ di ,offset)))))
                 (cond
                   ;; 1 octet
                   ((< eucjp #x100)
                    (set-octet 0 eucjp)
                    (incf di))
                   ;; 2 octets
                   ((< eucjp #x10000)
                    (set-octet 0 (f-logand #xff (f-ash eucjp -8)))
                    (set-octet 1 (logand eucjp #xff))
                    (incf di 2))
                   ;; 3 octets
                   (t
                    (set-octet 0 (f-logand #xff (f-ash eucjp -16)))
                    (set-octet 1 (f-logand #xff (f-ash eucjp -8)))
                    (set-octet 2 (logand eucjp #xff))
                    (incf di 3))
                   ))
           finally (return (the fixnum (- di d-start))))))


(define-decoder :eucjp (getter src-type setter dest-type)
  `(named-lambda eucjp-decoder (src start end dest d-start)
     (declare (type ,src-type src)
              (type ,dest-type dest)
              (fixnum start end d-start))
     (let ((u2 0))
       (declare (type ub8 u2))
       (loop for di fixnum from d-start
             for i fixnum from start below end
             for u1 of-type ub8 = (,getter src i) do
               ;; Note: CONSUME-OCTET doesn't check if I is being
               ;; incremented past END.  We're assuming that END has
               ;; been calculated with the CODE-POINT-POINTER above that
               ;; checks this.
               (macrolet
                   ((consume-octet ()
                      `(let ((next-i (incf i)))
                         (if (= next-i end)
                             ;; FIXME: data for this error is incomplete.
                             ;; and signalling this error twice
                             (return-from setter-block
                               (decoding-error nil :eucjp src i +repl+
                                               'end-of-input-in-character))
                             (,',getter src next-i))))
                    (handle-error (n &optional (c 'character-decoding-error))
                      `(decoding-error
                        (vector ,@(subseq '(u1 u2) 0 n))
                        :eucjp src (1+ (- i ,n)) +repl+ ',c))
                    (handle-error-if-icb (var n)
                      `(when (not (< #x7f ,var #xc0))
                         (decf i)
                         (return-from setter-block
                           (handle-error ,n invalid-utf8-continuation-byte)))))
                 (,setter
                  (block setter-block
                    (cond
                      ;; 3 octets
                      ((= u1 #x8f)
                       (setq u2 (consume-octet))
                       (eucjp-to-ucs (logior #x8f0000
                                             (f-ash u2 8)
                                             (consume-octet))))
                      ;; 2 octets
                      ((or (= u1 #x8e)
                           (< #xa0 u1 #xff))
                       (eucjp-to-ucs (logior (f-ash u1 8)
                                             (consume-octet))))
                      ;; 1 octet
                      (t
                       (eucjp-to-ucs u1))))
                  dest di))
         finally (return (the fixnum (- di d-start)))))))

;;;; CP932

(define-character-encoding :cp932
    "An 8-bit, variable-length character encoding in which
character code points in the range #x00-#x7f can be encoded in a
single octet; characters with larger code values can be encoded
in 2 bytes."
  :max-units-per-char 2
  :literal-char-code-limit #x80)


(define-octet-counter :cp932 (getter type)
  `(named-lambda cp932-octet-counter (seq start end max)
     (declare (type ,type seq) (fixnum start end max))
     (loop with noctets fixnum = 0
           for i fixnum from start below end
           for code of-type code-point = (,getter seq i)
           do (let* ((c (ucs-to-cp932 code))
                     (new (+ (cond ((< #xff c) 2)
                                   (t 1))
                             noctets)))
                (if (and (plusp max) (> new max))
                    (loop-finish)
                    (setq noctets new)))
           finally (return (values noctets i)))))

(define-code-point-counter :cp932 (getter type)
  `(named-lambda cp932-code-point-counter (seq start end max)
     (declare (type ,type seq) (fixnum start end max))
     (loop with nchars fixnum = 0
           with i fixnum = start
           while (< i end) do
             (let* ((octet (,getter seq i))
                    (next-i (+ i (cond ((or (<= #x81 octet #x9f)
                                            (<= #xe0 octet #xfc))
                                        2)
                                       (t 1)))))
               (declare (type ub8 octet) (fixnum next-i))
               (cond ((> next-i end)
                      ;; Should we add restarts to this error, we'll have
                      ;; to figure out a way to communicate with the
                      ;; decoder since we probably want to do something
                      ;; about it right here when we have a chance to
                      ;; change the count or something.  (Like an
                      ;; alternative replacement character or perhaps the
                      ;; existence of this error so that the decoder
                      ;; doesn't have to check for it on every iteration
                      ;; like we do.)
                      ;;
                      ;; FIXME: The data for this error is not right.
                      (decoding-error (vector octet) :cp932 seq i
                                      nil 'end-of-input-in-character)
                      (return (values (1+ nchars) end)))
                     (t
                      (setq nchars (1+ nchars)
                            i next-i)
                      (when (and (plusp max) (= nchars max))
                        (return (values nchars i))))))
           finally (progn (assert (= i end))
                     (return (values nchars i))))))

(define-encoder :cp932 (getter src-type setter dest-type)
  `(named-lambda cp932-encoder (src start end dest d-start)
     (declare (type ,src-type src)
              (type ,dest-type dest)
              (fixnum start end d-start))
     (loop with di fixnum = d-start
           for i fixnum from start below end
           for code of-type code-point = (,getter src i)
           for cp932 of-type code-point
             = (ucs-to-cp932 code) do
               (macrolet ((set-octet (offset value)
                            `(,',setter ,value dest (the fixnum (+ di ,offset)))))
                 (cond
                   ;; 1 octet
                   ((< cp932 #x100)
                    (set-octet 0 cp932)
                    (incf di))
                   ;; 2 octets
                   ((< cp932 #x10000)
                    (set-octet 0 (f-logand #xff (f-ash cp932 -8)))
                    (set-octet 1 (logand cp932 #xff))
                    (incf di 2))
                   ;; 3 octets
                   (t
                    (set-octet 0 (f-logand #xff (f-ash cp932 -16)))
                    (set-octet 1 (f-logand #xff (f-ash cp932 -8)))
                    (set-octet 2 (logand cp932 #xff))
                    (incf di 3))
                   ))
           finally (return (the fixnum (- di d-start))))))


(define-decoder :cp932 (getter src-type setter dest-type)
  `(named-lambda cp932-decoder (src start end dest d-start)
     (declare (type ,src-type src)
              (type ,dest-type dest)
              (fixnum start end d-start))
     (let ((u2 0))
       (declare (type ub8 u2))
       (loop for di fixnum from d-start
             for i fixnum from start below end
             for u1 of-type ub8 = (,getter src i) do
               ;; Note: CONSUME-OCTET doesn't check if I is being
               ;; incremented past END.  We're assuming that END has
               ;; been calculated with the CODE-POINT-POINTER above that
               ;; checks this.
               (macrolet
                   ((consume-octet ()
                      `(let ((next-i (incf i)))
                         (if (= next-i end)
                             ;; FIXME: data for this error is incomplete.
                             ;; and signalling this error twice
                             (return-from setter-block
                               (decoding-error nil :cp932 src i +repl+
                                               'end-of-input-in-character))
                             (,',getter src next-i))))
                    (handle-error (n &optional (c 'character-decoding-error))
                      `(decoding-error
                        (vector ,@(subseq '(u1 u2) 0 n))
                        :cp932 src (1+ (- i ,n)) +repl+ ',c))
                    (handle-error-if-icb (var n)
                      `(when (not (< #x7f ,var #xc0))
                         (decf i)
                         (return-from setter-block
                           (handle-error ,n invalid-utf8-continuation-byte)))))
                 (,setter
                  (block setter-block
                    (cond
                      ;; 2 octets
                      ((or (<= #x81 u1 #x9f)
                           (<= #xe0 u1 #xfc))
                       (setq u2 (consume-octet))
                       (cp932-to-ucs (logior (f-ash u1 8)
                                             u2)))
                      ;; 1 octet
                      (t
                       (cp932-to-ucs u1))))
                  dest di))
         finally (return (the fixnum (- di d-start)))))))
