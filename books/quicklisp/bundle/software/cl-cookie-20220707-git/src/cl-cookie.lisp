(in-package :cl-user)
(defpackage cl-cookie
  (:nicknames :cookie)
  (:use :cl
        :proc-parse)
  (:import-from :quri
                :cookie-domain-p)
  (:import-from :local-time
                :today
                :timestamp-century
                :timestamp-to-universal
                :universal-to-timestamp
                :format-timestring
                :encode-timestamp
                :*abbreviated-subzone-name->timezone-list*
                :reread-timezone-repository
                :timezone-subzones
                :subzone-abbrev
                :subzone-offset
                :+gmt-zone+)
  (:import-from :alexandria
                :ensure-cons
                :starts-with-subseq)
  (:export :parse-set-cookie-header
           :write-cookie-header
           :write-set-cookie-header
           :cookie
           :make-cookie
           :cookie=
           :cookie-equal
           :cookie-name
           :cookie-value
           :cookie-expires
           :cookie-path
           :cookie-domain
           :cookie-secure-p
           :cookie-httponly-p
           :cookie-origin-host
           :cookie-jar
           :make-cookie-jar
           :cookie-jar-cookies
           :cookie-jar-host-cookies
           :merge-cookies))
(in-package :cl-cookie)

(defstruct cookie
  name
  value
  expires
  path
  domain
  secure-p
  httponly-p
  origin-host)

(defstruct cookie-jar
  cookies)

(defun cookie= (cookie1 cookie2)
  (and (string= (cookie-name cookie1)
                (cookie-name cookie2))
       (if (cookie-domain cookie1)
           (equalp (cookie-domain cookie1)
                   (cookie-domain cookie2))
           (equalp (cookie-origin-host cookie1)
                   (cookie-origin-host cookie2)))
       (equal (cookie-path cookie1)
              (cookie-path cookie2))))

(defun cookie-equal (cookie1 cookie2)
  (and (cookie= cookie1 cookie2)
       (eq (cookie-secure-p cookie1) (cookie-secure-p cookie2))
       (eq (cookie-httponly-p cookie1) (cookie-httponly-p cookie2))))

(defun expired-cookie-p (cookie)
  (and (cookie-expires cookie)
       (< (cookie-expires cookie) (get-universal-time))))

(defun delete-old-cookies (cookie-jar)
  (setf (cookie-jar-cookies cookie-jar)
        (delete-if #'expired-cookie-p
                   (cookie-jar-cookies cookie-jar))))

(defun match-cookie-path (request-path cookie-path)
  (flet ((last-char (str)
           (aref str (1- (length str)))))
    (when (= 0 (length request-path))
      (setf request-path "/"))
    (when (= 0 (length cookie-path))
      (setf cookie-path "/"))
    (or (string= request-path cookie-path)
        (and (starts-with-subseq cookie-path request-path)
             (or (char= (last-char cookie-path) #\/)
                 (char= (aref request-path (length cookie-path)) #\/))))))

(defun match-cookie (cookie host path &key securep)
  (and (if (cookie-secure-p cookie)
           securep
           t)
       (match-cookie-path path (cookie-path cookie))
       (if (cookie-domain cookie)
           (cookie-domain-p host (cookie-domain cookie))
           (equalp host (cookie-origin-host cookie)))))

(defun cookie-jar-host-cookies (cookie-jar host path &key securep)
  (delete-old-cookies cookie-jar)
  (remove-if-not (lambda (cookie)
                   (match-cookie cookie host path :securep securep))
                 (cookie-jar-cookies cookie-jar)))

(defun write-cookie-header (cookies &optional stream)
  (labels ((write-cookie (cookie s)
             (format s "~A=~A"
                     (cookie-name cookie)
                     (cookie-value cookie)))
           (main (cookies stream)
             (write-cookie (pop cookies) stream) 
             (dolist (cookie cookies)
               (write-string "; " stream)
               (write-cookie cookie stream))))
    (when cookies
      (if stream
          (main (ensure-cons cookies) stream)
          (with-output-to-string (s)
            (main (ensure-cons cookies) s))))))

(defparameter +set-cookie-date-format+
  '(:short-weekday ", " (:day 2) #\space :short-month #\space (:year 4) #\space
    (:hour 2) #\: (:min 2) #\: (:sec 2) #\space "GMT")
  "The date format used in RFC 6265. For example: Wed, 09 Jun 2021 10:18:14 GMT.")

(defun write-set-cookie-header (cookie &optional stream)
  (labels ((format-cookie-date (universal-time s)
             (when universal-time
               (format-timestring s (universal-to-timestamp universal-time)
                                  :format +set-cookie-date-format+ :timezone local-time:+gmt-zone+))))
    (format stream
            "~A=~A~@[; Expires=~A~]~@[; Path=~A~]~@[; Domain=~A~]~:[~;; Secure~]~:[~;; HttpOnly~]"
            (cookie-name cookie)
            (cookie-value cookie)
            (format-cookie-date (cookie-expires cookie) stream)
            (cookie-path cookie)
            (cookie-domain cookie)
            (cookie-secure-p cookie)
            (cookie-httponly-p cookie))))

(defun merge-cookies (cookie-jar cookies)
  (setf (cookie-jar-cookies cookie-jar)
        (delete-duplicates
         (nconc (cookie-jar-cookies cookie-jar)
                cookies)
         :test #'cookie=)))

(define-condition invalid-set-cookie (error)
  ((header :initarg :header))
  (:report (lambda (condition stream)
             (format stream "Invalid Set-Cookie header: ~S"
                     (slot-value condition 'header)))))

(define-condition invalid-expires-date (error)
  ((expires :initarg :expires))
  (:report (lambda (condition stream)
             (format stream "Invalid expires date: ~S. Ignoring."
                     (slot-value condition 'expires)))))

(defun integer-char-p (char)
  (char<= #\0 char #\9))

(defun get-tz-offset (tz-abbrev)
  (symbol-macrolet ((timezones local-time::*abbreviated-subzone-name->timezone-list*))
    (let* ((tz (gethash tz-abbrev timezones nil))
           (tz (if tz
                   (car tz)
                   (when (zerop (hash-table-count timezones))
                     (local-time::reread-timezone-repository
                       :timezone-repository (asdf:system-relative-pathname :local-time #P"zoneinfo/"))
                     (first (gethash tz-abbrev timezones nil))))))
      (when tz
        (loop for sub across (local-time::timezone-subzones tz)
              when (equal tz-abbrev (local-time::subzone-abbrev sub))
                do (return (local-time::subzone-offset sub)))))))

(defparameter *current-century-offset*
  (* (1- (timestamp-century (today)))
     100))

(defun parse-cookie-date (cookie-date)
  (let (year month day hour min sec offset)
    (handler-case
        (with-vector-parsing (cookie-date)
          (labels ((parse-month ()
                     (if (integer-char-p (current))
                         (parse-int)
                         (match-case
                          ("Jan" (match? "uary") 1)
                          ("Feb" (match? "ruary") 2)
                          ("Mar" (match? "ch") 3)
                          ("Apr" (match? "il") 4)
                          ("May" 5)
                          ("Jun" (match? "e") 6)
                          ("Jul" (match? "y") 7)
                          ("Aug" (match? "ust") 8)
                          ("Sep" (match? "tember") 9)
                          ("Oct" (match? "ober") 10)
                          ("Nov" (match? "ember") 11)
                          ("Dec" (match? "ember") 12))))
                   (parse-int ()
                     (bind (int (skip-while integer-char-p))
                       (parse-integer int))))
            (skip? #\")
            (match-case
             ("Sun" (match? "day"))
             ("Mon" (match? "day"))
             ("Tue" (match? "sday"))
             ("Wed" (match? "nesday"))
             ("Thu" (match? "rsday"))
             ("Fri" (match? "day"))
             ("Sat" (match? "urday")))
            (skip? #\,)
            (skip #\Space)
            (if (integer-char-p (current))
                (progn
                  (setq day (parse-int))
                  (skip #\Space #\-)
                  (setq month (parse-month))
                  (skip #\Space #\-)
                  (setq year (parse-int))
                  (skip #\Space)
                  (setq hour (parse-int))
                  (skip #\:)
                  (setq min (parse-int))
                  (skip #\:)
                  (setq sec (parse-int)))
                (progn
                  (setq month (parse-month))
                  (skip #\Space #\-)
                  (setq day (parse-int))
                  (skip #\Space)
                  (setq hour (parse-int))
                  (skip #\:)
                  (setq min (parse-int))
                  (skip #\:)
                  (setq sec (parse-int))
                  (skip #\Space)
                  (setq year (parse-int))))
            (skip #\Space)
            (bind (tz-abbrev (skip-while alpha-char-p))
              (setq offset (get-tz-offset tz-abbrev))
              (skip? #\")
              ;; Shorthand year, default to current century
              (when (< year 100)
                (incf year *current-century-offset*))
              (return-from parse-cookie-date
                (local-time:timestamp-to-universal
                 (local-time:encode-timestamp 0 sec min hour day month year :timezone local-time:+gmt-zone+
                                                                            :offset offset))))))
      (error ()
        (error 'invalid-expires-date
               :expires cookie-date)))))

(defun parse-set-cookie-header (set-cookie-string origin-host origin-path)
  (check-type origin-host string)
  (let ((cookie (make-cookie :origin-host origin-host :path origin-path)))
    (handler-case
        (with-vector-parsing (set-cookie-string)
          (bind (name (skip+ (not #\=)))
            (setf (cookie-name cookie) name))
          (skip #\=)
          (bind (value (skip* (not #\;)))
            (setf (cookie-value cookie) value))
          (skip #\;)

          (loop
            (skip* #\Space)
            (match-i-case
             ("expires" (skip #\=)
                        ;; Assume there're both the Max-Age and the Expires attribute if cookie-expires has already set.
                        ;; In that case, just ignores Expires header.
                        (if (cookie-expires cookie)
                            (skip* (not #\;))
                            (bind (expires (skip* (not #\;)))
                              (setf (cookie-expires cookie)
                                    (parse-cookie-date expires)))))
             ("max-age" (skip #\=)
                        (bind (max-age (skip* (not #\;)))
                          (setf (cookie-expires cookie)
                                (+ (get-universal-time)
                                   (parse-integer max-age)))))
             ("path" (skip #\=)
                     (bind (path (skip* (not #\;)))
                       (setf (cookie-path cookie) path)))
             ("domain" (skip #\=)
                       (bind (domain (skip* (not #\;)))
                         (setf (cookie-domain cookie) domain)))
             ("secure" (setf (cookie-secure-p cookie) t))
             ("httponly" (setf (cookie-httponly-p cookie) t))
             (otherwise ;; Ignore unknown attributes
              (skip* (not #\=))
              (skip #\=)
              (skip* (not #\;))))
            (skip? #\;)))
      (match-failed ()
        (error 'invalid-set-cookie :header set-cookie-string))
      (invalid-expires-date (e)
        (warn (princ-to-string e))
        (return-from parse-set-cookie-header nil)))
    cookie))
