(in-package :local-time)

(export 'set-local-time-cl-postgres-readers :local-time)

;; Postgresql days are measured from 2000-01-01, whereas local-time
;; uses 2000-03-01. We expect the database server to be in the UTC timezone.
(defconstant +postgres-day-offset-to-local-time+ -60)

(defun set-local-time-cl-postgres-readers (&optional (table cl-postgres:*sql-readtable*))
  (flet ((timestamp-reader (usecs)
           (multiple-value-bind (days usecs)
               (floor usecs +usecs-per-day+)
             (multiple-value-bind (secs usecs)
                 (floor usecs 1000000)
               (local-time:make-timestamp :nsec (* usecs 1000)
                                          :sec secs
                                          :day (+ days +postgres-day-offset-to-local-time+))))))
    (cl-postgres:set-sql-datetime-readers
     :table table
     :date (lambda (days)
             (local-time:make-timestamp
              :nsec 0 :sec 0
              :day (+ days +postgres-day-offset-to-local-time+)))
     :timestamp #'timestamp-reader
     :timestamp-with-timezone #'timestamp-reader
     :interval
     (lambda (months days usecs)
       (declare (ignore months days usecs))
       (error "Intervals are not yet supported"))
     :time
     (lambda (usecs)
       (multiple-value-bind (days usecs)
           (floor usecs +usecs-per-day+)
         (assert (= days 0))
         (multiple-value-bind (secs usecs)
             (floor usecs 1000000)
           (let ((time-of-day (local-time:make-timestamp
                               :nsec (* usecs 1000)
                               :sec secs
                               :day 0)))
             (check-type time-of-day time-of-day)
             time-of-day)))))))

(defmethod cl-postgres:to-sql-string ((arg local-time:timestamp))
  (format nil "'~a'"
          (local-time:format-rfc3339-timestring nil arg :timezone +utc-zone+)))
