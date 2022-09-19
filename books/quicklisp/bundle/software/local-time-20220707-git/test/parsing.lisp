(in-package #:local-time.test)

(defsuite* (parsing :in test))

(deftest test/parsing/parse-format-consistency/range (&key (start-day -100000) (end-day 100000))
  (declare (optimize debug))
  (without-test-progress-printing
    (loop
      :with time = (make-timestamp)
      :for day :from start-day :upto end-day
      :for index :upfrom 0 :do
        (setf (day-of time) day)
        (when (zerop (mod index 10000))
          (print time))
        (let ((parsed (parse-timestring (format-timestring nil time))))
          (is (timestamp= parsed time))))))

(deftest test/parsing/parse-format-consistency ()
  (flet ((compare (nsec sec min hour day mon year str
                        &key start end offset
                        (allow-missing-elements t))
           (let* ((timestamp-a (encode-timestamp nsec sec min hour
                                                 day mon year :offset offset))
                  (used-offset (or offset
                                   (local-time::%guess-offset (sec-of timestamp-a)
                                                              (day-of timestamp-a))))
                  (timestamp-b (parse-timestring str
                                                 :start start
                                                 :end end
                                                 :allow-missing-elements
                                                 allow-missing-elements
                                                 :offset used-offset)))
             (is (timestamp= timestamp-a timestamp-b)))))
    (let ((timestamp (now)))
      (is (timestamp= timestamp
                      (parse-timestring
                       (format-timestring nil timestamp)))))

    (let* ((*default-timezone* (find-timezone-by-location-name "Europe/Budapest")))
      (compare 0 0 0 0 1 1 1 "0001-01-01T00:00:00,0"))

    (compare 0 0 0 0 1 1 1 "0001-01-01T00:00:00Z" :offset 0)

    (compare 0 0 0 0 1 1 2006 "2006-01-01T00:00:00,0")
    (compare 0 0 0 0 1 1 2006 "xxxx 2006-01-01T00:00:00,0 xxxx"
             :start 5
             :end 15)

    (is (eql (day-of (parse-timestring "2006-06-06TZ")) 2288))

    (compare 20000000 3 4 5 6 7 2008 "2008-07-06T05:04:03,02")
    (compare 0 2 0 0 23 3 2000 "--23T::02" :allow-missing-elements t)
    (compare 80000000 7 6 5 1 3 2000 "T05:06:07,08" :allow-missing-elements t)
    (compare 940703000 28 56 16 20 2 2008 "2008-02-20T16:56:28.940703Z"
             :offset 0)))

(deftest test/parsing/split ()
  (is (equal (local-time::%split-timestring "2006-01-02T03:04:05,6-05")
             '(2006 1 2 3 4 5 600000000 -5 0)))
  (is (equal (local-time::%split-timestring "2006-01-02T03:04:05,6-0515")
             '(2006 1 2 3 4 5 600000000 -5 -15)))
  (is (equal (local-time::%split-timestring "2006-01-02T03:04:05,6-05:15")
             '(2006 1 2 3 4 5 600000000 -5 -15))))


(deftest test/parsing/reader ()
  (let ((now (now)))
    (setf (nsec-of now) 123456000)
    (is (timestamp= now
                     (with-input-from-string (ins (format-timestring nil now))
                       (local-time::%read-timestring ins #\@))))))

(deftest test/parsing/read-universal-time ()
  (let ((now (now)))
    (setf (nsec-of now) 0)
    (is (timestamp= now
                     (with-input-from-string (ins (princ-to-string (timestamp-to-universal now)))
                       (local-time::%read-universal-time ins #\@ nil))))))

(deftest test/parsing/error ()
  (signals invalid-timestring (parse-timestring "2019-w2-20")))

(deftest test/parsing/parse-rfc3339 ()
  (let ((local-time:*default-timezone* local-time:+utc-zone+))
    (is (equal (multiple-value-list (decode-timestamp (local-time::parse-rfc3339-timestring "2006-01-02T03:04:05.6-05")))
               '(600000000 5 4 8 2 1 2006 1 NIL 0 "UTC")))
    ;; rfc3339 only supports . for fractional seconds
    (signals local-time::invalid-timestring (local-time::parse-rfc3339-timestring "2006-01-02T03:04:05,6-05"))))
