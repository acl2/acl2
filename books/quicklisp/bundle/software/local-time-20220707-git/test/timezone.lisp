(in-package #:local-time.test)

(defsuite* (timezone :in test))
(eval-when (:compile-toplevel :load-toplevel :execute)
  (local-time::define-timezone eastern-tz
      (merge-pathnames #p"EST5EDT" local-time::*default-timezone-repository-path*))
  (local-time::define-timezone utc-leaps
      (merge-pathnames #p"right/UTC" local-time::*default-timezone-repository-path*)))



(deftest transition-position/correct-position ()
  (let ((cases '((0 #(1 2 3 4 5) 0)
                 (1 #(1 2 3 4 5) 0)
                 (2 #(1 2 3 4 5) 1)
                 (3 #(1 2 3 4 5) 2)
                 (4 #(1 2 3 4 5) 3)
                 (5 #(1 2 3 4 5) 4)
                 (1 #(1 3 5) 0)
                 (2 #(1 3 5) 0)
                 (3 #(1 3 5) 1)
                 (4 #(1 3 5) 1)
                 (5 #(1 3 5) 2)
                 (6 #(1 3 5) 2)
                 (1 #(1 3 5 7) 0)
                 (2 #(1 3 5 7) 0)
                 (3 #(1 3 5 7) 1)
                 (4 #(1 3 5 7) 1)
                 (5 #(1 3 5 7) 2)
                 (6 #(1 3 5 7) 2)
                 (7 #(1 3 5 7) 3)
                 (8 #(1 3 5 7) 3)
                 )))
    (dolist (case cases)
      (destructuring-bind (needle haystack want)
          case
        (let ((got (local-time::transition-position needle haystack)))
          (is (= got want)
              "(transition-position ~a ~a) got ~a, want ~a"
              needle haystack got want))))))

(deftest test/timezone/decode-timestamp-dst ()
  ;; Testing DST calculation with a known timezone
  (let ((test-cases '(
                      ;; Spring forward
                      ((2008 3 9 6 58) (2008 3 9 1 58))
                      ((2008 3 9 6 59) (2008 3 9 1 59))
                      ((2008 3 9 7  0) (2008 3 9 3  0))
                      ((2008 3 9 7  1) (2008 3 9 3  1))
                      ;; Fall back
                      ((2008 11 2 5 59) (2008 11 2 1 59))
                      ((2008 11 2 6  0) (2008 11 2 1  0))
                      ((2008 11 2 6  1) (2008 11 2 1  1)))))
    (dolist (test-case test-cases)
      (is (equal
           (let ((timestamp
                   (apply 'local-time:encode-timestamp
                          `(0 0 ,@(reverse (first test-case)) :offset 0))))
             (local-time:decode-timestamp timestamp :timezone eastern-tz))
           (apply 'values `(0 0 ,@(reverse (second test-case)))))))))

(deftest test/timezone/adjust-across-dst-by-days ()
  (let* ((old (parse-timestring "2014-03-09T01:00:00.000000-05:00"))
         (new (timestamp+ old 1 :day eastern-tz)))
    (is (= (* 23 60 60) (timestamp-difference new old)))))

(deftest test/timezone/adjust-across-dst-by-hours ()
  (let* ((old (parse-timestring "2014-03-09T01:00:00.000000-05:00"))
         (new (timestamp+ old 24 :hour eastern-tz)))
    (is (= (* 24 60 60) (timestamp-difference new old)))))

(deftest test/timezone/timestamp-minimize-part ()
  (is (timestamp=
       (timestamp-minimize-part
	(encode-timestamp 999999999 59 59 1 14 3 2010 :timezone eastern-tz)
	:month
	:timezone eastern-tz)
       (encode-timestamp 0 0 0 0 1 1 2010 :timezone eastern-tz)))
  (is (timestamp=
       (timestamp-minimize-part
	(encode-timestamp 0 0 0 2 14 3 2010 :timezone eastern-tz)
	:month
	:timezone eastern-tz)
       (encode-timestamp 0 0 0 0 1 1 2010 :timezone eastern-tz))))

(deftest test/timezone/timestamp-maximize-part ()
  (is (timestamp=
       (timestamp-maximize-part
	(encode-timestamp 999999999 59 59 1 7 11 2010 :timezone eastern-tz)
	:month
	:timezone eastern-tz)
       (encode-timestamp 999999999 59 59 23 31 12 2010 :timezone eastern-tz)))
  (is (timestamp=
       (timestamp-maximize-part
	(encode-timestamp 0 0 0 2 7 11 2010 :timezone eastern-tz)
	:month
	:timezone eastern-tz)
       (encode-timestamp 999999999 59 59 23 31 12 2010 :timezone eastern-tz))))

(deftest test/leaps/tai-to-utc ()
  (let ((*default-timezone* utc-leaps))
    (is (= 1435708799
           (local-time::%adjust-sec-for-leap-seconds 1435708824)
           (local-time::%adjust-sec-for-leap-seconds 1435708825)))
    (is (= 1435708800
           (local-time::%adjust-sec-for-leap-seconds 1435708826)))))

(deftest test/abbrev-subzone/not-found ()
  (is (null (local-time:all-timezones-matching-subzone "FOO"))))

(deftest test/abbrev-subzone/find-bst ()
  (is (member
       "Europe/London"
       (local-time:timezones-matching-subzone "BST" (unix-to-timestamp 1585906626))
       :key (lambda (x) (local-time:zone-name (car x)))
       :test #'string=))
  ;; Some historical timezone
  (is (member
       "America/Atka"
       (local-time:all-timezones-matching-subzone "BST")
       :key (lambda (x) (local-time:zone-name (car x)))
       :test #'string=)))

(deftest test/abbrev-subzone/find-gmt ()
  ;; As of 2020-04-03
  (is (equal
       "Etc/Greenwich"
       (local-time:zone-name
        (caar (local-time:timezones-matching-subzone "GMT" (unix-to-timestamp 1585906626)))))))

