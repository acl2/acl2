; Tests for filepath library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Aakash Koneru

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FILEPATH")

(include-book "paths")

;Tests
;---------------------

; Parsing

(assert-event (equal (parse-path "foo/bar")
                     (make-path :relative (list "foo" "bar"))))
(assert-event (equal (parse-path "/foo/bar")
                     (make-path :absolute (list "foo" "bar"))))
(assert-event (equal (parse-path "../foo")
                     (make-path :relative (list :back "foo"))))
(assert-event (equal (parse-path "foo/../bar")
                     (make-path :relative (list "foo" :back "bar"))))
(assert-event (equal (parse-path ".")
                     (make-path :relative nil)))
(assert-event (equal (parse-path "/")
                     (make-path :absolute nil)))

(assert-event (equal (parse-path-windows "foo\\bar")
                     (make-path :relative (list "foo" "bar"))))
(assert-event (equal (parse-path-windows "\\foo\\bar")
                     (make-path :absolute (list "foo" "bar"))))

; Printing

(assert-event (equal (path-to-string (make-path :relative (list "foo" "bar")))  "foo/bar"))
(assert-event (equal (path-to-string (make-path :absolute (list "foo" "bar")))  "/foo/bar"))
(assert-event (equal (path-to-string (make-path :relative (list :back "foo")))  "../foo"))
(assert-event (equal (path-to-string (make-path :absolute nil))                 "/"))
(assert-event (equal (path-to-string-windows (make-path :relative (list "foo" "bar"))) "foo\\bar"))
