(in-package :cl-user)
(defpackage quri-test
  (:use :cl
        :quri
        :prove))
(in-package :quri-test)

(plan nil)

(defun common-uri-equivalences-assertions ()
  (is (make-uri :scheme "http" :host "b.hatena.ne.jp" :port 80 :path "/path")
      (make-uri :scheme "http" :host "b.hatena.ne.jp" :port 80 :path "/path")
      "Same scheme, host, port, path query and fragment.")
  (isnt (make-uri :scheme "http"  :host "b.hatena.ne.jp" :port 80 :path "/path")
        (make-uri :scheme "https" :host "b.hatena.ne.jp" :port 80 :path "/path")
        "Differ by scheme.")
  (isnt (make-uri :scheme "http" :host "b.hatena.ne.jp" :port 80)
        (make-uri :scheme "http" :host "b.hatena.ne.jp" :port 81)
        "Differ by port.")
  (isnt (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "/path")
        (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "/path" :query "?")
        "Differ by query.")
  (isnt (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "/path")
        (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "/path" :fragment "bar")
        "Differ by fragment.")
  (is (make-uri :scheme "http" :host "b.hatena.ne.jp")
      (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "")
      "The NIL and empty string path are equivalent."))

(subtest "uri="
  (let ((prove:*default-test-function* #'uri=))
    (common-uri-equivalences-assertions)
    (isnt (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "/")
          (make-uri :scheme "http" :host "b.hatena.ne.jp")
          "The NIL and \"/\" path aren't equivalent.")
    (isnt (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "/")
          (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "")
          "The empty string and \"/\" path aren't equivalent.")
    #+todo
    (is (uri "mailto:Joe@Example.COM")
        (uri "mailto:Joe@example.com"))
    #+todo
    (is (uri "mailto:Postmaster@example.com")
        (uri "mailto:POSTMASTER@example.com"))))

(subtest "uri-equal"
  (let ((prove:*default-test-function* #'uri-equal))
    (common-uri-equivalences-assertions)
    (is (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "/")
        (make-uri :scheme "http" :host "b.hatena.ne.jp")
        "The NIL and \"/\" path are equivalent.")
    (is (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "/")
        (make-uri :scheme "http" :host "b.hatena.ne.jp" :path "")
        "The empty string and \"/\" path are equivalent.")))

(defparameter *test-cases*
  '(("file:///tmp/junk.txt" .
     ("file" nil nil "/tmp/junk.txt" nil nil))
    ("imap://mail.common-lisp.net/mbox1" .
     ("imap" nil "mail.common-lisp.net" "/mbox1" nil nil))
    ("mms://wms.sys.hinet.net/cts/Drama/09006251100.asf" .
     ("mms" nil "wms.sys.hinet.net" "/cts/Drama/09006251100.asf" nil nil))
    ("nfs://server/path/to/file.txt" .
     ("nfs" nil "server" "/path/to/file.txt" nil nil))
    ("svn+ssh://svn.zope.org/repos/main/ZConfig/trunk/" .
     ("svn+ssh" nil "svn.zope.org" "/repos/main/ZConfig/trunk/" nil nil))
    ("git+ssh://git@github.com/user/project.git" .
     ("git+ssh" "git" "github.com" "/user/project.git" nil nil))
    ("http://common-lisp.net" .
     ("http" nil "common-lisp.net" nil nil nil))
    ("http://common-lisp.net#abc" .
     ("http" nil "common-lisp.net" nil nil "abc"))
    ("http://common-lisp.net?q=abc" .
     ("http" nil "common-lisp.net" nil "q=abc" nil))
    ("http://common-lisp.net/#abc" .
     ("http" nil "common-lisp.net" "/" nil "abc"))
    ("http://a/b/c/d;p?q#f" .
     ("http" nil "a" "/b/c/d;p" "q" "f"))
    ("http" .
     (nil nil nil "http" nil nil))
    ("http:" .
     ("http" nil nil nil nil nil))
    ("ldap://[2001:db8::7]/c=GB?objectClass?one" .
     ("ldap" nil "[2001:db8::7]" "/c=GB" "objectClass?one" nil))
    ("http://[dead:beef::]:/foo/" .
     ("http" nil "[dead:beef::]" "/foo/" nil nil))
    ("tel:+31-641044153" .
     ("tel" nil nil "+31-641044153" nil nil))
    ("http://" .
     ("http" nil nil nil nil nil))
    ("foo:/a/b/c" .
     ("foo" nil nil "/a/b/c" nil nil))
    ("foo::" .
     ("foo" nil nil ":" nil nil))
    ("/" .
     (nil nil nil "/" nil nil))
    ("foo:/" .
     ("foo" nil nil "/" nil nil))
    ("//a/" .
     (nil nil "a" "/" nil nil))
    ("//" .
     (nil nil nil nil nil nil))
    ("///" .
     (nil nil nil "/" nil nil))
    ("//foo/bar" .
     (nil nil "foo" "/bar" nil nil))))

(loop for (test-uri . params) in *test-cases* do
  (subtest (format nil "~A (string)" test-uri)
    (let ((uri (uri test-uri)))
      (is (uri-scheme uri)   (nth 0 params) "scheme")
      (is (uri-userinfo uri) (nth 1 params) "userinfo")
      (is (uri-host uri)     (nth 2 params) "host")
      (is (uri-path uri)     (nth 3 params) "path")
      (is (uri-query uri)    (nth 4 params) "query")
      (is (uri-fragment uri) (nth 5 params) "fragment")))
  (subtest (format nil "~A (byte-vector)" test-uri)
    (let ((uri (uri (babel:string-to-octets test-uri))))
      (is (uri-scheme uri)   (nth 0 params) "scheme")
      (is (uri-userinfo uri) (nth 1 params) "userinfo")
      (is (uri-host uri)     (nth 2 params) "host")
      (is (uri-path uri)     (nth 3 params) "path")
      (is (uri-query uri)    (nth 4 params) "query")
      (is (uri-fragment uri) (nth 5 params) "fragment")))
  (subtest (format nil "~A (copy-uri)" test-uri)
    (let ((uri (uri test-uri)))
      (is uri (copy-uri uri) :test #'uri=))))

(defparameter *render-uri-inverse-test-cases*
  '(("file:///tmp/junk.txt?query#fragment" .
     ("file" nil nil "/tmp/junk.txt" "query" "fragment"))))

(loop for (test-uri . params) in *render-uri-inverse-test-cases* do
  (subtest (format nil "~A (render-uri after uri gives identity)" test-uri)
    (is test-uri (render-uri (uri test-uri)))))

#+nil
(is-error (uri "//www.youtube.com/embed/”6j0LpmSdWg4”")
          'uri-malformed-string)

(defparameter *base-uri* (uri "http://www.example.com/path/a/b.html"))

(defparameter *merge-test-cases*
  `((,(uri "file:///tmp/junk.txt") . "file:///tmp/junk.txt")
    (,(make-uri :userinfo "auth" :host "secretplace.com") . "http://auth@secretplace.com")
    (,(make-uri :host "example.com" :path "/path" :query "query") . "http://example.com/path?query")
    (,(uri "/new/path") . "http://www.example.com/new/path")
    (,(uri "foo.txt") . "http://www.example.com/path/a/foo.txt")
    (,(uri "../bar") . "http://www.example.com/path/bar")
    (,(uri "other/./car") . "http://www.example.com/path/a/other/car")
    (,(uri "./../.") . "http://www.example.com/path/")
    (,(uri "/./foo") . "http://www.example.com/foo")
    (,(uri "/./foo/") . "http://www.example.com/foo/")
    (,(uri "/x/../y/") . "http://www.example.com/y/")
    (,(uri "/x/../../../y/") . "http://www.example.com/y/")
    (,(uri "foo://x/y/../z/") . "foo://x/z/")
    (,(make-uri :query "name=fukamachi") . "http://www.example.com/path/a/b.html?name=fukamachi")
    (,(make-uri :scheme "https" :host "foo.com" :path "foo/bar") . "https://foo.com/foo/bar")
    (,(uri "https://example.org/#/?b") . "https://example.org/#/?b")
    (,(uri "about:blank") . "about:blank")))

(loop for (test-uri . result-uri) in *merge-test-cases* do
  (let ((merged-uri (merge-uris test-uri *base-uri*)))
    (subtest "merge-uris"
      (is (render-uri merged-uri) result-uri :test 'string=))
    (subtest "merge-uris type checking"
      (unless (uri-scheme test-uri)
        (is (symbol-name (type-of merged-uri))
            (symbol-name (type-of *base-uri*)))))))

(subtest "render-uri"
  (is (let* ((*print-base* 2))
        (render-uri (uri "//foo:80?a=5")))
      "//foo:80?a=5"))

(finalize)
