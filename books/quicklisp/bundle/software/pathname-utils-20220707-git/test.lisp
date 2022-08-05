#|
 This file is a part of 3d-vectors
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:cl-user)
(defpackage #:pathname-utils-test
  (:nicknames #:org.shirakumo.pathname-utils.test)
  (:use #:cl #:parachute #:pathname-utils)
  (:shadowing-import-from #:pathname-utils #:parent))
(in-package #:org.shirakumo.pathname-utils.test)

(define-test pathname-utils)

(defmacro skip-on (impls explanation &body body)
  `(,@(if (loop for impl in impls
                thereis (find impl *features* :test #'string=))
          (list 'skip explanation)
          (list 'progn))
    ,@body))

(define-test normalization
  :parent pathname-utils)

(define-test clean-directory-spec
  :parent normalization
  :depends-on (unspecific-p)
  (is equal '(:relative) (clean-directory-spec '(:relative)))
  (is equal '(:absolute) (clean-directory-spec '(:absolute)))
  (is equal '(:relative :home) (clean-directory-spec '(:relative :home)))
  (is equal '(:relative "a") (clean-directory-spec '(:relative "a")))
  (is equal '(:relative) (clean-directory-spec '(:relative ".")))
  (is equal '(:relative) (clean-directory-spec '(:relative :unspecific)))
  (is equal '(:relative) (clean-directory-spec '(:relative "")))
  (is equal '(:relative) (clean-directory-spec '(:relative NIL)))
  (is equal '(:relative) (clean-directory-spec '(:relative "a" :back)))
  (is equal '(:relative "a" :up) (clean-directory-spec '(:relative "a" :up)))
  (is equal '(:relative :up) (clean-directory-spec '(:relative :up)))
  (is equal '(:relative :up) (clean-directory-spec '(:relative :back)))
  (is equal '(:relative :up :up) (clean-directory-spec '(:relative :back :back)))
  (is equal '(:relative :up) (clean-directory-spec '(:relative :back "a" :back)))
  (is equal '(:relative :up "b") (clean-directory-spec '(:relative :back "a" :back "b"))))

(define-test normalize-directory-spec
  :parent normalization
  :depends-on (clean-directory-spec unspecific-p)
  (is equal '() (normalize-directory-spec '()))
  (is equal '(:absolute "a") (normalize-directory-spec "a"))
  (is equal `(:relative ,*wild-component*) (normalize-directory-spec *wild-component*))
  (is equal `(:relative ,*wild-inferiors-component*) (normalize-directory-spec *wild-inferiors-component*))
  (is equal '(:absolute) (normalize-directory-spec '(:absolute)))
  (is equal '(:relative) (normalize-directory-spec '(:relative)))
  #-gcl (fail (normalize-directory-spec '(a)))
  (is equal '(:relative :up "b") (normalize-directory-spec '(:relative :back "a" :back "b"))))

(define-test normalize-pathname
  :parent normalization
  :depends-on (normalize-directory-spec unspecific-p)
  (is equal NIL (pathname-device (normalize-pathname (make-pathname :device NIL))))
  (is equal NIL (pathname-name (normalize-pathname (make-pathname :name NIL))))
  (is equal NIL (pathname-type (normalize-pathname (make-pathname :type NIL))))
  (skip-on (allegro) "Allegro's pathname-version always returns :unspecific, even if NIL is supplied."
    (is equal NIL (pathname-version (normalize-pathname (make-pathname :version NIL)))))
  (is equal NIL (pathname-directory (normalize-pathname (make-pathname :directory NIL))))
  (skip-on (ecl clasp clisp) ":unspecific is not allowed in pathname components."
    (is equal NIL (pathname-device (normalize-pathname (make-pathname :device :unspecific))))
    (is equal NIL (pathname-name (normalize-pathname (make-pathname :name :unspecific))))
    (is equal NIL (pathname-type (normalize-pathname (make-pathname :type :unspecific))))
    (skip-on (allegro) "Allegro's pathname-version always returns :unspecific, even if NIL is supplied."
      (is equal NIL (pathname-version (normalize-pathname (make-pathname :version :unspecific))))))
  (skip-on (allegro clisp) "This implementation does not allow a string for the device component"
   (is equal NIL (pathname-device (normalize-pathname (make-pathname :device "")))))
  (is equal NIL (pathname-name (normalize-pathname (make-pathname :name ""))))
  (is equal NIL (pathname-type (normalize-pathname (make-pathname :type ""))))
  (skip-on (allegro) "Allegro's pathname-version always returns :unspecific, even if NIL is supplied."
    (is equal NIL (pathname-version (normalize-pathname (make-pathname :version NIL)))))
  (is equal '(:absolute "a") (pathname-directory (normalize-pathname (make-pathname :directory "a"))))
  (skip-on (allegro ccl lispworks) "This implementation parses (make-pathname :directory \"\") badly."
    (is equal '(:absolute) (pathname-directory (normalize-pathname (make-pathname :directory ""))))))

(define-test pathname*
  :parent normalization
  :depends-on (normalize-pathname)
  (let ((pathname (pathname "a/b/c")))
    (is eq pathname (pathname* pathname)))
  (of-type pathname (pathname* "a/b/c"))
  (is equal (normalize-pathname "a/b/c") (pathname* "a/b/c"))
  (is equal (normalize-pathname "a/b/*") (pathname* "a/b/*")))

(define-test predicates
  :parent pathname-utils)

(define-test unspecific-p
  :parent predicates
  (true (unspecific-p NIL))
  (true (unspecific-p :unspecific))
  (true (unspecific-p ""))
  (false (unspecific-p "a"))
  (false (unspecific-p *wild-component*)))

(define-test relative-p
  :parent predicates
  :depends-on (unspecific-p pathname*)
  (true (relative-p ""))
  (false (relative-p "/")))

(define-test absolute-p
  :parent predicates
  :depends-on (pathname*)
  (false (absolute-p ""))
  (true (absolute-p "/")))

(define-test logical-p
  :parent predicates
  :depends-on (pathname*)
  (false (logical-p "/"))
  (false (logical-p "a"))
  #+sbcl (true (logical-p (logical-pathname "SYS:SRC;")))
  #-sbcl (skip "Cannot portably test logical pathnames as we cannot create them."))

(define-test physical-p
  :parent predicates
  :depends-on (pathname*)
  (true (physical-p "/"))
  (true (physical-p "a"))
  #+sbcl (false (physical-p (logical-pathname "SYS:SRC;"))))

(define-test root-p
  :parent predicates
  :depends-on (pathname* directory-p normalize-directory-spec)
  (true (root-p "/"))
  (false (root-p "a"))
  (false (root-p (make-pathname :directory NIL))))

(define-test directory-p
  :parent predicates
  :depends-on (pathname* unspecific-p)
  (true (directory-p "/"))
  (true (directory-p "a/"))
  (false (directory-p "a"))
  (true (directory-p (user-homedir-pathname))))

(define-test file-p
  :parent predicates
  :depends-on (pathname* directory-p)
  (false (file-p "/"))
  (false (file-p "a/"))
  (true (file-p "a")))

(define-test subpath-p
  :parent predicates
  :depends-on (enough-pathname relative-p)
  (true (subpath-p "/a/b" "/a/"))
  (true (subpath-p "/a/b" "/a/b"))
  (true (subpath-p "a/" "/"))
  (false (subpath-p "/a" "/b"))
  (false (subpath-p "a/" "/b" "/c/")))

(define-test pathname=
  :parent predicates
  :depends-on (normalize-pathname unspecific-p)
  (true (pathname= "a" "a"))
  (true (pathname= "a.b" "a.b"))
  (true (pathname= "a/" "a/"))
  (true (pathname= "/" "/"))
  (true (pathname= "" ""))
  (true (pathname= (make-pathname :directory '(:relative :up))
                   (make-pathname :directory '(:relative :back))))
  (true (pathname= "a///b/" "a/b/"))
  (true (pathname= (make-pathname :version 1) (make-pathname :version 1)))
  (true (pathname= (make-pathname :version 1) (make-pathname :version 2)))
  (false (pathname= "a" "b"))
  (false (pathname= "a.b" "a.c"))
  (false (pathname= "b/a" "c/a"))
  (false (pathname= (make-pathname :version 1) (make-pathname :version 2) :ignore-version NIL)))

(define-test pathname-equal
  :parent predicates
  :depends-on (pathname=)
  (skip "Cannot test pathname-equal as there are no reliable symlinks to test against."))

(define-test coercion
  :parent pathname-utils
  :depends-on (predicates))

(define-test to-root
  :parent coercion
  (is pathname= #p"/" (to-root "/a"))
  (is pathname= #p"/" (to-root "a/"))
  (isnt pathname=
        (make-pathname :name NIL :type NIL :version NIL :directory '(:absolute) :device "a")
        (to-root "/")))

(define-test to-physical
  :parent coercion
  :depends-on (pathname* logical-p)
  (is pathname= #p"a/b" (to-physical "a/b"))
  (is pathname= #p"/a" (to-physical "/a"))
  (skip "Cannot portably test logical pathnames as we cannot create them."))

(define-test to-directory
  :parent coercion
  :depends-on (pathname*)
  (is pathname= #p"/" (to-directory "/"))
  (is pathname= #p"/" (to-directory "/a"))
  (is pathname= #p"" (to-directory "a"))
  (is pathname= #p"a/" (to-directory "a/"))
  (is pathname= #p"a/" (to-directory "a/b.c"))
  (is pathname= (user-homedir-pathname) (to-directory :home))
  (is pathname= (make-pathname :directory '(:relative :up)) (to-directory :up))
  (is pathname= (make-pathname :directory '(:relative :back)) (to-directory :back)))

(define-test to-file
  :parent coercion
  :depends-on (pathname*)
  (is pathname= #p"a" (to-file "a"))
  (is pathname= #p"b" (to-file "/a/b"))
  (is pathname= #p"" (to-file "/")))

(define-test operations
  :parent pathname-utils
  :depends-on (predicates))

(define-test subdirectory
  :parent operations
  :depends-on (to-directory)
  (is pathname= #p"a/b/c/" (subdirectory #p"a/" "b" "c"))
  (is pathname= #p"a/b/" (subdirectory #p"a/c" "b"))
  (is pathname= #p"/a/" (subdirectory #p"/" "a")))

(define-test pop-directory
  :parent operations
  :depends-on (pathname*)
  (is pathname= (make-pathname :directory '(:relative)) (pop-directory "a/"))
  (is pathname= (make-pathname :directory '(:relative "a")) (pop-directory "a/b/"))
  (is pathname= (make-pathname :name "b" :directory '(:relative)) (pop-directory "a/b"))
  (is pathname= #p"" (pop-directory ""))
  (is pathname= #p"/" (pop-directory "/")))

(define-test parent
  :parent operations
  :depends-on (pathname* directory-p root-p to-directory)
  (is pathname= #p"/" (parent "/"))
  (is pathname= #p"/" (parent "/a"))
  (is pathname= #p"" (parent "a"))
  (is pathname= #p"" (parent "a/"))
  (is pathname= #p"a/" (parent "a/b/"))
  (is pathname= (make-pathname :directory '(:relative :up)) (parent "")))

(define-test upwards
  :parent operations
  :depends-on (directory-p subdirectory directory-name to-directory)
  (is pathname= #p"/" (upwards "/"))
  (is pathname= #p"/a" (upwards "/a"))
  (is pathname= #p"/a/" (upwards "/a/"))
  (is pathname= #p"/b" (upwards "/a/b"))
  (is pathname= #p"/b/" (upwards "/a/b/"))
  (is pathname= (make-pathname :directory '(:relative :up)) (upwards ""))
  (is pathname= (make-pathname :name "a" :directory '(:relative :up)) (upwards "a")))

(define-test downwards
  :parent operations
  :depends-on (subdirectory directory-name)
  (is pathname= #p"/a/" (downwards "/" "a"))
  (is pathname= #p"b/a/" (downwards "a/" "b"))
  (is pathname= #p"b/a" (downwards "a" "b")))

(define-test queries
  :parent pathname-utils
  :depends-on (predicates))

(define-test enough-pathname
  :parent queries
  :depends-on (pathname*)
  (is pathname= #p"a/" (enough-pathname #p"a/" #p"/b/"))
  (is pathname= #p"/a/" (enough-pathname #p"/a/" #p"/b/")))

(define-test relative-pathname
  :parent queries
  :depends-on (normalize-pathname to-directory)
  (is pathname= #p"" (relative-pathname #p"/" #p"/"))
  (is pathname= #p"" (relative-pathname #p"a/" #p"a/"))
  (is pathname= #p"a" (relative-pathname #p"a" #p"a"))
  (is pathname= #p"a/" (relative-pathname #p"/" #p"/a/"))
  (is pathname= #p"a" (relative-pathname #p"/" #p"/a"))
  (is pathname= #p"b/c" (relative-pathname #p"a/" #p"a/b/c"))
  (is pathname= #p"b/c/" (relative-pathname #p"a/" #p"a/b/c/"))
  (is pathname= (make-pathname :directory '(:relative :up "d")) (relative-pathname #p"/a/b/" #p"/a/d/"))
  #+windows
  (is pathname= #p"b/c/" (relative-pathname #p"a:/a/" #p"a:/a/b/c/"))
  #+windows
  (fail (relative-pathname #p"a:/a/" #p"b:/a/b/c/")))

(define-test file-in
  :parent queries
  (is pathname= #p"/a.b" (file-in #p"/" #p"a.b"))
  (is pathname= #p"/b.c" (file-in #p"/a" #p"b.c"))
  (is pathname= #p"/c" (file-in #p"/a.b" #p"c"))
  (is pathname= #p"/a/b.c" (file-in #p"/a/" #p"b.c"))
  (is pathname= #p"/a/c.d" (file-in #p"/a/" #p"b/c.d")))

(define-test file-type
  :parent queries
  :depends-on (unspecific-p)
  (is equal "b" (file-type "a.b"))
  (is equal "c" (file-type "a.b.c"))
  (is equal "b" (file-type (make-pathname :name "a.b")))
  (is equal "c" (file-type (make-pathname :name "a" :type "b.c")))
  (is equal NIL (file-type "a"))
  (is equal NIL (file-type "a/"))
  (is equal NIL (file-type "/")))

(define-test file-name
  :parent queries
  (is equal "a" (file-name "a"))
  (is equal "a.b" (file-name "a.b"))
  (is equal "b" (file-name "a/b"))
  (is equal NIL (file-name "a/"))
  (is equal NIL (file-name "/")))

(define-test directory-name
  :parent queries
  :depends-on (to-directory)
  (is equal "a" (directory-name "a/"))
  (is equal "a" (directory-name "a/b"))
  (is equal "b" (directory-name "a/b/"))
  (is equal NIL (directory-name "a"))
  (is equal NIL (directory-name "/")))

(define-test directory-separator
  :parent queries
  #+windows (is equal "\\" (directory-separator))
  #+unix (is equal "/" (directory-separator))
  #-(or windows unix)
  (skip "Directory separator not known on platforms other than windows or unix."))
