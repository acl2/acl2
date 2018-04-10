(in-package "XDOC")


(include-book "../archive")
(include-book "std/util/define" :dir :system)




(archive-xdoc
 (std::define foo->>bar (x)
  :parents (test)
  :short "Testing"
  :long "<p>Just makes a list of each element of x like this: @('(list x #\\}\\)'). Body: @(body foo->>bar).</p>"
  (if (atom x)
      nil
    (cons (list (car x) #\})
          (foo->>bar (cdr x))))
  ///
  (defthm consp-of-foo->>bar
    (equal (consp (foo->>bar x))
           (consp x)))))


(archive-xdoc
 (std::define bar->>baz (x)
  :parents (test)
  :short "Testing"
  :long "<p>Just makes a  list of each element of x like this: @('(list x #\\}\\)'). Body: @(body bar->baz).</p>"
  (if (atom x)
      nil
    (cons (list (car x) #\})
          (bar->>baz (cdr x))))
  ///
  (defthm consp-of-bar->>baz
    (equal (consp (bar->>baz x))
           (consp x)))))
