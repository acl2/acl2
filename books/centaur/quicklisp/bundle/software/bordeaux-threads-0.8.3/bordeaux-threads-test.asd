#|
Copyright 2006,2007 Greg Pfeil

Distributed under the MIT license (see LICENSE file)
|#

(asdf:defsystem :bordeaux-threads-test
  :depends-on (:bordeaux-threads :fiveam)
  :version #.(with-open-file
                 (vers (merge-pathnames "version.lisp-expr" *load-truename*))
               (read vers))
  :components ((:module "test"
                :components ((:file "bordeaux-threads-test"))))
  :in-order-to ((asdf:test-op (asdf:load-op bordeaux-threads-test)))
  :perform (asdf:test-op :after (op c)
             (describe (funcall (intern (string '#:run!) :fiveam)
                                :bordeaux-threads))))
