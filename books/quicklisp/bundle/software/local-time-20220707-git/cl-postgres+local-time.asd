(defsystem #:cl-postgres+local-time
  :name "cl-postgres+local-time"
  :version "1.0.6"
  :author "Daniel Lowe <dlowe@dlowe.net>"
  :description "Integration between cl-postgres and local-time"
  :depends-on (:cl-postgres :local-time)
  :components ((:module "src"
                :components ((:module "integration"
                              :components ((:file "cl-postgres")))))))
