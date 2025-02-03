(defsystem "simple-tcp-service/tcp-worker"
    :depends-on ("alexandria" "usocket" "usocket-server" "flexi-streams")
    :serial t
    :pathname "src/tcp-worker"
    :components
    ((:file "package")
     (:file "string-trim")
     (:file "tcp-server")))

(defsystem "simple-tcp-service/json"
  :depends-on ("cl-json" "trivia")
  :pathname "src/json"
  :serial t
  :components
  ((:file "package")
   (:file "json")))

(defsystem "simple-tcp-service"
    :depends-on ("simple-tcp-service/tcp-worker"))
