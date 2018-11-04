#|
  This file is a part of bt-semaphore project.
  Copyright (c) 2013 Ralph Moeritz (ralphmoritz@outlook.com)
|#

(in-package :cl-user)
(defpackage :bt-semaphore
  (:nicknames :bt-sem)
  (:use :cl)
  (:export :make-semaphore
           :signal-semaphore
           :wait-on-semaphore
           :try-semaphore
           :semaphore-count
           :semaphore-waiters
           :semaphore-name))
