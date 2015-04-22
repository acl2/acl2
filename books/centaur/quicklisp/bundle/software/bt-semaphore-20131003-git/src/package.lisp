#|
  This file is a part of bt-semaphore project.
  Copyright (c) 2013 Ralph Möritz (ralph.moeritz@outlook.com)
|#

(in-package :cl-user)
(defpackage :bt-semaphore
  (:nicknames :bt-sem)
  (:use :cl :bordeaux-threads)
  (:export :make-semaphore
           :signal-semaphore
           :wait-on-semaphore
           :try-semaphore
           :semaphore-count
           :semaphore-waiters
           :semaphore-name))
