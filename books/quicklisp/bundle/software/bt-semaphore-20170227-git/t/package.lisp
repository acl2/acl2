#|
  This file is a part of bt-semaphore project.
  Copyright (c) 2013 Ralph Moeritz (ralphmoritz@outlook.com)
|#

(in-package :cl-user)
(defpackage bt-semaphore-test
  (:use :cl
        :bordeaux-threads
        :bt-semaphore
        :clunit))
