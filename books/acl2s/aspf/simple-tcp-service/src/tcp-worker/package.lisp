;; SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT

(defpackage :server
  (:use :cl :usocket :flexi-streams)
  (:import-from :alexandria #:define-constant)
  (:export #:run-tcp-server #:handler-shutdown-request))
