; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/c/portcullis" :dir :system)
(include-book "kestrel/c/syntax/portcullis" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)
(include-book "oslib/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

(include-book "../syntax/abstract-syntax-symbols")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "C2C" (append
               (set-difference-eq *std-pkg-symbols*
                                  '())
               c$::*abstract-syntax-symbols*
               '(defxdoc+
                 er-soft+
                 erp
                 impossible
                 index-of
                 packn-pos
                 pseudo-event-formp
                 pseudo-event-form-listp
                 reterr
                 retok
                 std::defret-mutual)))
