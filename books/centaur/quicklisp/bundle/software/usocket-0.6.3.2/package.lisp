;;;; $Id$
;;;; $URL$

;;;; See the LICENSE file for licensing information.

(defpackage :usocket
  (:use :common-lisp #+abcl :java)
  (:export   #:*version*

             #:*wildcard-host*
             #:*auto-port*

             #:*remote-host* ; special variables (udp)
             #:*remote-port*

             #:+max-datagram-packet-size+

             #:socket-connect ; socket constructors and methods
             #:socket-listen
             #:socket-accept
             #:socket-close
             #:get-local-address
             #:get-peer-address
             #:get-local-port
             #:get-peer-port
             #:get-local-name
             #:get-peer-name

             #:socket-send    ; udp function (send)
             #:socket-receive ; udp function (receive)
             #:socket-server  ; udp server
             #:socket-option  ; 0.6.x

             #:wait-for-input ; waiting for input-ready state (select() like)
             #:make-wait-list
             #:add-waiter
             #:remove-waiter
             #:remove-all-waiters

             #:with-connected-socket ; convenience macros
             #:with-server-socket
             #:with-client-socket
             #:with-socket-listener

             #:usocket ; socket object and accessors
             #:stream-usocket
             #:stream-server-usocket
             #:socket
             #:socket-stream
             #:datagram-usocket

             ;; predicates (for version 0.6 or 1.0 ?)
             #:usocket-p
             #:stream-usocket-p
             #:stream-server-usocket-p
             #:datagram-usocket-p

             #:host-byte-order ; IPv4 utility functions
             #:hbo-to-dotted-quad
             #:hbo-to-vector-quad
             #:vector-quad-to-dotted-quad
             #:dotted-quad-to-vector-quad

             #:vector-to-ipv6-host ; IPv6 utility functions
             #:ipv6-host-to-vector

             #:ip= ; IPv4+IPv6 utility function
             #:ip/=

             #:integer-to-octet-buffer ; Network utility functions
             #:octet-buffer-to-integer
             #:port-to-octet-buffer
             #:port-from-octet-buffer
             #:ip-to-octet-buffer
             #:ip-from-octet-buffer

             #:with-mapped-conditions

             #:socket-condition ; conditions
             #:ns-condition
             #:socket-error ; errors
             #:ns-error
             #:unknown-condition
             #:ns-unknown-condition
             #:unknown-error
             #:ns-unknown-error
             #:socket-warning ; warnings (udp)

             #:insufficient-implementation ; conditions regarding usocket support level
             #:unsupported
             #:unimplemented))
