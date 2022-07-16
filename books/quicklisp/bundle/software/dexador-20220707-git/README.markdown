# Dexador

[![Build Status](https://travis-ci.org/fukamachi/dexador.svg?branch=master)](https://travis-ci.org/fukamachi/dexador)
[![Coverage Status](https://coveralls.io/repos/fukamachi/dexador/badge.svg?branch=master)](https://coveralls.io/r/fukamachi/dexador)

Dexador is yet another HTTP client for Common Lisp with neat APIs and connection-pooling.

## Warning

This software is still BETA quality. The APIs will be likely to change.

## Differences from Drakma

* Fast, particularly when requesting to the same host (See [Benchmark](#benchmark))
* Neat APIs
* Signal a condition when HTTP request failed
* OpenSSL isn't required for Windows

See also [a presentation given at Lisp Meetup #31](http://www.slideshare.net/fukamachi/dexador-rises).

## Usage

```common-lisp
(dex:get "http://lisp.org/")

(dex:post "https://example.com/login"
          :content '(("name" . "fukamachi") ("password" . "1ispa1ien")))
```

### Posting a form-data

You can specify a form-data at `:content` in an association list. The data will be sent in `application/x-www-form-urlencoded` format.

```common-lisp
(dex:post "http://example.com/entry/create"
          :content '(("title" . "The Truth About Lisp")
                     ("body" . "In which the truth about lisp is revealed, and some alternatives are enumerated.")))
```

### Auto-detects Multipart

If the association list contains a pathname, the data will be sent as `multipart/form-data`.

```common-lisp
(dex:post "http://example.com/entry/create"
          :content '(("photo" . #P"images/2015030201.jpg")))
```

### Following redirects (GET or HEAD)

If the server reports that the requested page has moved to a different location (indicated with a Location header and a 3XX response code), Dexador will redo the request on the new place, the fourth return value shows.

```common-lisp
(dex:head "http://lisp.org")
;=> ""
;   200
;   #<HASH-TABLE :TEST EQUAL :COUNT 7 {100D2A47A3}>
;   #<QURI.URI.HTTP:URI-HTTP http://lisp.org/index.html>
;   NIL
```

You can limit the count of redirection by specifying `:max-redirects` with an integer. The default value is `5`.

### Using cookies

Dexador adopts [cl-cookie](https://github.com/fukamachi/cl-cookie) for its cookie management. All functions takes a cookie-jar instance at `:cookie-jar`.

```common-lisp
(defvar *cookie-jar* (cl-cookie:make-cookie-jar))

(dex:head "https://mixi.jp" :cookie-jar *cookie-jar* :verbose t)
;-> >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
;   HEAD / HTTP/1.1
;   User-Agent: Dexador/0.1 (SBCL 1.2.9); Darwin; 14.1.0
;   Host: mixi.jp
;   Accept: */*
;   
;   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
;   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
;   HTTP/1.1 200 OK
;   Date: Tue, 10 Mar 2015 10:16:29 GMT
;   Server: Apache
;   X-Dealer: 152151
;   X-XRDS-Location: https://mixi.jp/xrds.pl
;   Cache-Control: no-cache
;   Pragma: no-cache
;   Vary: User-Agent
;   Content-Type: text/html; charset=EUC-JP
;   Set-Cookie: _auid=9d47ca5a00ce4980c41511beb2626fd4; domain=.mixi.jp; path=/; expires=Thu, 09-Mar-2017 10:16:29 GMT
;   Set-Cookie: _lcp=8ee4121c9866435007fff2c90dc31a4d; domain=.mixi.jp; expires=Wed, 11-Mar-2015 10:16:29 GMT
;   X-Content-Type-Options: nosniff
;   
;   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

;; Again
(dex:head "https://mixi.jp" :cookie-jar *cookie-jar* :verbose t)
;-> >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
;   HEAD / HTTP/1.1
;   User-Agent: Dexador/0.1 (SBCL 1.2.9); Darwin; 14.1.0
;   Host: mixi.jp
;   Accept: */*
;   Cookie: _auid=b878756ed71a0ed5bcf527e324c78f8c; _lcp=8ee4121c9866435007fff2c90dc31a4d
;   
;   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
;   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
;   HTTP/1.1 200 OK
;   Date: Tue, 10 Mar 2015 10:16:59 GMT
;   Server: Apache
;   X-Dealer: 152146
;   X-XRDS-Location: https://mixi.jp/xrds.pl
;   Cache-Control: no-cache
;   Pragma: no-cache
;   Vary: User-Agent
;   Content-Type: text/html; charset=EUC-JP
;   Set-Cookie: _auid=b878756ed71a0ed5bcf527e324c78f8c; domain=.mixi.jp; path=/; expires=Thu, 09-Mar-2017 10:16:59 GMT
;   Set-Cookie: _lcp=8ee4121c9866435007fff2c90dc31a4d; domain=.mixi.jp; expires=Wed, 11-Mar-2015 10:16:59 GMT
;   X-Content-Type-Options: nosniff
;   
;   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
```

### Basic Authorization

```common-lisp
(dex:head "http://www.hatena.ne.jp/" :basic-auth '("nitro_idiot" . "password") :verbose t)
;-> >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
;   HEAD / HTTP/1.1
;   User-Agent: Dexador/0.1 (SBCL 1.2.9); Darwin; 14.1.0
;   Host: www.hatena.ne.jp
;   Accept: */*
;   Authorization: Basic bml0cm9faWRpb3Q6cGFzc3dvcmQ=
;   
;   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
```

### Faking a User-Agent header

You can overwrite the default User-Agent header by simply specifying "User-Agent" in `:headers`.

```common-lisp
(dex:head "http://www.sbcl.org/" :verbose t)
;-> >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
;   HEAD / HTTP/1.1
;   User-Agent: Dexador/0.1 (SBCL 1.2.6); Darwin; 14.1.0
;   Host: www.sbcl.org
;   Accept: */*
;   
;   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

(dex:head "http://www.sbcl.org/"
          :headers '(("User-Agent" . "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_10_2) AppleWebKit/600.3.18 (KHTML, like Gecko) Version/8.0.3 Safari/600.3.18"))
          :verbose t)
;-> >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
;   HEAD / HTTP/1.1
;   User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_10_2) AppleWebKit/600.3.18 (KHTML, like Gecko) Version/8.0.3 Safari/600.3.18
;   Host: www.sbcl.org
;   Accept: */*
;   
;   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
```

### Reusing a connection

Dexador reuses a connection by default. As it skips a TCP handshake, it would be much faster when you send requests to the same host continuously.

### Handling unexpected HTTP status code

Dexador signals a condition `http-request-failed` when the server returned 4xx or 5xx status code.

```common-lisp
;; Handles 400 bad request
(handler-case (dex:get "http://lisp.org")
  (dex:http-request-bad-request ()
    ;; Runs when 400 bad request returned
    )
  (dex:http-request-failed (e)
    ;; For other 4xx or 5xx
    (format *error-output* "The server returned ~D" (dex:response-status e))))

;; Ignore 404 Not Found and continue
(handler-bind ((dex:http-request-not-found #'dex:ignore-and-continue))
  (dex:get "http://lisp.org"))

;; Retry
(handler-bind ((dex:http-request-failed #'dex:retry-request))
  (dex:get "http://lisp.org"))

;; Retry 5 times
(let ((retry-request (dex:retry-request 5 :interval 3)))
  (handler-bind ((dex:http-request-failed retry-request))
    (dex:get "http://lisp.org")))
```

### Proxy

You can connect via proxy.

```common-lisp
(dex:get "http://lisp.org/" :proxy "http://proxy.yourcompany.com:8080/")
```

You can connect via SOCKS5 proxy.

```common-lisp
(dex:get "https://www.facebookcorewwwi.onion/" :proxy "socks5://127.0.0.1:9150")
```

You can set the default proxy by setting
```dex:*default-proxy*```
which defaults to the value of the environment variable HTTPS_PROXY or HTTP_PROXY

## Functions

All functions take similar arguments.

- `uri` (string or quri:uri)
- `method` (keyword)
  - The HTTP request method: `:GET`, `:HEAD`, `:OPTIONS`, `:PUT`, `:POST`, or `:DELETE`. The default is `:GET`.
- `version` (number)
  - The version of the HTTP protocol: typically `1.0` or `1.1`. The default is `1.1`.
- `content` (string, alist or pathname)
  - The body of the request.
- `headers` (alist)
  - The headers of the request. If the value of a pair is `NIL`, the header won't be sent. You can overwrite the default headers (Host, User-Agent and Accept) by this with the same header name.
- `basic-auth` (cons of username and password)
  - Username and password for basic authorization. This is a cons having username at car and password at cdr. (e.g. `'("foo" . "bar")`)
- `cookie-jar` (cookie-jar of [cl-cookie](https://github.com/fukamachi/cl-cookie))
  - A cookie jar object.
- `connect-timeout` (fixnum)
  - The seconds to timeout until the HTTP connection established. The default is `10`, the value of `*default-connect-timeout*`.
- `read-timeout` (fixnum)
  - The seconds to timeout until the whole HTTP body read. The default is `10`, the value of `*default-read-timeout*`.
- `keep-alive` (boolean)
  - A flag if the connection keep connected even after the HTTP request. The default is `T`.
- `use-connection-pool` (boolean)
  - When combined with `:keep-alive t`, will internally cache the socket connection to web servers to avoid having to open new ones.  This is compatible with `:want-stream t` (when you close the returned stream or it is garbage collected the connection will be returned to the pool).  If you pass in a stream with `:stream` then the connection pool is not used (unless there is a redirect to a new web server).  This is not supported when using the WINHTTP backend. The default is `T`.
- `max-redirects` (fixnum)
  - The limit of redirections. The default is `5`. If the redirection exceeds the limit, functions return the last response (not raise a condition).
- `ssl-key-file`, `ssl-cert-file`, `ssl-key-password`
  - for HTTPS connection
- `stream`
  - The stream to write an HTTP request. This is a way to reuse a connection and commonly used with `:keep-alive T`.  This allows the caller to do connection pooling, etc.  It is easier to just use `:use-connection-pool t`, which is the default, and let the dexador internals take care of this for you (only supported for usocket backends).
- `verbose` (boolean)
  - This option is for debugging. When `T`, it dumps the HTTP request headers.
- `force-binary` (boolean)
  - A flag for suppressing auto-decoding of the response body.
<!-- - `force-string` -->
- `want-stream` (boolean)
  - A flag to get the response body as a stream.
- `proxy` (string)
  - for use proxy. defaults to the value of `dex:*default-proxy*` which defaults to the value of environment variables HTTPS_PROXY or HTTP_PROXY.  Not supported on windows currently
- `insecure` (boolean)
  - To bypass SSL certificate verification (use at your own risk). The default is `NIL`, the value of `*not-verify-ssl*`.
<!-- - `ca-path` -->


### \[Function\] request

```common-lisp
(dex:request uri &key (method get) (version 1.1) content headers
             basic-auth cookie-jar (connect-timeout *default-connect-timeout*)
             (read-timeout *default-read-timeout*) (keep-alive t) (use-connection-pool t)
             (max-redirects 5) ssl-key-file ssl-cert-file ssl-key-password stream
             (verbose *verbose*) force-binary force-string want-stream proxy
             (insecure *not-verify-ssl*) ca-path)
;=> body
;   status
;   response-headers
;   uri
;   stream
```

Send an HTTP request to `uri`.

The `body` is an octet vector or a string if the `Content-Type` is `text/*`. If you always want it to return an octet vector, specify `:force-binary` as `T`.

The `status` is an integer which represents HTTP status code.

The `response-headers` is a hash table which represents HTTP response headers. Note that all hash keys are downcased like "content-type". If there's duplicate HTTP headers, those values are concatenated with a comma.

The `uri` is a [QURI](https://github.com/fukamachi/quri) object which represents the last URI Dexador requested.

The `stream` is a usocket stream to communicate with the HTTP server if the connection is still alive and can be reused. This value may be `NIL` if `:keep-alive` is `NIL` or the server closed the connection with `Connection: close` header or you are using `:use-connection-pool t` which handles re-using the connections for you.

This function signals `http-request-failed` when the HTTP status code is 4xx or 5xx.

### \[Function\] get

```common-lisp
(dex:get uri &key version headers basic-auth cookie-jar keep-alive
         use-connection-pool connect-timeout read-timeout max-redirects
         force-binary force-string want-stream ssl-key-file
         ssl-cert-file ssl-key-password stream verbose proxy insecure
         ca-path)
```

### \[Function\] post

```common-lisp
(dex:post uri &key version content headers basic-auth cookie-jar
          keep-alive use-connection-pool connect-timeout read-timeout
          force-binary force-string want-stream ssl-key-file
          ssl-cert-file ssl-key-password stream verbose proxy insecure
          ca-path)
```

### \[Function\] head

```common-lisp
(dex:head uri &key version headers basic-auth cookie-jar connect-timeout
          read-timeout max-redirects ssl-key-file ssl-cert-file
          ssl-key-password stream verbose proxy insecure ca-path)
```

### \[Function\] put

```common-lisp
(dex:put uri &key version content headers basic-auth cookie-jar
         keep-alive use-connection-pool connect-timeout read-timeout
         force-binary force-string want-stream ssl-key-file
         ssl-cert-file ssl-key-password stream verbose proxy insecure
         ca-path)
```

### \[Function\] patch

```common-lisp
(dex:patch uri &key version content headers basic-auth cookie-jar
           keep-alive use-connection-pool connect-timeout read-timeout
           force-binary force-string want-stream ssl-key-file
           ssl-cert-file ssl-key-password stream verbose proxy insecure
           ca-path)
```

### \[Function\] delete

```common-lisp
(dex:delete uri &key version headers basic-auth cookie-jar keep-alive
            use-connection-pool connect-timeout read-timeout
            force-binary force-string want-stream ssl-key-file
            ssl-cert-file ssl-key-password stream verbose proxy insecure
            ca-path)
```

### \[Function\] fetch

Send a GET request to `URI` and write the response body to the `DESTINATION`.

```common-lisp
(dex:fetch uri destination &key (if-exists error) verbose proxy insecure)
```

## Benchmark

![Benchmark graph](images/benchmark.png)

* Server
  * Sakura VPS 1GB
  * nginx 1.2.7, KeepAlive On
* Client
  * MacBook Pro OS X Yosemite (CPU: 3GHz Intel Core i7, Memory: 8GB)
  * SBCL 1.2.9
* Downloads an HTML file (181 bytes).

### Drakma

```
(time (dotimes (i 30) (drakma:http-request "http://files.8arrow.org/181B.html")))
Evaluation took:
  1.012 seconds of real time
  0.174742 seconds of total run time (0.148141 user, 0.026601 system)
  17.29% CPU
  1,683 forms interpreted
  500 lambdas converted
  3,027,928,949 processor cycles
  29,416,656 bytes consed
```

### Dexador

```
(time (dotimes (i 30) (dex:get "http://files.8arrow.org/181B.html")))
Evaluation took:
  0.499 seconds of real time
  0.028057 seconds of total run time (0.019234 user, 0.008823 system)
  5.61% CPU
  56 forms interpreted
  16 lambdas converted
  1,494,851,690 processor cycles
  1,472,992 bytes consed
```

## See Also

* [fast-http](https://github.com/fukamachi/fast-http)
* [cl-cookie](https://github.com/fukamachi/cl-cookie)
* [QURI](https://github.com/fukamachi/quri)

## Author

* Eitaro Fukamachi (e.arrows@gmail.com)

## Copyright

Copyright (c) 2015 Eitaro Fukamachi (e.arrows@gmail.com)

## License

Licensed under the MIT License.
