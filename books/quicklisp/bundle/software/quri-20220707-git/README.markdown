# QURI

[![Build Status](https://travis-ci.org/fukamachi/quri.svg?branch=master)](https://travis-ci.org/fukamachi/quri)
[![Coverage Status](https://coveralls.io/repos/fukamachi/quri/badge.svg?branch=master)](https://coveralls.io/r/fukamachi/quri)

<p align=center><a href="https://www.flickr.com/photos/m-louis/8209540334/"><img src="https://c7.staticflickr.com/9/8202/8209540334_76417d9fde_b.jpg" alt="冷やしきゅうり"></a></p>
<p align=right><i>Photo by <a href="https://www.flickr.com/photos/m-louis/">m-louis</a>, licensed under the <a href="https://creativecommons.org/licenses/by-sa/2.0/">CC BY-SA 2.0</a> license.</i></p>

**QURI** (pronounced "Q-ree") is yet another URI library for Common Lisp. It is intended to be a replacement of [PURI](http://puri.b9.com).

## Differences from PURI

- Fast. (See [Benchmark](#benchmark).)
- Doesn't encode/decode URL implicitly.
- UTF-8 characters support.
- Supports userinfo. (Example: `git` in `git@github.com`)
- Supports IPv6 hostname. (Example: `ldap://[2001:db8::7]/`)
- Allows byte vectors as input.
- Takes optional `:start` and `:end` keyword arguments.
- Low-level parser functions.
- URL encoding/decoding utilities.
  - `url-decode`
  - `url-decode-params`
  - `url-encode`
  - `url-encode-params`

## Usage

```common-lisp
(use-package :quri)

(defvar *uri* (uri "http://www.ics.uci.edu/pub/ietf/uri/#Related"))

*uri*
;=> #<QURI.URI.HTTP:URI-HTTP http://www.ics.uci.edu/pub/ietf/uri/#Related>

(uri-scheme *uri*)
;=> "http"

(uri-host *uri*)
;=> "www.ics.uci.edu"

(uri-domain *uri*)
;=> "uci.edu"

(uri-path *uri*)
;=> "/pub/ietf/uri/"

(uri-fragment *uri*)
;=> "Related"
```

## Functions

### \[Function] uri

Parse a string or a byte vector and return a `uri` object.

### \[Function] make-uri

Create a `uri` object.

```common-lisp
(make-uri :scheme "http"
          :host "8arrow.org"
          :path "/")
;=> #<QURI.URI.HTTP:URI-HTTP http://8arrow.org/>

(make-uri :defaults "http://8arrow.org"
          :query '(("guest" . 1)))
;=> #<QURI.URI.HTTP:URI-HTTP http://8arrow.org?guest=1>
```

### \[Function] copy-uri

Return a copy of the given `uri` object.

### \[Function] merge-uris

Merge a reference URI into the base URI as described in RFC 2396 Section 5.2. The returned URI may or may not be a new instance. Neither REFERENCE nor BASE is mutated.

### \[Structure] uri

Structure class as a representation of URIs. The following methods are available for all classes extends this class.

#### Methods

- `uri-scheme`
- `uri-userinfo`
- `uri-host`
- `uri-domain`
- `uri-tld`
- `uri-port`
- `uri-path`
- `uri-authority`
- `render-uri`

### \[Structure] urn (extends uri)

Structure class as a representation of URNs. All methods of `uri` are also available for this class.

#### Methods

- `urn-nid`
- `urn-nss`

### \[Structure] uri-http (extends uri)

Structure class for HTTP/HTTPS URIs.

#### Methods

- `uri-query-params`

```common-lisp
(defvar *uri* (quri:uri "http://quickdocs.org/search?q=web"))

(uri-query-params *uri*)
;=> (("q" . "web"))

(setf (uri-query-params *uri*) '(("q" . "system programming")))

*uri*
;=> #<QURI.URI.HTTP:URI-HTTP http://quickdocs.org/search?q=system%20programming>
```

### \[Structure] uri-ftp (extends uri)

Structure class for FTP URIs.

#### Methods

- `uri-ftp-typecode`

### \[Structure] uri-ldap (extends uri)

Structure class for LDAP/LDAPS URIs.

#### Methods

- `uri-ldap-dn`
- `uri-ldap-attributes`
- `uri-ldap-scope`
- `uri-ldap-filter`
- `uri-ldap-extensions`

### \[Function] url-decode

Decode a Percent-Encoded string or byte vector.

```common-lisp
(url-decode "%2Ffoo%E3%81%82")
;=> "/fooあ"
```

### \[Function] url-decode-params

Decode a [form-urlencoded](http://tools.ietf.org/html/rfc1866#section-8.2.1) string or byte vector and return an association list.

### \[Function] url-encode

Encode a string or a byte vector into a Percent-Encoded string.

```common-lisp
(url-encode "/fooあ")
;=> "%2Ffoo%E3%81%82"
```

### \[Function] url-encode-params

Encode an association list into a [form-urlencoded](http://tools.ietf.org/html/rfc1866#section-8.2.1) string.

## Low-level functions

### \[Function] parse-uri

Parse a URI string or a URI byte vector and return 7 URI components -- scheme, userinfo, host name, port, path, query and fragment.

```common-lisp
(parse-uri "http://www.ics.uci.edu/pub/ietf/uri/#Related")
;=> "http"
;   NIL
;   "www.ics.uci.edu"
;   NIL
;   "/pub/ietf/uri/"
;   NIL
;   "Related"
```

## Installation

```
$ git clone https://github.com/fukamachi/quri
```

```common-lisp
(ql:quickload :quri)
```

## Benchmark

### Parsing URI

- Parsing a URI string 100,000 times.

|  QURI  |  PURI  |
|--------|--------|
| 0.064s | 0.423s |

QURI is **6.6 times faster** than PURI for URI parsing.

#### QURI

```common-lisp
(time
  (dotimes (i 100000)
    (quri:uri "http://www.ics.uci.edu/pub/ietf/uri/#Related")))
```

```
Evaluation took:
  0.064 seconds of real time
  0.063984 seconds of total run time (0.063745 user, 0.000239 system)
  100.00% CPU
  191,340,531 processor cycles
  28,807,728 bytes consed
```

#### PURI

```common-lisp
(time
  (dotimes (i 100000)
    (puri:uri "http://www.ics.uci.edu/pub/ietf/uri/#Related")))
```

```
Evaluation took:
  0.423 seconds of real time
  0.425327 seconds of total run time (0.422234 user, 0.003093 system)
  [ Run times consist of 0.004 seconds GC time, and 0.422 seconds non-GC time. ]
  100.47% CPU
  1,266,663,894 processor cycles
  64,001,408 bytes consed
```

### URL decoding

- Decoding a URL-encoded string 100,000 times.

|  QURI  | Hunchentoot | do-urlencode |
|--------|-------------|--------------|
| 0.029s |    0.089s   |    0.634s    |

QURI is **3 times faster** than Hunchentoot, and **21.8 times faster** than do-urlencode.

#### QURI

```common-lisp
(time
  (dotimes (i 100000)
    (quri:url-decode "foo%E3%81%82")))
```

```
Evaluation took:
  0.029 seconds of real time
  0.028683 seconds of total run time (0.027934 user, 0.000749 system)
  100.00% CPU
  85,421,676 processor cycles
  7,993,456 bytes consed
```

#### Hunchentoot

```common-lisp
(time
  (dotimes (i 100000)
    (hunchentoot:url-decode "foo%E3%81%82")))
```

```
Evaluation took:
  0.089 seconds of real time
  0.088946 seconds of total run time (0.087632 user, 0.001314 system)
  100.00% CPU
  265,341,714 processor cycles
  17,611,968 bytes consed
```

#### do-urlencode

```common-lisp
(time
  (dotimes (i 100000)
    (do-urlencode:urldecode "foo%E3%81%82")))
```

```
Evaluation took:
  0.634 seconds of real time
  0.637236 seconds of total run time (0.632224 user, 0.005012 system)
  [ Run times consist of 0.023 seconds GC time, and 0.615 seconds non-GC time. ]
  100.47% CPU
  1,897,304,959 processor cycles
  153,606,064 bytes consed
```

### URL encoding

- URL-encoding a string 100,000 times.

|  QURI  | Hunchentoot | do-urlencode |
|--------|-------------|--------------|
| 0.074s |    0.282s   |    0.317s    |

QURI is **3.8 times faster** than Hunchentoot, and **4.2 times faster** than do-urlencode.

#### QURI

```common-lisp
(time
  (dotimes (i 100000)
    (quri:url-encode "fooあ")))
```

```
Evaluation took:
  0.074 seconds of real time
  0.074284 seconds of total run time (0.072908 user, 0.001376 system)
  100.00% CPU
  221,267,517 processor cycles
  31,993,520 bytes consed
```

#### Hunchentoot

```common-lisp
(time
  (dotimes (i 100000)
    (hunchentoot:url-encode "fooあ")))
```

```
Evaluation took:
  0.282 seconds of real time
  0.284922 seconds of total run time (0.280063 user, 0.004859 system)
  [ Run times consist of 0.034 seconds GC time, and 0.251 seconds non-GC time. ]
  101.06% CPU
  845,204,850 processor cycles
  214,382,672 bytes consed
```

#### do-urlencode

```common-lisp
(time
  (dotimes (i 100000)
    (do-urlencode:urlencode "fooあ")))
```

```
Evaluation took:
  0.317 seconds of real time
  0.319419 seconds of total run time (0.314339 user, 0.005080 system)
  [ Run times consist of 0.026 seconds GC time, and 0.294 seconds non-GC time. ]
  100.63% CPU
  946,704,912 processor cycles
  219,186,768 bytes consed
```

## Change log

### 0.6.0

- All constructors like `make-uri-file` and `make-uri-https` exported.

- `uri=` and `uri-equal` normalize the path so that NIL and "" are considered equal.

- The `file` scheme renders the query and the fragment.

### 0.5.0

- URI schemes are now read-only.

  This preserves the integrity of the structures (or else the scheme of a
  `uri-http` could be set to FTP).
  
  `merge-uris` has been updated accordingly, so now the following returns the
  right thing:

  ```lisp
  (merge-uris (uri "/") (uri "https://en.wikipedia.org/wiki/URL"))
  ; => #<URI-HTTPS https://en.wikipedia.org/>
  ```

- Prevent some functions from being affected by *PRINT-BASE*.

  Functions `make-uri` and `uri-authority` build strings from a number; they now
  do so with the standard value for `*print-base*`.

### 0.4.0

- Query values accept numbers again.
  This should fix backward-compatibility issues.

- New `uri-equal` which normalizes the path when comparing URIs.

- The empty path and the root path are no longer equal with `uri=`.  Use
  `uri-equal` if you want the old behaviour.

- Dot segments are removed when merging URLs.

- Fix parsing of the colon at the end of the scheme.

### 0.3.0

- Handle strings and byte vectors in query values, and nothing else.

  In particular, numbers are no longer supported.  You'll have to convert them
  to a string or a byte-vector from the caller.

- `parse-uri-string` and `parse-uri-byte-vector` now return the scheme default
  port when unspecified.

## Authors and maintainers

* Eitaro Fukamachi (e.arrows@gmail.com): author
* Pierre Neidhardt (mail@ambrevar.xyz): maintainer

## Copyright

Copyright (c) 2014-2019 Eitaro Fukamachi (e.arrows@gmail.com)

## License

Licensed under the BSD 3-Clause License.
