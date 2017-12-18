This package contains an implementation of RFC 2388, which is used to
process form data posted with HTTP POST method using enctype
"multipart/form-data".

The main functions of interest are PARSE-MIME and PARSE-HEADER.

Use PARSE-MIME to parse MIME content. It can be given either a string
or a stream. It returns a list of MIME parts. The second argument must
be a boundary, which is a string that seperates MIME parts. See below
how to obtain it.

PARSE-HEADER is used by PARSE-MIME internally, but you can use it to
parse headers yourself. For instance, when data is posted to server
using POST method, a header describing the content type is sent as
well. Usually its content is application/x-www-form-urlencoded or
something similar. But users may set it to multipart/form-data, with
additional parameter named "boundary". This is how one would usually
parse the posted data:

```lisp
(let* ((header (parse-header <request-content-type> :value))
       (boundary (or (assoc "boundary" (header-parameters header)
                            :test #'string-equal)
                     (error "Form data is missing a boundary: ~S"
                            <request-content-type>))))
  (parse-mime <request-posted-content> boundary))
```
      
The :VALUE keyword parameter to PARSE-HEADER means that parsing should
begin with header value, not name (because header name is
"content-type" and the web server has already seperated them, at least
in this scenario).
