;Author: Aakash Koneru

; Representation
;
; A path directory is a cons whose CAR is :RELATIVE or :ABSOLUTE and whose CDR
; is a list of segments; each segment is a string or the keyword :BACK. There is
; no distinction between filenames and directories.

; Examples:
;
;   "foo/bar"                 -> (:relative "foo" "bar")
;   "../foo"                  -> (:relative :back "foo")
;   "/foo/bar"                -> (:absolute "foo" "bar")
;   "foo/../bar"              -> (:relative "foo" :back "bar")
;   "."                       -> (:relative)
;


(in-package "FILEPATH")

(include-book "std/strings/top" :dir :system)
(include-book "kestrel/lists-light/prefixp" :dir :system)

(defxdoc paths
  :parents (acl2::kestrel-books)
  :short "A library of file-path operations in ACL2."
  :long
  "<p>A path is represented as a cons of a kind (@(':relative') or
    @(':absolute')) and a list of segments, where each segment is a string or
    the keyword @(':back') (a @('\"..\"') component).  For example,
    @('\"foo/../bar\"') is represented as @('(:relative \"foo\" :back \"bar\")').</p>

   <p>This library deals with paths <i>lexically</i>, as opposed to
    <i>physically</i>: operations look only at the path itself, never at a
    file system.  To illustrate the difference, consider a file path
    @('\"foo/bar\"'), where @('\"bar\"') is a symlink to @('\"/my/dir\"').
    The lexical normalization of @('\"foo/bar/..\"') is @('\"foo\"') (we
    cancel the @('\"..\"') with @('\"bar\"')).  But the physical
    normalization would be @('\"/my\"') (the @('\"foo/bar\"') is replaced
    with its destination first).</p>

   <p>Main operations:</p>
   <ul>
   <li>@('path-p'): recognizer for well-formed paths.</li>
   <li>@('parse-path'): parse a path string (segments separated by
       @('/')) into a path.  @('parse-path-windows') is the analogue for
       backslash-separated strings.</li>
   <li>@('path-to-string'): render a path back into a Unix-style string
       (@('path-to-string-windows') uses backslashes).</li>
   <li>@('resolve'): @('(resolve base p)') interprets @('p') relative to
       @('base').  A relative @('p') is concatenated onto @('base'), while an
       absolute @('p') stands on its own and @('base') is discarded.</li>
   <li>@('normalize-path'): cancel @('\"..\"') segments against the preceding
       segment where possible, e.g. @('\"foo/../bar\"') normalizes to
       @('\"bar\"').</li>
   <li>@('path-parent'): the parent directory of a path.  Trailing
       @(':back') segments are cancelled against the names before them
       (normalizing as little as possible).  A path that is empty or ends in
       an uncancellable @(':back') has no parent and is returned
       unchanged.</li>
   <li>@('basename'): the final component (file name) of a path, as a string.
       Trailing @(':back') segments are cancelled against the names before
       them, as in @('path-parent'); errors on a path in which no name
       survives the cancelling.</li>
   <li>@('path-prefixp'): recognize when one path is a prefix of another (same
       kind, and the first's segments are an initial sublist of the
       second's).</li>
   <li>@('relativize-path'): @('(relativize-path base p)') expresses @('p')
       relative to @('base'), which must be a @('path-prefixp') of @('p');
       errors otherwise.</li>
   </ul>

   <p>Some operations respect normalization and others don't.  @('resolve')
    respects it: normalizing either argument first does not change the
    normalized result. @('path-parent') and @('basename') respect it for the
    end of the path, cancelling trailing @(':back') segments as described above.
    In contrast, @('path-prefixp') and @('relativize-path') compare the literal
    segments and neither perform nor assume normalization. Paths can be normalized explicitly with
    @('normalize-path'), and @('path-equiv') equates paths that normalize to the same thing.</p>")


; Recognizers for the path representation
;----------------------------------------

(defund path-kind-p (x)
  (declare (xargs :guard t))
  (or (eq x :relative) (eq x :absolute)))

(defthm path-kind-compound-recognizer
  (implies (path-kind-p x)
           (symbolp x))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable path-kind-p))))

(defund segment-p (x)
  (declare (xargs :guard t))
  (or (stringp x) (eq x :back)))

(defthm segment-p-compound-recognizer
  (if (segment-p x)
      (or (stringp x)
          (symbolp x))
    (not (stringp x)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable segment-p))))

(defund segment-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (segment-p (car x))
         (segment-listp (cdr x)))))

(defthm true-listp-when-segment-listp
  (if (segment-listp x)
      (true-listp x)
    x)
  :hints (("Goal" :in-theory (enable segment-listp)))
  :rule-classes ((:compound-recognizer)))

(defthm segment-p-of-car-when-segment-listp
  (implies (segment-listp x)
           (equal (segment-p (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable segment-listp))))

(defthm segment-listp-of-cdr
  (implies (segment-listp x)
           (segment-listp (cdr x)))
  :hints (("Goal" :in-theory (enable segment-listp))))

(defthm segment-listp-of-append
  (implies (segment-listp a)
           (equal (segment-listp (append a b))
                  (segment-listp b)))
  :hints (("Goal" :in-theory (enable segment-listp))))

(defthm segment-listp-of-revappend
  (implies (segment-listp a)
           (equal (segment-listp (revappend a b))
                  (segment-listp b)))
  :hints (("Goal" :in-theory (enable segment-listp))))

(defund path-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (path-kind-p (car x))
       (segment-listp (cdr x))))

(defthm consp-when-path-p
  (implies (path-p x)
           (consp x))
  :hints (("Goal" :in-theory (enable path-p)))
  :rule-classes ((:compound-recognizer)))


; Accessors
;--------------------------

(defund path-kind (x)
  (declare (xargs :guard (path-p x)))
  (car x))

(defund path-segments (x)
  (declare (xargs :guard (path-p x)))
  (cdr x))

(defund make-path (kind segs)
  (declare (xargs :guard (and (path-kind-p kind)
                              (segment-listp segs))))
  (cons kind segs))

(defthm path-kind-of-make-path
  (equal (path-kind (make-path kind segs))
         kind)
  :hints (("Goal" :in-theory (enable path-kind make-path))))

(defthm path-segments-of-make-path
  (equal (path-segments (make-path kind segs))
         segs)
  :hints (("Goal" :in-theory (enable path-segments make-path))))

(defthm elim-of-make-path
  (implies (path-p x)
           (equal (make-path (path-kind x)
                             (path-segments x))
                  x))
  :hints (("Goal" :in-theory (enable path-p make-path path-kind
                                     path-segments)))
  :rule-classes ((:elim)))

(defthm path-kind-p-of-path-kind
  (implies (path-p x)
           (path-kind-p (path-kind x)))
  :hints (("Goal" :in-theory (enable path-p path-kind))))

(defthm segment-listp-of-path-segments
  (implies (path-p x)
           (segment-listp (path-segments x)))
  :hints (("Goal" :in-theory (enable path-p path-segments))))

(defthm true-listp-of-path-segments
  (implies (path-p x)
           (true-listp (path-segments x)))
  :hints (("Goal" :in-theory (disable segment-listp-of-path-segments)
                  :use segment-listp-of-path-segments)))

(defthm path-p-of-make-path
  (implies (and (path-kind-p kind)
                (segment-listp segs))
           (path-p (make-path kind segs)))
  :hints (("Goal" :in-theory (enable path-p make-path))))

(defund absolute-path-p (x)
  (declare (xargs :guard (path-p x)))
  (eq (path-kind x) :absolute))

(defund relative-path-p (x)
  (declare (xargs :guard (path-p x)))
  (eq (path-kind x) :relative))

(defthm either-absolute-or-relative-path
  (implies (path-p p)
           (equal (not (absolute-path-p p))
                  (relative-path-p p)))
  :hints (("Goal" :in-theory (enable path-p absolute-path-p relative-path-p
                                     path-kind path-kind-p))))

; Parse-path : String to path.

(defund map-tokens (strs)
  (declare (xargs :guard (string-listp strs)))
  (cond ((atom strs) nil)
        ((equal (car strs) ".")  (map-tokens (cdr strs)))
        ((equal (car strs) "..") (cons :back (map-tokens (cdr strs))))
        (t (cons (car strs) (map-tokens (cdr strs))))))

(local
  (defthm segment-listp-of-map-tokens
    (implies (string-listp strs)
             (segment-listp (map-tokens strs)))
    :hints (("Goal" :in-theory (enable map-tokens segment-listp segment-p)))))

;main (mac/linux)
(defund parse-path (str)
  (declare (xargs :guard (stringp str)))
  (make-path (if (str::strprefixp "/" str) :absolute :relative)
             (map-tokens (str::strtok str (list #\/)))))

(defthm path-p-of-parse-path
  (implies (stringp str)
           (path-p (parse-path str)))
  :hints (("Goal" :in-theory (enable parse-path))))

(defund parse-path-windows (str)
  (declare (xargs :guard (stringp str)))
  (parse-path (str::strsubst "\\" "/" str)))

(defthm path-p-of-parse-path-windows
  (implies (stringp str)
           (path-p (parse-path-windows str)))
  :hints (("Goal" :in-theory (enable parse-path-windows))))


; Path-to-string
;--------------------

(defund seg->string (seg)
  (declare (xargs :guard (segment-p seg)))
  (if (eq seg :back) ".."
    seg))

(defthm stringp-of-seg->string
  (implies (segment-p seg)
           (stringp (seg->string seg)))
  :hints (("Goal" :in-theory (enable seg->string segment-p))))

(defund segs->strings (segs)
  (declare (xargs :guard (segment-listp segs)))
  (if (atom segs)
      nil
    (cons (seg->string (car segs)) (segs->strings (cdr segs)))))

(defthm string-listp-of-segs->strings
  (implies (segment-listp segs)
           (string-listp (segs->strings segs)))
  :hints (("Goal" :in-theory (enable segs->strings))))

(defund path-to-string-sep (pd sep)
  (declare (xargs :guard (and (path-p pd)
                              (stringp sep))))
  (let ((body (str::join (segs->strings (path-segments pd)) sep)))
    (if (eq (path-kind pd) :absolute)
        (str::cat sep body)
      body)))

(defund path-to-string-windows (pd)
  (declare (xargs :guard (path-p pd)))
  (path-to-string-sep pd "\\"))

(defund path-to-string (pd)
  (declare (xargs :guard (path-p pd)))
  (path-to-string-sep pd "/"))

(defthm stringp-of-path-to-string-windows
  (implies (path-p pd)
           (stringp (path-to-string-windows pd)))
  :hints (("Goal" :in-theory (enable path-to-string-windows))))

(defthm stringp-of-path-to-string
  (implies (path-p pd)
           (stringp (path-to-string pd)))
  :hints (("Goal" :in-theory (enable path-to-string))))

;Path resolution
;--------------------

; Resolve the path RIGHT with respect to the base path LEFT: interpret RIGHT as
; being relative to LEFT.  If RIGHT is absolute it stands on its own and LEFT is
; discarded; otherwise RIGHT's segments are concatenated onto LEFT's.

(defund resolve (left right)
  (declare (xargs :guard (and (path-p left)
                              (path-p right))))
  (if (absolute-path-p right)
      right
    (make-path (path-kind left)
               (append (path-segments left)
                       (path-segments right)))))


(defthm resolve-when-absolute
  (implies (absolute-path-p right)
           (equal (resolve left right)
                  right))
  :hints (("Goal" :in-theory (enable resolve))))

(defthm resolve-associative
  (equal (resolve (resolve x y) z)
         (resolve x (resolve y z)))
  :hints (("Goal" :in-theory (enable resolve make-path absolute-path-p
                                     path-kind path-segments))))

;(:relative) is the left identity for resolution
(defthm resolve-left-identity
  (implies (path-p p)
           (equal (resolve (make-path :relative nil) p)
                  p))
  :hints (("Goal" :in-theory (enable path-p path-kind-p resolve make-path
                                     absolute-path-p
                                     path-kind path-segments))))

(defthm resolve-right-identity
  (implies (path-p p)
           (equal (resolve p (make-path :relative nil))
                  p))
  :hints (("Goal" :in-theory (enable path-p resolve make-path
                                     absolute-path-p
                                     path-kind path-segments))))

(defthm path-kind-of-resolve
  (equal (path-kind (resolve left right))
         (if (absolute-path-p right)
             (path-kind right)
           (path-kind left)))
  :hints (("Goal" :in-theory (enable resolve make-path absolute-path-p
                                     path-kind))))


;Path normalization
;--------------------

; A path is normal when no segment cancels with a following :back, since "foo/.."
; is just "."

(defund cancel-backs (segs)
  (declare (xargs :guard (segment-listp segs)))
  (if (atom segs)
      nil
    (let ((rest (cancel-backs (cdr segs))))
      (if (and (not (eq (car segs) :back))
               (consp rest)
               (eq (car rest) :back))
          (cdr rest)
        (cons (car segs) rest)))))

(defund drop-leading-backs (segs)
  (declare (xargs :guard (segment-listp segs)))
  (if (and (consp segs) (eq (car segs) :back))
      (drop-leading-backs (cdr segs))
    segs))

(defthm segment-listp-of-cancel-backs
  (implies (segment-listp segs)
           (segment-listp (cancel-backs segs)))
  :hints (("Goal" :in-theory (enable cancel-backs segment-listp))))

(defthm segment-listp-of-drop-leading-backs
  (implies (segment-listp segs)
           (segment-listp (drop-leading-backs segs)))
  :hints (("Goal" :in-theory (enable drop-leading-backs))))

(defund normalize-segments (segs kind)
  (declare (xargs :guard (segment-listp segs)))
  (if (eq kind :absolute)
      (drop-leading-backs (cancel-backs segs))
    (cancel-backs segs)))

(defthm segment-listp-of-normalize-segments
  (implies (segment-listp segs)
           (segment-listp (normalize-segments segs kind)))
  :hints (("Goal" :in-theory (enable normalize-segments))))

(defund normalize-path (p)
  (declare (xargs :guard (path-p p)))
  (make-path (path-kind p)
             (normalize-segments (path-segments p)
                                 (path-kind p))))

(defund no-back-p (segs)
  (declare (xargs :guard t))
  (or (atom segs)
      (and (not (eq (car segs) :back))
           (no-back-p (cdr segs)))))

(defund normal-relative-segments-p (segs)
  (declare (xargs :guard t))
  (if (atom segs)
      t
    (if (eq (car segs) :back)
        (normal-relative-segments-p (cdr segs))
      (no-back-p segs))))

(defund normal-path-p (p)
  (declare (xargs :guard (path-p p)))
  (if (eq (path-kind p) :absolute)
      (no-back-p (path-segments p))
    (normal-relative-segments-p (path-segments p))))


; Idempotence: normalizing an already-normal path changes nothing.
;-----------------

(defthm normal-relative-when-no-back
  (implies (no-back-p segs)
           (normal-relative-segments-p segs))
  :hints (("Goal" :in-theory (enable no-back-p normal-relative-segments-p))))

(defthm normal-relative-of-cancel-backs
  (normal-relative-segments-p (cancel-backs segs))
  :hints (("Goal" :in-theory (enable cancel-backs normal-relative-segments-p
                                     no-back-p))))

(defthm cancel-backs-when-normal-relative
  (implies (and (normal-relative-segments-p segs)
                (true-listp segs))
           (equal (cancel-backs segs) segs))
  :hints (("Goal" :in-theory (enable cancel-backs normal-relative-segments-p
                                     no-back-p))))

(defthm no-back-p-of-drop-leading-backs-when-normal-relative
  (implies (normal-relative-segments-p segs)
           (no-back-p (drop-leading-backs segs)))
  :hints (("Goal" :in-theory (enable drop-leading-backs normal-relative-segments-p
                                     no-back-p))))

; normalize-path always produces a normal path.
(defthm normal-path-p-of-normalize-path
  (implies (path-p p)
           (normal-path-p (normalize-path p)))
  :hints (("Goal" :in-theory (enable normal-path-p normalize-path
                                     normalize-segments))))

(defthm drop-leading-backs-when-no-back
  (implies (no-back-p segs)
           (equal (drop-leading-backs segs) segs))
  :hints (("Goal" :in-theory (enable drop-leading-backs no-back-p))))

(defthm true-listp-of-drop-leading-backs
  (implies (true-listp segs)
           (true-listp (drop-leading-backs segs)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable drop-leading-backs))))

(defthm normalize-segments-idempotent
  (equal (normalize-segments (normalize-segments segs kind) kind)
         (normalize-segments segs kind))
  :hints (("Goal" :in-theory (enable normalize-segments))))

(defthm normalize-path-when-normal-path-p
  (implies (and (normal-path-p p)
                (path-p p))
           (equal (normalize-path p)
                  p))
  :hints (("Goal" :in-theory (enable normalize-path normalize-segments
                                     normal-path-p path-p make-path
                                     path-kind path-segments))))

(defthm normalize-path-idempotent
  (equal (normalize-path (normalize-path p))
         (normalize-path p))
  :hints (("Goal" :in-theory (enable normalize-path make-path
                                     path-kind path-segments))))


;Normalization vs Resolution
;--------------------

; Pre-normalizing either path before concatenating does not change the
; result.

(defthm cancel-backs-of-append-right-cancel-backs
  (equal (cancel-backs (append a (cancel-backs b)))
         (cancel-backs (append a b)))
  :hints (("Goal" :in-theory (enable cancel-backs))))

(defthm normalize-segments-of-append-right-cancel-backs
  (equal (normalize-segments (append a (cancel-backs b)) kind)
         (normalize-segments (append a b) kind))
  :hints (("Goal" :in-theory (enable normalize-segments))))

(local
  (defthm cancel-backs-of-cons-back
    (equal (cancel-backs (cons :back l))
           (cons :back (cancel-backs l)))
    :hints (("Goal" :in-theory (enable cancel-backs)))))

(defthm cancel-backs-of-append-left-cancel-backs
  (equal (cancel-backs (append (cancel-backs a) b))
         (cancel-backs (append a b)))
  :hints (("Goal" :in-theory (enable cancel-backs))))

(local
  (defthm drop-leading-backs-of-cons-back
    (equal (drop-leading-backs (cons :back x))
           (drop-leading-backs x))
    :hints (("Goal" :in-theory (enable drop-leading-backs)))))

(local
  (defthm drop-leading-backs-cancel-backs-of-append-drop-leading-backs
    (equal (drop-leading-backs
             (cancel-backs (append (drop-leading-backs c) b)))
           (drop-leading-backs (cancel-backs (append c b))))
    :hints (("Goal" :induct (drop-leading-backs c)
                    :in-theory (enable drop-leading-backs)))))

(defthm normalize-segments-of-append-left-normalize-segments
  (equal (normalize-segments (append (normalize-segments a kind) b) kind)
         (normalize-segments (append a b) kind))
  :hints (("Goal" :in-theory (enable normalize-segments))))

(defthm normalize-resolve-of-normalize-left
  (equal (normalize-path (resolve (normalize-path p) q))
         (normalize-path (resolve p q)))
  :hints (("Goal" :in-theory (enable normalize-path resolve make-path
                                     absolute-path-p
                                     path-kind path-segments))))

(defthm normalize-resolve-of-normalize-right
  (equal (normalize-path (resolve p (normalize-path q)))
         (normalize-path (resolve p q)))
  :hints (("Goal" :in-theory (enable normalize-path resolve make-path
                                     relative-path-p absolute-path-p
                                     normalize-segments
                                     path-kind path-segments))))


;Equivalence relation
;---------------------

(defund path-equiv (x y)
  (declare (xargs :guard (and (path-p x)
                              (path-p y))))
  (equal (normalize-path x) (normalize-path y)))

(defequiv path-equiv
  :hints (("Goal" :in-theory (enable path-equiv))))

(defthm normalize-path-preserves-path-equiv
  (implies (path-equiv x y)
           (path-equiv (normalize-path x) (normalize-path y)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable path-equiv))))

(defthm normalize-path-is-path-equiv
  (path-equiv (normalize-path p) p)
  :hints (("Goal" :in-theory (enable path-equiv))))


; Path-parent
;--------------------

; The directory containing a file path: drop the last segment, after first
; cancelling any trailing :backs against the names before them (normalizing as
; little as possible). A path that is empty or reduces to trailing
; uncancellable :backs has no parent and is returned unchanged.

(defund name-survives-p (segs)
  (declare (xargs :guard (segment-listp segs)))
  (consp (drop-leading-backs (cancel-backs segs))))

(defund parent-segments (segs)
  (declare (xargs :guard (segment-listp segs)))
  (cond ((atom segs) segs)
        ((not (name-survives-p segs)) segs)
        ((not (name-survives-p (cdr segs))) nil)
        (t (cons (car segs) (parent-segments (cdr segs))))))

(defthm segment-listp-of-parent-segments
  (implies (segment-listp segs)
           (segment-listp (parent-segments segs)))
  :hints (("Goal" :in-theory (enable parent-segments segment-listp))))

(defund path-parent (p)
  (declare (xargs :guard (path-p p)))
  (make-path (path-kind p)
             (parent-segments (path-segments p))))

(defthm path-p-of-path-parent
  (implies (path-p p)
           (path-p (path-parent p)))
  :hints (("Goal" :in-theory (enable path-parent))))


; Basename
;--------------------

; Interpreting a path as a file path, basename returns its last segment (the
; file name) as a string, after first cancelling any trailing :backs against
; the names before them. A path in which no name survives the cancelling has no basename.

(defund last-name (segs)
  (declare (xargs :guard (segment-listp segs)))
  (cond ((atom segs) nil)
        ((name-survives-p (cdr segs)) (last-name (cdr segs)))
        ((name-survives-p segs) (car segs))
        (t nil)))

(local
  (defthm name-survives-p-of-cons
    (implies (name-survives-p segs)
             (name-survives-p (cons seg segs)))
    :hints (("Goal" :in-theory (enable name-survives-p cancel-backs
                                       drop-leading-backs)))))

(local
  (defthm stringp-of-last-name
    (implies (segment-listp segs)
             (equal (stringp (last-name segs))
                    (name-survives-p segs)))
    :hints (("Goal" :in-theory (enable last-name name-survives-p cancel-backs
                                       drop-leading-backs segment-listp)))))

(defund basename (p)
  (declare (xargs :guard (path-p p)))
  (let ((segs (path-segments p)))
    (if (name-survives-p segs)
        (last-name segs)
      (er hard? 'basename
          "The path ~x0 has no name segments, so it has no basename." p))))

(defthm stringp-of-basename
  (implies (path-p p)
           (equal (stringp (basename p))
                  (name-survives-p (path-segments p))))
  :hints (("Goal" :in-theory (enable basename))))


; Relativize-path
;--------------------

; Make a path relative to a base path that is a prefix of it.  base is a prefix
; of p when they have the same kind. Relativize-path returns the relative path of the remaining segments.

(defund segments-after-prefix (a b)
  (declare (xargs :guard (and (segment-listp a)
                              (segment-listp b))))
  (if (atom a)
      b
    (segments-after-prefix (cdr a) (cdr b))))

(defthm segment-listp-of-segments-after-prefix
  (implies (segment-listp b)
           (segment-listp (segments-after-prefix a b)))
  :hints (("Goal" :in-theory (enable segments-after-prefix))))

(defthm append-of-segments-after-prefix-when-prefixp
  (implies (acl2::prefixp a b)
           (equal (append a (segments-after-prefix a b))
                  b))
  :hints (("Goal" :in-theory (enable acl2::prefixp segments-after-prefix))))

(defund path-prefixp (base p)
  (declare (xargs :guard (and (path-p base)
                              (path-p p))))
  (and (eq (path-kind base) (path-kind p))
       (acl2::prefixp (path-segments base)
                      (path-segments p))))

(defund relativize-path (base p)
  (declare (xargs :guard (and (path-p base)
                              (path-p p))))
  (if (path-prefixp base p)
      (make-path :relative
                 (segments-after-prefix (path-segments base)
                                        (path-segments p)))
    (er hard? 'relativize-path
        "~x0 is not a prefix of ~x1." base p)))

(defthm relative-path-p-of-relativize-path
  (implies (path-prefixp base p)
           (relative-path-p (relativize-path base p)))
  :hints (("Goal" :in-theory (enable relativize-path relative-path-p))))

(defthm path-p-of-relativize-path
  (implies (and (path-p base)
                (path-p p)
                (path-prefixp base p))
           (path-p (relativize-path base p)))
  :hints (("Goal" :in-theory (enable relativize-path))))

(defthm path-equiv-of-resolve-of-relativize-path
  (implies (and (path-p base)
                (path-p p)
                (path-prefixp base p))
           (path-equiv (resolve base (relativize-path base p))
                       p))
  :hints (("Goal" :in-theory (enable relativize-path path-equiv resolve
                                     absolute-path-p relative-path-p
                                     path-prefixp path-p))))

(local
  (defthm segments-after-prefix-of-append
    (equal (segments-after-prefix a (append a b))
           b)
    :hints (("Goal" :in-theory (enable segments-after-prefix)))))

(defthm relativize-path-of-resolve
  (implies (and (path-p base)
                (path-p r)
                (relative-path-p r))
           (equal (relativize-path base (resolve base r))
                  r))
  :hints (("Goal" :in-theory (enable relativize-path resolve path-prefixp
                                     relative-path-p absolute-path-p path-p
                                     make-path path-kind path-segments))))


;Tests
;---------------------

; Parsing

(assert-event (equal (parse-path "foo/bar")
                     (make-path :relative (list "foo" "bar"))))
(assert-event (equal (parse-path "/foo/bar")
                     (make-path :absolute (list "foo" "bar"))))
(assert-event (equal (parse-path "../foo")
                     (make-path :relative (list :back "foo"))))
(assert-event (equal (parse-path "foo/../bar")
                     (make-path :relative (list "foo" :back "bar"))))
(assert-event (equal (parse-path ".")
                     (make-path :relative nil)))
(assert-event (equal (parse-path "/")
                     (make-path :absolute nil)))

(assert-event (equal (parse-path-windows "foo\\bar")
                     (make-path :relative (list "foo" "bar"))))
(assert-event (equal (parse-path-windows "\\foo\\bar")
                     (make-path :absolute (list "foo" "bar"))))

; Printing

(assert-event (equal (path-to-string (make-path :relative (list "foo" "bar")))  "foo/bar"))
(assert-event (equal (path-to-string (make-path :absolute (list "foo" "bar")))  "/foo/bar"))
(assert-event (equal (path-to-string (make-path :relative (list :back "foo")))  "../foo"))
(assert-event (equal (path-to-string (make-path :absolute nil))                 "/"))
(assert-event (equal (path-to-string-windows (make-path :relative (list "foo" "bar"))) "foo\\bar"))
