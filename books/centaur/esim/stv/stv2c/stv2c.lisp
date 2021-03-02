; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

; Added 10/17/2013 by Matt K.: Making this hons-only, because the proof of
; RETURN-TYPE-OF-STV2C-OUTPUT-STUFF-AUX seems to bog down in ACL2 as opposed to
; ACL2(h), perhaps because worse-than needs to be memoized.
; NOTE: perhaps this no longer needs to be hons-only, given the new clocked
; scheme for the "worse-than" algorithm (see source function
; worse-than-builtin-clocked).
; cert_param: (hons-only)

; stv2c.lisp -- translates STVs into C++ functions
;
; Original author: Jared Davis

(in-package "ACL2")
(include-book "../stv-util")
(include-book "centaur/aig/aig2c" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-vars-1pass" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-to-faig" :dir :system)
(local (include-book "std/io/base" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))

#||
(include-book ;; Handy for testing
 "centaur/esim/tutorial/alu16-book" :dir :system)
||#

(define stv2c-tailchar-p ((x characterp))
  :parents (stv2c-c-symbol-name)
  (or (str::dec-digit-char-p x)
      (str::down-alpha-p x)
      (str::up-alpha-p x)
      (eql x #\_)))

(std::deflist stv2c-tailchars-p (x)
  (stv2c-tailchar-p x)
  :guard (character-listp x)
  :parents (stv2c-c-symbol-name))

(define stv2c-c-symbol-name
  :parents (stv2c)
  :short "Convert STV input/output names into similar C++ names."
  ((x "A user-level STV input/output name."))
  :returns (str stringp :rule-classes :type-prescription)
  (b* (((unless (symbolp x))
        (raise "Expected STV names to be symbols, found ~x0." x)
        "")
       (name   (symbol-name x))
       (c-name (str::downcase-string (str::strsubst "-" "_" name)))
       (chars  (str::explode c-name))
       ((unless (consp chars))
        (raise "Empty symbol-name used in the STV?")
        "")
       ((cons head tail) chars)
       ((unless (and (or (str::down-alpha-p head)
                         (str::up-alpha-p head)
                         (eql head #\_))
                     (stv2c-tailchars-p tail)))
        (raise "Can't translate name ~x0 into a nice C name." x)
        ""))
    c-name))

(std::defprojection stv2c-c-symbol-names (x)
  (stv2c-c-symbol-name x)
  :guard t
  :result-type string-listp
  :parents (stv2c))



; We will create a structure for the inputs, and a structure for the outputs,
; and a run function.

(define stv2c-ins-structname ((stv processed-stv-p))
  :parents (stv2c-ins-structdef)
  (b* (((processed-stv stv) stv)
       (c-name (stv2c-c-symbol-name stv.name)))
    (str::cat c-name "_ins")))

(define stv2c-ins-structfields
  :parents (stv2c-ins-structdef)
  ((ins "Initially the @(see stv->ins) from the stv.")
   (stv processed-stv-p)
   acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (atom ins))
        acc)
       ((unless (symbolp (car ins)))
        (raise "STV input not a symbol? ~x0" (car ins))
        acc)
       (c-name (stv2c-c-symbol-name (car ins)))
       (width  (stv-in->width (car ins) stv))
       (acc    (str::revappend-chars "    fourval<" acc))
       (acc    (str::revappend-chars (str::natstr width) acc))
       (acc    (str::revappend-chars "> " acc))
       (acc    (str::revappend-chars c-name acc))
       (acc    (str::revappend-chars ";" acc))
       (acc    (cons #\Newline acc)))
    (stv2c-ins-structfields (cdr ins) stv acc)))

(define stv2c-ins-structdef ((stv processed-stv-p)
                            acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  :parents (stv2c)
  :short "Structure definition for the STV inputs."
  (b* ((ins          (stv->ins stv))
       (c-structname (stv2c-ins-structname stv))
       (c-fieldnames (stv2c-c-symbol-names ins))
       ((unless (uniquep c-fieldnames))
        (raise "Name clash for STV input C names: ~x0."
               (duplicated-members c-fieldnames)))
       (acc (str::revappend-chars "class " acc))
       (acc (str::revappend-chars c-structname acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "{" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "  public:" acc))
       (acc (cons #\Newline acc))
       (acc (stv2c-ins-structfields ins stv acc))
       (acc (str::revappend-chars "};" acc))
       (acc (cons #\Newline acc)))
    acc))


(define stv2c-outs-structname ((stv processed-stv-p))
  :parents (stv2c-outs-structdef)
  (b* (((processed-stv stv) stv)
       (c-name (stv2c-c-symbol-name stv.name)))
    (str::cat c-name "_outs")))

(define stv2c-outs-structfields
  :parents (stv2c-outs-structdef)
  ((outs "Initially the @(see stv->outs) from the stv.")
   (stv processed-stv-p)
   acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (atom outs))
        acc)
       ((unless (symbolp (car outs)))
        (raise "STV output not a symbol? ~x0" (car outs))
        acc)
       (c-name (stv2c-c-symbol-name (car outs)))
       (width  (stv-out->width (car outs) stv))
       (acc    (str::revappend-chars "    fourval<" acc))
       (acc    (str::revappend-chars (str::natstr width) acc))
       (acc    (str::revappend-chars "> " acc))
       (acc    (str::revappend-chars c-name acc))
       (acc    (str::revappend-chars ";" acc))
       (acc    (cons #\Newline acc)))
    (stv2c-outs-structfields (cdr outs) stv acc)))

(define stv2c-outs-structdef ((stv processed-stv-p)
                              acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  :parents (stv2c)
  :short "Structure definition for the STV outputs."
  (b* ((outs         (stv->outs stv))
       (c-structname (stv2c-outs-structname stv))
       (c-fieldnames (stv2c-c-symbol-names outs))
       ((unless (uniquep c-fieldnames))
        (raise "Name clash for STV output C names: ~x0."
               (duplicated-members c-fieldnames)))
       (acc (str::revappend-chars "class " acc))
       (acc (str::revappend-chars c-structname acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "{" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "  public:" acc))
       (acc (cons #\Newline acc))
       (acc (stv2c-outs-structfields outs stv acc))
       (acc (str::revappend-chars "};" acc))
       (acc (cons #\Newline acc)))
    acc))


(define stv2c-run-fnname ((stv processed-stv-p))
  :parents (stv2c-header)
  (b* (((processed-stv stv) stv)
       (c-name (stv2c-c-symbol-name stv.name)))
    (str::cat c-name "_run")))

(define stv2c-header
  :parents (stv2c)
  :short "Generate the header file for an STV."
  ((stv processed-stv-p)
   acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* ((in-struct  (stv2c-ins-structname stv))
       (out-struct (stv2c-outs-structname stv))
       (run-fn     (stv2c-run-fnname stv))

       (acc (str::revappend-chars "#pragma once

// Warning: Automatically generated file!
// Do not hand edit!

#include \"fourval.h\"

" acc))
       (acc (stv2c-ins-structdef stv acc))
       (acc (cons #\Newline acc))
       (acc (stv2c-outs-structdef stv acc))
       (acc (cons #\Newline acc))
       (tmp (str::cat "void " run-fn))
       (acc (str::revappend-chars tmp acc))
       (acc (str::revappend-chars
             (str::cat "(const " in-struct "& in,")
             acc))
       (acc (cons #\Newline acc))
       (acc (make-list-ac (+ 1 (length tmp)) #\Space acc))
       (acc (str::revappend-chars (str::cat out-struct "& out);") acc))
       (acc (cons #\Newline acc)))
    acc))

#||
; Example:
(str::rchars-to-string
 (stv2c-header (alu16-test-vector) nil))
||#


; Actual code generation.
;
; For now we're going to just piggy-back on aig2c.  The first step toward this
; is to convert all the sexprs into FAIGs.  Mostly to do this we just need a
; suitable onoff alist.  We'll generate one in a way that shouldn't create name
; clashes, and is still mostly readable.

(define suffix-symbols ((symbols symbol-listp)
                        (suffix stringp))
  (if (atom symbols)
      nil
    (cons (intern$ (str::cat (symbol-name (car symbols)) suffix) "ACL2")
          (suffix-symbols (cdr symbols) suffix))))

(define stv2c-onoff ((stv processed-stv-p))
  ;; Makes the onoff alist for translating sexprs to faigs.
  (b* ((cstv          (processed-stv->compiled-stv stv))
       (in-usersyms   (compiled-stv->in-usersyms cstv))
       (flat-usersyms (flatten (alist-vals in-usersyms)))
       ((unless (symbol-listp flat-usersyms))
        (raise "expected input usersyms to be symbols!"))
       ((unless (uniquep flat-usersyms))
        (raise "name clash in usersyms? ~x0." (duplicated-members flat-usersyms)))
       (onsets  (suffix-symbols flat-usersyms "_ON"))
       (offsets (suffix-symbols flat-usersyms "_OFF"))
       ((unless (uniquep onsets))
        (raise "name clash for onsets: ~x0." (duplicated-members onsets)))
       ((unless (uniquep offsets))
        (raise "name clash for offsets: ~x0." (duplicated-members offsets))))
    (pairlis$ flat-usersyms
              (pairlis$ onsets offsets))))

#||
; Example:
(stv2c-onoff (alu16-test-vector))
||#


; The STV's relevant-signals alist binds each output bit name to a sexpr.  We
; can now translate these, to produce a list where each output bit name is
; bound to an FAIG, in terms of the onset/offset variables above.

(define stv2c-relevant-faigs ((stv processed-stv-p))
  :returns (faig-alist "binds out/int simulation variable bits to faigs")
  (b* ((onoff                (stv2c-onoff stv))
       (relevant-sexpr-alist (processed-stv->relevant-signals stv))
       (out-bit-names        (alist-keys relevant-sexpr-alist))
       (sexprs               (alist-vals relevant-sexpr-alist))
       (used-vars            (4v-sexpr-vars-1pass-list sexprs))  ;; a set
       (bound-vars           (set::mergesort (alist-keys onoff)))
       (unbound-vars         (set::difference used-vars bound-vars))
       ((unless (set::empty unbound-vars))
        (raise "variables used in relevant sexprs, but not bound in onoff: ~x0."
               unbound-vars))
       ;; Else looks okay, go ahead and translate.  We'll at least do
       ;; basic 3v optimization here.
       (faigs (with-fast-alist onoff
                (4v-sexpr-to-faig-opt-list sexprs onoff))))
    (pairlis$ out-bit-names faigs)))

#||
; This is hard to demo.
(plev)
(stv2c-relevant-faigs (alu16-test-vector))
||#


; Now we need to create the input alist for aig2c.  This needs to be an alist
; that maps the AIG variables to the C expressions that should drive them.

(define stv2c-input-name-alist-aux
  ;; Maps a single usersyms entry, like:
  ;;   foo -> (foo[3] foo[4] foo[5] foo[6])
  ;;
  ;; Into an input alist mapping AIG variables to C names, e.g.,
  ;;   foo[3]_ON -> "in.foo.onset.getBit(0)"
  ;;   foo[3]_OFF -> "in.foo.offset.getBit(0)"
  ;;   ...
  ;;   foo[6]_OFF -> "in.foo.onset.getBit(3)"
  ;;   foo[6]_OFF -> "in.foo.offset.getBit(3)"
  ((c-name     stringp "C name of a field from the _ins structure, e.g., foo")
   (index      natp    "Position to use for getBit calls, initially 0, counts up.")
   (sexpr-vars symbol-listp "List of sexpr vars we're processing, e.g.,
                               e.g., (foo[3] foo[4] foo[5] foo[6])")
   (onoff "Alist binding sexpr vars to faig on/off variable pairs, e.g.,
              foo[3] to (foo[3]_ON . foo[3]_OFF)"))
  (b* (((when (atom sexpr-vars))
        nil)
       (sexpr-var (car sexpr-vars))
       (faig-vars (cdr (hons-get sexpr-var onoff)))
       ((unless (consp faig-vars))
        (raise "No onoff binding for ~x0" sexpr-var))
       ((cons on off) faig-vars)
       (index-str (str::natstr index))
       (c-onset-rhs   (str::cat "in." c-name ".onset.getBit(" index-str ")"))
       (c-offset-rhs  (str::cat "in." c-name ".offset.getBit(" index-str ")")))
    (list* (cons on c-onset-rhs)
           (cons off c-offset-rhs)
           (stv2c-input-name-alist-aux c-name (+ 1 index) (cdr sexpr-vars) onoff))))

(define stv2c-input-name-alist (in-usersyms onoff)
  (b* (((when (atom in-usersyms))
        nil)
       ((when (atom (car in-usersyms)))
        (raise "In-usersyms isn't even an alist?"))
       ((cons user-name sexpr-vars) (car in-usersyms))
       (c-fieldname (stv2c-c-symbol-name user-name))
       ((unless (symbol-listp sexpr-vars))
        (raise "In-usersyms has non symbols?")))
    (append (stv2c-input-name-alist-aux c-fieldname 0 sexpr-vars onoff)
            (stv2c-input-name-alist (cdr in-usersyms) onoff))))

#||
; Example:
(b* ((stv         (alu16-test-vector))
     (cstv        (processed-stv->compiled-stv stv))
     (in-usersyms (compiled-stv->in-usersyms cstv))
     (onoff       (stv2c-onoff stv)))
  (with-fast-alist onoff
    (stv2c-input-name-alist in-usersyms onoff)))
||#


; The other thing that aig2c needs is an alist of Name -> AIG.  This isn't quite
; what we have after stv2c-relevant-faigs.  We have an alist of the form
;    (Lisp) Bit Name -> FAIG.
; So we're going to need twice as many names.  Well, we don't need these to be
; especially readable, so let's just throw something together.

(define stv2c-stupid-names ((prefix stringp)
                            (n natp)
                            acc)
  :returns (names string-listp :hyp (string-listp acc))
  (b* (((when (zp n))
        acc)
       (n (- n 1))
       (name (str::cat prefix (str::natstr n)))
       (acc  (cons name acc)))
    (stv2c-stupid-names prefix n acc))
  ///
  (defthm true-listp-stv2c-stupid-names
    (implies (true-listp acc)
             (true-listp (stv2c-stupid-names prefix n acc)))
    :rule-classes :type-prescription))

(define stv2c-c-bool-declarations ((names string-listp)
                                   acc)
  (b* (((when (atom names))
        acc)
       (acc (str::revappend-chars "  bool " acc))
       (acc (str::revappend-chars (car names) acc))
       (acc (cons #\; acc))
       (acc (cons #\Newline acc)))
    (stv2c-c-bool-declarations (cdr names) acc)))

#||
(str::rchars-to-string
 (stv2c-c-bool-declarations (list "blah1" "blah2" "blah3")
                            nil))
||#

(define stv2c-out-renaming-alist (bit-names)
  ;; Maps the sexpr bit names to temporary C names
  (b* ((num-names    (len bit-names))
       (onset-names  (stv2c-stupid-names "res_on_" num-names nil))
       (offset-names (stv2c-stupid-names "res_off_" num-names nil)))
    (pairlis$ (list-fix bit-names)
              (pairlis$ onset-names offset-names))))

#||
(b* ((stv (alu16-test-vector))
     (relevant-sexprs (processed-stv->relevant-signals stv))
     (bit-names (alist-keys relevant-sexprs)))
  (stv2c-out-renaming-alist bit-names))
||#

(define stv2c-aig-alist-aux (relevant-faigs
                             renaming-alist)
  (b* (((when (atom relevant-faigs))
        nil)

       ((unless (and (consp (car relevant-faigs))
                     (consp (cdar relevant-faigs))))
        (raise "relevant-faig entry isn't well-formed?: ~x0" (car relevant-faigs)))

       ((cons bit-name (cons on-aig off-aig)) (car relevant-faigs))
       (renaming (cdr (hons-get bit-name renaming-alist)))
       ((unless (and (consp renaming)
                     (stringp (car renaming))
                     (stringp (cdr renaming))))
        (raise "renaming-alist for ~x0 is crazy: ~x1." bit-name renaming))

       ((cons on-name off-name) renaming))

    (list* (cons (str::cat "const bool " on-name) on-aig)
           (cons (str::cat "const bool " off-name) off-aig)
           (stv2c-aig-alist-aux (cdr relevant-faigs) renaming-alist))))

#||
(plev)
(b* ((stv            (alu16-test-vector))
     (relevant-faigs (stv2c-relevant-faigs stv))
     (bit-names      (alist-keys relevant-faigs))
     (renaming-alist (stv2c-out-renaming-alist bit-names)))
  (with-fast-alist renaming-alist
    (stv2c-aig-alist-aux relevant-faigs renaming-alist)))
||#

(define stv2c-output-stuff-aux
  ;; Consider an out-usersyms entry entry, like:
  ;;   ans -> (ans[3] ans[4] ans[5] ans[6])
  ((c-name     stringp "C name of the field, e.g., ans")
   (index      natp    "Position to use for setBit calls, initially 0, counts up.")
   (sexpr-vars symbol-listp
               "List of sexpr vars we're processing, e.g.,
                 (ans[3] ans[4] ans[5] ans[6])")
   (renaming-alist
    "Mapping of sexpr-vars to their temporary C onset/offset names.")
   (acc "Character accumulator, reverse order as usual."))
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (atom sexpr-vars))
        acc)
       (onoff (cdr (hons-get (car sexpr-vars) renaming-alist)))
       ((unless (and (consp onoff)
                     (stringp (car onoff))
                     (stringp (cdr onoff))))
        (raise "Bad renaming-alist entry for ~x0: ~x1."
               (car sexpr-vars) onoff)
        acc)
       ((cons on off) onoff)
       (index-str (str::natstr index))
       (acc (str::revappend-chars
             (str::cat "  out." c-name ".onset.cpyBit(" index-str ", " on ");")
             acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars
             (str::cat "  out." c-name ".offset.cpyBit(" index-str ", " off ");")
             acc))
       (acc (cons #\Newline acc)))
    (stv2c-output-stuff-aux c-name (+ 1 index) (cdr sexpr-vars)
                            renaming-alist acc)))

(define stv2c-output-stuff (out-usersyms renaming-alist acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (atom out-usersyms))
        acc)
       ((when (atom (car out-usersyms)))
        (raise "Out-usersyms isn't even an alist?")
        acc)
       ((cons user-name sexpr-vars) (car out-usersyms))
       (c-fieldname (stv2c-c-symbol-name user-name))
       ((unless (symbol-listp sexpr-vars))
        (raise "out-usersyms has non symbols?"))
       (acc
        (stv2c-output-stuff-aux c-fieldname 0 sexpr-vars renaming-alist acc)))
    (stv2c-output-stuff (cdr out-usersyms) renaming-alist acc)))

#||
; Example:
(b* ((stv             (alu16-test-vector))
     (cstv            (processed-stv->compiled-stv stv))
     (out-usersyms    (compiled-stv->out-usersyms cstv))
     (relevant-sexprs (processed-stv->relevant-signals stv))
     (bit-names       (alist-keys relevant-sexprs))
     (renaming-alist  (stv2c-out-renaming-alist bit-names)))
  (str::rchars-to-string
   (with-fast-alist renaming-alist
     (stv2c-output-stuff out-usersyms renaming-alist nil))))
||#


(define stv2c-make-run-fn ((stv processed-stv-p)
                           acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* ((cstv           (processed-stv->compiled-stv stv))
       (in-usersyms    (compiled-stv->in-usersyms cstv))
       (out-usersyms   (compiled-stv->out-usersyms cstv))
       (onoff          (stv2c-onoff stv))
       (relevant-faigs (stv2c-relevant-faigs stv))
       (bit-names      (alist-keys relevant-faigs))
       (renaming-alist (stv2c-out-renaming-alist bit-names))
       ((with-fast renaming-alist onoff))
       (aig-alist   (stv2c-aig-alist-aux relevant-faigs renaming-alist))
       (input-names (stv2c-input-name-alist in-usersyms onoff))
       (config      (make-aig2c-config :prefix "_temp"
                                       :type "const bool"
                                       :op-and "&&"
                                       :op-not "!"))
       ((unless (string-listp (alist-vals input-names)))
        (raise "Bad input names.")
        acc)
       ((unless (string-listp (alist-keys aig-alist)))
        (raise "Bad aig names.")
        acc)
       ((mv err body)
        (aig2c-compile aig-alist input-names :config config))
       ((when err)
        (raise "Error compiling AIGs: ~@0." err)
        acc)

       (in-struct  (stv2c-ins-structname stv))
       (out-struct (stv2c-outs-structname stv))
       (run-fn     (stv2c-run-fnname stv))
       (acc (str::revappend-chars "void " acc))
       (acc (str::revappend-chars run-fn acc))
       (acc (str::revappend-chars " (const " acc))
       (acc (str::revappend-chars in-struct acc))
       (acc (str::revappend-chars "& in, " acc))
       (acc (str::revappend-chars out-struct acc))
       (acc (str::revappend-chars "& out)" acc))
       (acc (cons #\Newline acc))
       (acc (cons #\{ acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars body acc))
       (acc (stv2c-output-stuff out-usersyms renaming-alist acc))
       (acc (str::revappend-chars "}" acc))
       (acc (cons #\Newline acc)))
    acc))

;; So all that is left is to then install these result bits into
;; the proper places in the output structure.

#||
(plev)
(str::rchars-to-string
 (stv2c-make-run-fn (alu16-test-vector) nil))
||#

(define stv2c-write ((filename stringp) (contents stringp) state)
  :guard-debug t
  (b* ((- (cw "Writing ~s0.~%" filename))
       ((mv channel state)
        (open-output-channel filename :character state))
       ((unless channel)
        (raise "Can't open file ~s0 for output.")
        state)
       (state (princ$ contents channel state))
       (state (close-output-channel channel state)))
    state))

(define stv2c-main
  :parents (stv2c)
  ((stv processed-stv-p)
   &key
   (state 'state))
  (b* (((processed-stv stv) stv)
       (c-name          (stv2c-c-symbol-name stv.name))
       (header-filename (str::cat c-name ".h"))
       (impl-filename   (str::cat c-name ".cc"))
       (header-txt      (str::rchars-to-string (stv2c-header stv nil)))
       (impl-txt (b* ((acc nil)
                      (acc (str::revappend-chars "// Warning: automatically generated file!
// Do not hand edit!

#include \"" acc))
                      (acc (str::revappend-chars header-filename acc))
                      (acc (cons #\" acc))
                      (acc (cons #\Newline acc))
                      (acc (cons #\Newline acc))
                      (acc (stv2c-make-run-fn stv acc)))
                   (str::rchars-to-string acc)))
       (state (stv2c-write header-filename header-txt state))
       (state (stv2c-write impl-filename impl-txt state)))
    state))


#||
Example:
(stv2c-main (alu16-test-vector))
||#
