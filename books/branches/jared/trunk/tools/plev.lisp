(in-package "ACL2")
(set-state-ok t)

(defdoc plev
  ":Doc-Section Print-control
Easy-to-use functions for controlling the printer.~/

Example:
~bv[]
  (include-book \"tools/plev\" :dir :system)

  (plev)     ;; moderate abbreviations, a good default
  (plev-max) ;; don't abbreviate anything, show everything
  (plev-min) ;; heavily abbreviate things, usually too terse
  (plev-mid) ;; somewhat similar to plev
~ev[]

Each of these is actually a macro with keyword arguments
like :length, :level, :lines, :circle, :pretty, and :readably.  You can choose
your own values for these arguments, or just use the above macros.

~st[Clozure Common Lisp Users]:  you may wish to instead include
~bv[]
 (include-book \"tools/plev-ccl\" :dir :system :ttags :all)
~ev[]
for a version of plev that also updates the print levels used during
backtraces and error messages.  CCL users can also use:
~bv[]
  (plev-info)
~ev[]
to see the current values of certain print-related variables.~/~/")

(link-doc-to plev-max print-control plev)
(link-doc-to plev-min print-control plev)
(link-doc-to plev-mid print-control plev)
(link-doc-to plev-info print-control plev)


(defn plev-fn (length level lines circle pretty readably state)
  (declare (xargs :mode :program))
  (let* ((old-tuple (abbrev-evisc-tuple state))
         (new-tuple (list (car old-tuple) level length
                          (cadddr old-tuple))))
    (mv-let (flg val state)
      (set-evisc-tuple new-tuple
                       :iprint t
                       :sites :all)
      (declare (ignore val))
      (mv flg
          (list :length length
                :level level
                :lines lines
                :circle circle
                :readably readably
                :pretty pretty)
          state))))

(defmacro plev (&key (length '16)
                     (level '3)
                     (lines 'nil)
                     (circle 't)
                     (pretty 't)
                     (readably 'nil))
  `(plev-fn ,length ,level ,lines ,circle ,pretty ,readably state))

(defmacro plev-max (&key (length 'nil)
                         (level 'nil)
                         (lines 'nil)
                         (circle 'nil)
                         (pretty 't)
                         (readably 'nil))
  `(plev-fn ,length ,level ,lines ,circle ,pretty ,readably state))

(defmacro plev-mid (&key (length '10)
                         (level '5)
                         (lines '200)
                         (circle 't)
                         (pretty 't)
                         (readably 'nil))
  `(plev-fn ,length ,level ,lines ,circle ,pretty ,readably state))


(defmacro plev-min (&key (length '3)
                         (level '3)
                         (lines '60)
                         (circle 't)
                         (pretty 'nil)
                         (readably 'nil))
  `(plev-fn ,length ,level ,lines ,circle ,pretty ,readably state))


