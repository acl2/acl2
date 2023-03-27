
; constants.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/util/defval" :dir :system)

;; <h3>Mathematical Constants</h3>
;; <h3>Fundamental Physical Constants</h3>
;; <h3>Rapid Single Flux Quantum Constants</h3>

(defsection vwsim-constants
  :parents (vwsim-hdl)
  :short "The constants used by the VWSIM simulator."
  :long
  ; xdoc doesn't support defconst
  "<p>The VWSIM simulator defines several constants to perform
  simulations of electrical circuits.</p>
  <h3>Unit Prefixes</h3>
@({
  (defconst *kilo*   1000)
  (defconst *mega*   1000000)
  (defconst *giga*   1000000000)
  (defconst *tera*   1000000000000)
  (defconst *peta*   1000000000000000)

  (defconst *milli*  1/1000)
  (defconst *micro*  1/1000000)
  (defconst *nano*   1/1000000000)
  (defconst *pico*   1/1000000000000)
  (defconst *femto*  1/1000000000000000)
})
"

;! 1000x multipliers

  (defconst *kilo*   1000)
  (defconst *mega*   1000000)
  (defconst *giga*   1000000000)
  (defconst *tera*   1000000000000)
  (defconst *peta*   1000000000000000)

  (defconst *milli*  1/1000)
  (defconst *micro*  1/1000000)
  (defconst *nano*   1/1000000000)
  (defconst *pico*   1/1000000000000)
  (defconst *femto*  1/1000000000000000)
)

(defconst *multiplier-constants*
  `((*kilo*  ,*kilo*)
    (*mega*  ,*mega*)
    (*giga*  ,*giga*)
    (*tera*  ,*tera*)
    (*peta*  ,*peta*)
    (*milli* ,*milli*)
    (*micro* ,*micro*)
    (*nano*  ,*nano*)
    (*pico*  ,*pico*)
    (*femto* ,*femto*)))

; We define and use our own version of these constants.
; NOTE: some of the constants are not so precise!

#||
; Pulled from JoSIM source.

namespace JoSIM {
  namespace Constants {
    static constexpr double PI = 3.141592653589793238463;
    static constexpr double PHI_ZERO = 2.067833831170082E-15;
    static constexpr double BOLTZMANN = 1.38064852E-23;
    static constexpr double EV = 1.6021766208e-19;
    static constexpr double HBAR = 1.0545718001391127e-34;
    static constexpr double C = 299792458;
    static constexpr double MU0 = 12.566370614E-7;
    static constexpr double EPS0 = 8.854187817E-12;
    static constexpr double SIGMA = 3.291059757e-16;
  }
}
||#

; Some of the constants above were different than we found in various
; references, such as Wikipedia.  To permit operation of our simulator
; so that it calculates JoSIM-compatible results, we use the next
; flag.

(defconst *use-josim-constants* nil)

(defsection vw-math-constants
  :extension vwsim-constants
  "<h3>Mathematical Constants</h3>"

  (defun f*pi* ()
    "Half the distance around a unit circle"
    (declare (xargs :guard t))
    (if *use-josim-constants*
        (/ 3141592653589793238463
           1000000000000000000000)
      (/ 3141592653589793
         1000000000000000)))

  (defun f*e* ()
    "Euler's number"
    (declare (xargs :guard t))
    (/ 2718281828459045
       1000000000000000))
  )

(defsection vw-physical-constants
  :extension vwsim-constants
  "<h3>Fundamental Physical Constants</h3>"
  (defun f*h* ()
    "Planck's Constant (Joules * seconds)"
    (declare (xargs :guard t))
    (/ 662607015 (expt 10 42)))

  (defun f*h_bar* ()
    "Planck's Constant divided by two pi"
    (declare (xargs :guard t))
    (if *use-josim-constants*
        (* 10545718001391127 (expt 10 -50))
      (/ (f*h*) (* 2 (f*pi*)))))

  (defun f*e_C* ()
    "Charge of an electron in Coulumbs"
    (declare (xargs :guard t))
    (if *use-josim-constants*
        (* 16021766208 (expt 10 -29))
      (* 16021766341 (expt 10 -29))))

  (defun f*K_b* ()
    "Boltzmann's constant (Joules/Kelvin)"
    (declare (xargs :guard t))
    (/ 1380649 (expt 10 29)))
  )

(defsection vw-RSFQ-constants
  :extension vwsim-constants
  "<h3>Rapid Single Flux Quantum Constants</h3>"

  (defun f*deltaV* ()
    "deltaV determines the size of the JJ transition region"
    (declare (xargs :guard t))
    (/ 1 10000))

  (defun f*phi0* ()
    "phi0 is the magnetic flux quantum"
    (declare (xargs :guard t))
    (if *use-josim-constants*
        (* 2067833831170082 (expt 10 -30))
      (/ (f*h*) (* 2 (f*e_C*)))))

  (defun f*Icfact* ()
    "ratio of JJ critical current to quasiparticle step height"
    (declare (xargs :guard t))
    (/ (f*pi*) 4))

  )

(defconst *f-constants*
  ;; This will have to appear in the ``raw'' file.
  `((*pi*     ,(f*pi*))
    (*e*      ,(f*e*))
    (*h*      ,(f*h*))
    (*h_bar*  ,(f*h_bar*))
    (*e_C*    ,(f*e_C*))
    (*K_b*    ,(f*K_b*))
    (*deltaV* ,(f*deltaV*))
    (*phi0*   ,(f*phi0*))
    (*Icfact* ,(f*Icfact*))))


; For convenience...

(defmacro ! (x y)
  (declare (xargs :guard (symbolp x)))
  `(assign ,x ,y))

(defmacro !! (variable new-value)
  ;; Assign without printing the result.
  (declare (xargs :guard t))
  `(mv-let
    (erp result state)
    (assign ,variable ,new-value)
    (declare (ignore result))
    (value (if erp 'Error! ',variable))))

(defmacro !s (variable new-value)
  ;; Assign without printing the result.
  (declare (xargs :guard t))
  `(mv-let
    (erp result state)
    (assign ,variable ,new-value)
    (declare (ignore result))
    (value (if erp 'Error! ',variable))))

(defun file-extension-is-lisp (file-path)
  (declare (xargs :guard (stringp file-path)))
  (let* ((file-path-list (coerce file-path 'list))
	 (length (length file-path-list)))
    (if (< length 5)
	nil
      (let ((last-5-chars (nthcdr (- length 5) file-path-list)))
	(equal last-5-chars
	       '(#\. #\l #\i #\s #\p))))))
