(asdf:defsystem zippy-dwim
  :components ((:file "dwim"))
  :depends-on (:zippy)
  :defsystem-depends-on (:deploy)
  :build-operation "deploy-op"
  :build-pathname
  #+win32 "zippy-dwim.exe"
  #+linux "zippy-dwim.run"
  #+darwin "zippy-dwim.o"
  :entry-point "org.shirakumo.zippy.dwim::main")
