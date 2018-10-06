; This follows the recommendations in the WORKING-WITH-PACKAGES manual page.

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(ld "centaur/fty/package.lsp" :dir :system)

(reset-prehistory)

(in-package "FTY")
