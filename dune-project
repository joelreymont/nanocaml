(lang dune 3.18)

(map_workspace_root false)

(wrapped_executables false)

(package
 (name ppx_nanocaml)
 (synopsis "Nanopass framework for OCaml")
 (description
  "An implementation of nanopass for OCaml using a PPX preprocessor.")
 (authors "iitalics <milo@ccs.neu.edu>" "OhadRau <admin@ohad.space>")
 (maintainers "iitalics, OhadRau")
 (license LICENSE)
 (source
  (github nanocaml/nanocaml))
 (depends
  (ocaml
   (>= "5.3.0"))
  dune
  ppxlib
  ounit
  batteries))
