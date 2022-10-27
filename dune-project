(lang dune 2.8)

(name braid)

; (cram enable)

(using menhir 2.0)

(generate_opam_files true)

(source
 (github fferreira/nu2scr))

(license GPL-3.0-or-later)

(authors "Francisco Ferreira")

(maintainers "Francisco Ferreira")

; (homepage "https://...")

; (documentation "https://...")

(package
 (name braidMPST)
 (synopsis
   "A tool to manipulate and validate MPST protocols with flexible interleavings.")
 (description
   "A tool to manipulate and validate MPST protocols supporting mixed choice.")
 (depends
  (ocaml
   (>= 4.08))
  (menhir
   (>= 20190924))
  ; (ppx_deriving
  ;  (>= 5.2))
  dune
  ; (base
  ;  (>= v0.12.0))
  ; (stdio
  ;  (>= v0.12.0))
  ; (ppx_sexp_conv
  ;  (>= v0.12.0))
  ; (ppx_here
  ;  (>= v0.12.0))
  ; (z3 :with-test)
  ; (odoc :with-doc)
  (ocamlgraph
   (>= 1.8.8))
  ; (ppxlib
  ;  (>= 0.22.0))
  ; (cmdliner
  ;  (>= 1.1.0))
  ; (process
  ;  (>= 0.2.1))
 ))

(package
 (name braidIDE)
 (synopsis
   "A web tool to manipulate and validate Synthetic MPST protocols.")
 (description
   "A web tool to manipulate and validate Synthetic MPST protocols supporting mixed choice.")
 (depends
  ; (nuscr
  ;  (= :version))
  dune
  (js_of_ocaml
   (>= 3.5.0))
  (js_of_ocaml-ppx
   (>= 3.5.0))
  (js_of_ocaml-tyxml
   (>= 3.5.0))))
