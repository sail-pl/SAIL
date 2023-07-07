(lang dune 3.2)
(name "sail-pl")
(version 0.1)
(using menhir 2.0)
(generate_opam_files true)

(license GPL) 
(authors "Frederic Dabrowski")
(maintainers "sail-pl-maintainers@listes.univ-orleans.fr")
(homepage "https://sail-pl.github.io")
(bug_reports "https://sail-pl.github.io")

(package
  (name "sail-pl")
  (synopsis "SAIL: Safe Interactive Language")
  (description "SAIL means Safe Interactive Language.")
  (depends 
    (ocaml (>= 4.13.1))
    (cmdliner (>= 1.1.1))
    (fmt  (>= 0.9.0))
    (menhir (>= 2.0))
    (logs (>= 0.7))
    (mtime (>= 1.3.0))
    (ctypes-foreign (>= 0.18.0))
    (llvm (>= 13.0.0))
    zarith
    ppx_lun
    logs-ppx
    ))
