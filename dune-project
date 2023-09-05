(lang dune 3.7)
(name "sail-pl")
(version 0.1)
(using menhir 2.0)
(generate_opam_files true)
(map_workspace_root false)

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
    (ocaml (>= 5.1.0))
    (cmdliner (>= 1.1.1))
    (fmt  (>= 0.9.0))
    (menhir (>= 2.0))
    (logs (>= 0.7))
    (mtime (>= 1.3.0))
    (ctypes-foreign (>= 0.18.0))
    (llvm (= 15.0.7+nnp-2))
    zarith
    ))
