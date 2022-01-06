(lang dune 2.9)
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
    (dune (>= 2.9))
    (core (>= 0.14.1))
    (fmt  (>= 0.9.0))
    (menhir (>= 2.0))))
