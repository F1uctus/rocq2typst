(lang dune 3.21)
(name rocq2typst)
(version 0.2.0)
(using rocq 0.11)

(generate_opam_files true)

(license GPL-3.0-or-later)
(authors "Ilya I. Nikitin <ilya.i.nikitin@proton.me>")
(maintainers "Ilya I. Nikitin <ilya.i.nikitin@proton.me>")
(source (github F1uctus/rocq2typst))

(package
 (name rocq2typst)
 (synopsis "Rendering of Rocq statements as Typst mathematical markup")
 (depends
  (rocq-core (and (>= 9.3) (< 9.4~)))
  (rocq-elpi (>= 3.5.1))))

(package
 (name rocq2typst-mathcomp)
 (synopsis "Mathematical Components notation dictionary for rocq2typst")
 (depends
  (rocq2typst (= :version))
  (rocq-mathcomp-finite-group (>= 2.6.0))
  (rocq-mathcomp-algebra (>= 2.6.0))))

(package
 (name rocq2typst-analysis)
 (synopsis "Mathcomp-analysis notation dictionary for rocq2typst")
 (depends
  (rocq2typst-mathcomp (= :version))
  (rocq-micromega-plugin (>= 1.1.1))
  (rocq-mathcomp-analysis (>= 1.19.0))))

(package
 (name rocq2typst-coqeal)
 (synopsis "CoqEAL notation dictionary for rocq2typst")
 (depends
  (rocq2typst-mathcomp (= :version))
  (coq-coqeal (>= 2.1.2))))

(package
 (name rocq2typst-infotheo)
 (synopsis "Infotheo notation dictionary for rocq2typst")
 (depends
  (rocq2typst (= :version))
  (rocq-micromega-plugin (>= 1.1.1))
  (rocq-infotheo (>= 0.9.9))))
