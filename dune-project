(lang dune 3.17)

(name nicegeo)

(using menhir 3.0)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license MIT)

(documentation https://url/to/documentation)

(package
 (name nicegeo)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  (ocaml (= "5.4.1"))
  (sedlex (= "3.7"))
  (z3 (= "4.15.2"))
  (yojson (= "3.0.0"))
  (ocamlformat (and (= "0.28.1") :with-test))
  (alcotest (and (= "1.9.1") :with-test))
  (ppx_expect (and (= "v0.17.3") :with-test))
  (odoc :with-doc))
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
