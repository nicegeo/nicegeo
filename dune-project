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
  ocaml
  (ocamlformat :with-test)
  (alcotest :with-test)
  (odoc :with-doc))
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
