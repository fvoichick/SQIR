{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    pkgs.ocaml
    pkgs.coq_8_12
    pkgs.opam
    pkgs.coq.ocamlPackages.zarith
    pkgs.coq.ocamlPackages.dune_2
    pkgs.coq.ocamlPackages.menhir
    pkgs.coq.ocamlPackages.batteries
  ];
}
