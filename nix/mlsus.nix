{
  lib,
  ocamlPackages,
}:
with ocamlPackages;
  buildDunePackage rec {
    pname = "mlsus";
    version = "dev";

    src = lib.cleanSource ../.;

    nativeBuildInputs = [
      menhir
    ];

    propagatedBuildInputs = [
      core
      core_unix
      async
      ppx_jane
      grace
      fmt
      menhir
    ];
  }
