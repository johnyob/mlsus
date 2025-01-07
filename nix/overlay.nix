final: prev:
with prev; {
  ocamlPackages = final.ocaml-ng.ocamlPackages_5_2;

  ocaml-ng =
    ocaml-ng
    // (with ocaml-ng; {
      ocamlPackages_5_2 = ocamlPackages_5_2.overrideScope (
        _: prev:
          with prev; {
            grace = buildDunePackage rec {
              pname = "grace";
              version = "0.2.0";

              minimalOCamlVersion = "4.14";

              src = fetchFromGitHub {
                owner = "johnyob";
                repo = "grace";
                rev = "275adda398834612b804283fe9548708e570bfdf";
                hash = "sha256-2zBYXrNb/rVWjEBmmQfW+rAWs/qhx6nMhAdJEwIdhHQ=";
              };
              propagatedBuildInputs = [core ppx_jane fmt dedent iter core_unix uutf ppx_optcomp];
            };
          }
      );
    });
}
