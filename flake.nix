{
  description = "MLsus Nix Flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    treefmt = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # OCaml overlay
    ocaml-overlay = {
      url = "github:nix-ocaml/nix-overlays";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs:
    with inputs;
      flake-utils.lib.eachDefaultSystem (system: let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            ocaml-overlay.overlays.default
            (import ./nix/overlay.nix)
          ];
        };

        mlsus = pkgs.callPackage ./nix/mlsus.nix {};

        fmt = treefmt.lib.evalModule pkgs {
          projectRootFile = "flake.nix";

          programs.alejandra.enable = true;
          programs.ocamlformat = {
            enable = true;
            package = pkgs.ocamlformat_0_26_2;
          };

          settings.global.excludes = ["examples/*" "result" ".direnv" "_build"];
        };
      in {
        packages = {
          inherit mlsus;
          default = mlsus;
        };

        checks = {
          mlsus = self.packages.${system}.mlsus.overrideAttrs (old: {
            name = "check-${old.name}";
            doCheck = true;
          });
        };

        formatter = fmt.config.build.wrapper;

        devShells.default = pkgs.mkShell {
          name = "mlsus-dev-shell";

          inputsFrom = [mlsus];

          buildInputs = with pkgs; [
            # Formatters
            alejandra
            ocamlformat_0_26_2

            # OCaml devenv
            ocamlPackages.utop
            ocamlPackages.ocaml-lsp
            ocamlPackages.merlin
            ocamlPackages.merlin-lib
            ocamlPackages.ocaml
            ocamlPackages.dune
          ];
        };
      });
}
