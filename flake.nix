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

    typix = {
      url = "github:johnyob/typix/ajob410@add-support-for-packages";
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
          programs.typstyle.enable = true;

          settings.global.excludes = ["examples/*" "result" ".direnv" "_build"];
        };

        typixLib = typix.lib.${system};
        typstLib = pkgs.callPackage ./nix/typst.nix {};

        report = typixLib.buildTypstProject {
          src = pkgs.lib.sources.cleanSource ./report;
          fontPaths = with pkgs; [libertinus roboto];
          typstSource = "main.typ";
          typstPackages = [
            {
              name = "curryst";
              version = "0.3.0";
              sha256 = "sha256-TyA4XV57N1YDDVncy/sI06FWqAR+3mbqHisKmkRjqZE=";
            }
            {
              name = "ctheorems";
              version = "1.1.3";
              sha256 = "sha256-hzWgHWt88VLofnhaq4DB5JAGaWgt1rCDP4O9nknZzVY=";
            }
          ];
        };
      in {
        packages = {
          inherit mlsus;
          inherit report;
          default = mlsus;
        };

        checks = {
          inherit report;
          mlsus = self.packages.${system}.mlsus.overrideAttrs (old: {
            name = "check-${old.name}";
            doCheck = true;
          });
        };

        formatter = fmt.config.build.wrapper;

        devShells.default = typixLib.devShell {
          name = "mlsus-dev-shell";

          fontPaths = with pkgs; [libertinus roboto];
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

            # Typst
            typst
            tinymist
            typstyle
          ];
        };
      });
}
