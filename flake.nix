{
  description = "abstract-set-theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    flake-utils.url = "github:numtide/flake-utils";

    agda-nix = {
      url = "github:input-output-hk/agda.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    agda-stdlib = {
      url = "github:agda/agda-stdlib/v2.4";
      flake = false;
    };

    agda-stdlib-classes = {
      url = "github:agda/agda-stdlib-classes/v2.4";
      flake = false;
    };

    agda-stdlib-meta = {
      url = "github:agda/agda-stdlib-meta/v2.4";
      flake = false;
    };
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-utils,
      agda-nix,
      ...
    }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];
      overlay = nixpkgs.lib.composeManyExtensions [
        inputs.agda-nix.overlays.default
        (final: prev: {
          agdaPackages = prev.agdaPackages.overrideScope (
            afinal: aprev: {
              standard-library = aprev.standard-library.overrideAttrs (_: {
                src = inputs.agda-stdlib;
              });
              standard-library-classes = aprev.standard-library-classes.overrideAttrs (_: {
                src = inputs.agda-stdlib-classes;
              });
              standard-library-meta = aprev.standard-library-meta.overrideAttrs (_: {
                src = inputs.agda-stdlib-meta;
              });
              abstract-set-theory = aprev.abstract-set-theory.overrideAttrs (_: {
                src = ./.;
              });
            }
          );
        })
      ];
    in
    flake-utils.lib.eachSystem systems (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            overlay
          ];
        };
      in
      {
        packages.default = pkgs.agdaPackages.abstract-set-theory;
        devShells.default = pkgs.agda.shellFor pkgs.agdaPackages.abstract-set-theory;
        hydraJobs =
          let
            jobs = { inherit (self) packages devShells; };
          in
          jobs
          // {
            required = pkgs.releaseTools.aggregate {
              name = "${system}-required";
              constituents = with nixpkgs.lib; collect isDerivation jobs;
            };
          };
      }
    )
    // {
      overlays.default = overlay;
    };
}
