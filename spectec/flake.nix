{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
#  inputs.lean.url = "github:leanprover/lean4";

  description = "Nix infrastructure for spectec";
  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.${system}.default =
        pkgs.mkShell {
          packages = with pkgs; [
            #lean.packages.${system}.lean-all
            dune_3
            ocamlPackages.ocaml
            ocamlPackages.menhir
            ocamlPackages.mdx
            ocamlPackages.merlin
            ghc
          ];
        };
    };
}
