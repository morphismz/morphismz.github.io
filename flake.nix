{
  description = "Personal Site - built in Typst";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    press.url = "github:RossSmyth/press";
  };

  outputs =
    { self, nixpkgs, press }:
    let
      system = "x86_64-linux";

      pkgs = import nixpkgs {
        inherit system;
        overlays = [ (import press) ];
      };

      fs = pkgs.lib.fileset;

      document = {
        # [Optional] The name of the derivation
        # Default: ${pname}-${version}
        pname = "personal-site";
        version = "0.0.0";

        # Source directory to copy to the store.
        # Recommended to filter with filesets.
        src = fs.toSource {
          root = ./.;
          fileset = fs.unions [
            ./main.typ
            ./src
            ./site
          ];
        };

        # [Optional] The entry-point to the document, default is "main.typ"
        # This is relative to the directory input above.
        # Default: "main.typ"
        file = "main.typ";

        # [Optional] Key-value attribute set passed as --input arguments to typst
        # (available as the `sys.inputs` dictionary)
        inputs = {
          # "language" = "fr";
        };

        # [Optional] Typst universe package selection
        #
        # Pass in a function that accept an attrset of Typst pacakges,
        # and returns a list of packages.
        #
        # The input parameter is from the pkgs.typstPackages attributes
        # in nixpkgs. See this section of the nixpkgs reference for patching
        # and overriding
        # https://nixos.org/manual/nixpkgs/unstable/#typst
        #
        # Default: (_: [])
        typstEnv = (p: [ p.fontawesome_0_6_2 ]);

        # [Optional] Any non-universe packages. The attribute key is the namespace.
        # The package must have a typst.toml file in its root.
        #
        # Default: {}
        extraPackages = {
          # # Does import-from-derivation to determine the name and version
          # local = [ inputs.unify ];
          # # Does not to IFD, so realization will be faster.
          # namespace = [
          #   {
          #     pname = "unify";
          #     version = "0.7.1";
          #     src = inputs.unify;
          #   }
          # ];
        };

        # [Optional] A timestamp representing the current date when using `datetime.today()`.
        #
        # Accept a Unix timestamp. When not set, is the value of `SOURCE_DATE_EPOCH`, which in
        # Nixpkgs builds is `315532800` by default.
        #
        # In a flake can be set to `self.lastModified` to get the git timestamp
        creationTimestamp = self.lastModified;

        # [Optional] The format to output
        # Default: "pdf"
        # Can be either "pdf", "html", "svg", or "png"
        format = "bundle";

        # [Optional] The fonts to include in the build environment
        # Note that they must follow the standard of nixpkgs placing fonts
        # in $out/share/fonts/. Look at Inconsolta or Fira Code for reference.
        # Default: []
        fonts = [
          pkgs.font-awesome
          pkgs.tex-gyre-math.termes
          pkgs.inter
          pkgs.cm_unicode
        ];

        # [Optional] Whether to have a verbose Typst compilation session
        # Default: false
        verbose = false;

        # [Optional, String]
        # Pages to export. See Typst documentation for the format. Automatically
        # inserts commas.
        #
        # Examples:
        #
        # Only export pages 2 and 5
        # pages = [ "2" "5" ];
        #
        # Export pages 2, 3 through 6 (inclusive), and then page 8 and any pages after
        # pages = [ "2" "3-6" "8-" ]
        pages = [ ];

        # [Optional, bool]
        # By default true. If `false`, then no tags will be
        # emitted in the PDF document
        pdfTags = true;

        # [Optional, string/int]
        # By default 144 ppi
        # > The PPI (pixels per inch) to use for PNG export
        #
        # Not useful if PNG is not used
        pngPpi = 144;

        # [Optional, List String]
        # The PDF standard to follow.
        #
        # See Typst documentation for valid inputs.
        #
        # Not useful if PDF is not used
        pdfStandards = [ ];
      };

      typst-watch = pkgs.writeShellScriptBin "typst-watch" ''
        typst watch --format bundle --port 3000 main.typ temp
      '';

      deploy = pkgs.writeShellScriptBin "deploy" ''
        cd "$TYPST_ROOT"
        rm -r docs
        nix build
        cp -rL result docs
        chmod -R +w docs
      '';
    in
    {
      packages.${system}.default = pkgs.buildTypstDocument document;

      # Provides a development environment with the typst command available
      devShells.${system}.default = pkgs.mkShell {
        inputsFrom = [ self.packages.${system}.default ];
        packages = [
          pkgs.tinymist
          pkgs.typstyle
          typst-watch
          deploy
        ];

        TYPST_FEATURES = "bundle,html";

        shellHook = ''
          export TYPST_ROOT=$(git rev-parse --show-toplevel 2>/dev/null)
        '';
      };
    };
}
