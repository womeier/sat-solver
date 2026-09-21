{
  description = "sat-solver dev environment: Rust + hax (Lean backend)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    hax.url = "github:cryspen/hax";
  };

  outputs = { self, nixpkgs, flake-utils, hax }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            # Rust: left to rustup, not nixpkgs' rustc — cargo-hax/charon
            # manage their own pinned nightly toolchain via rustup itself.
            rustup
            gcc
            pkg-config
            openssl

            # Lean: elan manages the toolchain pinned by lean-toolchain /
            # lakefile.toml once `cargo hax into lean` generates them.
            elan

            # hax CLI (the `cargo hax` subcommand), built by hax's own flake.
            hax.packages.${system}.default

            # lean-lsp-mcp (MCP server for interactive Lean proof development,
            # see proofs/lean/.lake/packages/aeneas/documentation/skills/lean-lsp-mcp.instructions.md)
            # isn't in nixpkgs, so `uv` installs it as a tool — same
            # self-managing-toolchain pattern as rustup/elan above.
            uv

            gnumake
            git
            just
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            pkgs.libiconv
            pkgs.darwin.apple_sdk.frameworks.Security
          ];

          shellHook = ''
            # $HOME may not be executable in some sandboxes (rustup/elan/cargo
            # all default to installing under $HOME), so every toolchain home
            # is redirected project-local instead — this also makes them
            # persistent across sandbox/session restarts, unlike /tmp.
            export RUSTUP_HOME="$PWD/.rustup-home"
            export CARGO_HOME="$PWD/.cargo-home"
            export ELAN_HOME="$PWD/.elan-home"
            export PATH="$CARGO_HOME/bin:$ELAN_HOME/bin:$PATH"

            if ! rustup show active-toolchain >/dev/null 2>&1; then
              rustup default stable >/dev/null 2>&1 || true
            fi

            export UV_TOOL_DIR="$PWD/.uv-tools"
            export UV_TOOL_BIN_DIR="$PWD/.uv-tools/bin"
            export UV_CACHE_DIR="$PWD/.uv-cache"
            export PATH="$UV_TOOL_BIN_DIR:$PATH"
            if [ ! -x "$UV_TOOL_BIN_DIR/lean-lsp-mcp" ]; then
              uv tool install --quiet lean-lsp-mcp >/dev/null 2>&1 || true
            fi

            echo ""
            echo "sat-solver dev shell ready."
            echo "  extract:  cargo hax into lean"
            echo "  verify:   cd proofs/lean && lake exe cache get && lake build"
          '';
        };
      });
}
