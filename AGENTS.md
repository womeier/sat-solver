# AGENTS.md

## Lean proof work (proofs/lean/)

Before writing or editing anything under `proofs/lean/SatSolver/Verification/`, read
`proofs/lean/.lake/packages/aeneas/documentation/skills/aeneas-lean-core.instructions.md`
(and the sibling skill files in that directory — `aeneas-tactics-quickref`,
`proof-patterns`, `lean-lsp-mcp`, `verification-campaigns`). This is `aeneas`'s own
agent-facing documentation for proving properties about its generated Lean code
(the `@[step]`/`spec`/`⦃ ⦄` pattern, banned tactics, loop-proof idioms, etc.) and is
required context — see `proofs/lean/.lake/packages/aeneas/CLAUDE.md` for the full
skill file index.

Our extraction uses `-loops-to-rec` (recursive loop translation), passed via
`--aeneas-args` in the `just extract` recipe, per the skill file's recommendation
over `aeneas`'s default fixed-point-combinator mode (whose proof infrastructure is
described as less mature). Loop-heavy proofs should follow the recursive-function
pattern (`unfold`/`by_cases`/`step`/`termination_by`). Check `PLAN.md` for the
current status.

The `lean-lsp-mcp` skill file (above) mandates using the lean-lsp-mcp MCP tools for
proof work instead of `lake build` loops. It's wired up via `.mcp.json` at the repo
root, backed by `.uv-tools/bin/lean-lsp-mcp` (gitignored). Since nixpkgs has no
`lean-lsp-mcp` package, the flake's `shellHook` installs it as a `uv tool` on shell
entry (same self-managing-toolchain pattern as rustup/elan) — just entering the nix
devShell (`nix develop`) is enough to (re-)provision it if `.uv-tools/` is missing.

`$HOME` is non-executable in some sandboxes this project runs in, which breaks
`rustup`/`cargo`/`elan` (they default to installing under `$HOME`). `flake.nix`'s
`shellHook` redirects all three toolchain homes to project-local, gitignored
directories instead (`.rustup-home`, `.cargo-home`, `.elan-home`) — this also makes
them persistent across sandbox/session restarts, unlike `/tmp`. `.mcp.json` sets
`ELAN_HOME` to the same path so the lean-lsp-mcp server subprocess (launched outside
the nix devShell by the MCP client) can find the Lean toolchain too — without it,
`lake`/`lean` fail with a permission error and the LSP server refuses to start
("Language server closed the connection"). If `.elan-home`/`.rustup-home`/
`.cargo-home` are missing (fresh clone, or a wiped sandbox), `nix develop` recreates
them; for the MCP server specifically (which doesn't go through the devShell), you
may need to run `rustup default stable` and `lake build` once under these env vars
manually — see the `shellHook` in `flake.nix` for the exact exports.

See `PLAN.md` for the overall proof plan and progress log.
