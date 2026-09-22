claude *args:
    nix develop --command claude-sandbox {{args}}

# Extract sat_naive/sat_naive_functional (and their dependencies) to proofs/lean.
# main.rs is moved aside for the duration: charon treats whichever cargo target it
# compiles as "primary" and gives it full bodies, everything else becomes an opaque
# dependency reference — so a bin target alongside the lib silently starves the lib's
# own items of their bodies. Removing it makes the lib the (only, primary) target.
extract:
    #!/usr/bin/env bash
    set -u
    root=$(pwd)
    backup=$(mktemp /tmp/sat-solver-main.rs.XXXXXX)
    mv "$root/src/main.rs" "$backup"
    trap 'mv "$backup" "$root/src/main.rs"' EXIT
    cargo hax into lean --charon-args="\
        --exclude crate::expr::parse_bool \
        --exclude crate::expr::parse_var \
        --exclude crate::expr::parse_neg \
        --exclude crate::expr::parse_conj \
        --exclude crate::expr::parse_disj \
        --exclude crate::expr::parse_expr \
        --exclude crate::expr::example_expr_sat \
        --exclude crate::expr::example_expr_unsat \
        --exclude crate::sat \
        --exclude crate::sat_naive::SAT_SOLVER_NAIVE \
        --exclude crate::sat_naive_functional::SAT_SOLVER_NAIVE_FUNCTIONAL \
        --exclude crate::sat_dpll \
        --exclude crate::sat_cdcl \
        --opaque 'crate::expr::{impl core::fmt::Debug for crate::expr::Entry}' \
        --opaque 'crate::expr::{impl core::fmt::Debug for crate::expr::Map}' \
        --opaque 'crate::expr::{impl core::fmt::Debug for crate::expr::Expr}' \
        --opaque 'crate::expr::{impl core::fmt::Display for crate::expr::Expr}'" \
        --aeneas-args="-loops-to-rec"
    # The --opaque flags above stop charon from attempting to translate the
    # derived Debug impls / the handwritten Display impl for Entry/Map/Expr:
    # doing so hits an internal "Unreachable" aeneas error (their bodies use
    # unsupported alloc::fmt machinery anyway, same reason evaluate's error
    # type is `()` instead of `String` -- see justfile history). Opaque items
    # still get properly seeded into Assumptions/ as axiom stubs below; this
    # just avoids the crash on the way there.

    # Work around a hax quirk: Extraction/{Types,Funs}.lean unconditionally
    # `import SatSolver.Extraction.{Types,Funs}External`, but hax sometimes skips
    # writing that file (and the Assumptions/ file it should seed) even when the
    # _Template.lean shows real content (e.g. Debug/Display axioms) is needed.
    # Seed Assumptions/ from the template on first run (hax never touches
    # Assumptions/ itself afterward) and make sure the Extraction/ forwarder
    # exists, since hax regenerates/clears Extraction/ on every run.
    cd "$root/proofs/lean"
    mkdir -p SatSolver/Assumptions
    for f in TypesExternal FunsExternal; do
        if [ ! -f "SatSolver/Assumptions/$f.lean" ] && [ -f "SatSolver/Extraction/${f}_Template.lean" ]; then
            cp "SatSolver/Extraction/${f}_Template.lean" "SatSolver/Assumptions/$f.lean"
            # Another hax quirk: the template's Debug/Display `fmt` axioms declare an
            # extra spurious `× (core.fmt.Formatter → core.fmt.Formatter)` tuple
            # component that doesn't match what call sites actually expect. Strip it.
            # (-z: null-data mode, so the multi-line pattern can match across the
            # template's line-wrapped tuple type.)
            sed -z -E \
                's/× core\.fmt\.Formatter × \(core\.fmt\.Formatter →[^)]*core\.fmt\.Formatter\)\)/× core.fmt.Formatter)/g' \
                -i "SatSolver/Assumptions/$f.lean"
        fi
        if [ ! -f "SatSolver/Extraction/$f.lean" ] && [ -f "SatSolver/Assumptions/$f.lean" ]; then
            echo "import SatSolver.Assumptions.$f" > "SatSolver/Extraction/$f.lean"
        fi
    done

    # Same story for the root integration files: hax sometimes skips writing
    # these even though the "SatSolver" lean_lib's default target needs them.
    if [ ! -f SatSolver/Extraction.lean ]; then
        printf '%s\n' \
            '-- Imports the extraction modules. Rewritten by hax on every extraction.' \
            'import SatSolver.Extraction.Types' \
            'import SatSolver.Extraction.Funs' \
            > SatSolver/Extraction.lean
    fi
    if [ ! -f SatSolver.lean ]; then
        printf '%s\n' \
            'import SatSolver.Extraction' \
            'import SatSolver.Verification.ProofObligations' \
            > SatSolver.lean
    fi
