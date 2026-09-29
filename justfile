claude *args:
    nix develop --command claude-sandbox {{args}}

# Download the SATLIB uniform-random-3-SAT benchmark sets into benchmarks/
# (gitignored). Three sets of 1000 instances each, at the clause/variable ratio
# 4.26 where random 3-SAT is hardest: uf20-91 and uf50-218 are satisfiable,
# uuf50-218 unsatisfiable. 50 variables is what DPLL solves in milliseconds; the
# `Expr::Variable(u16)` ceiling is 65535 and not the binding constraint.
satlib:
    #!/usr/bin/env bash
    set -eu
    base=https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT
    mkdir -p benchmarks/satlib
    cd benchmarks/satlib
    for set in uf20-91 uf50-218 uuf50-218; do
        if [ -d "$set" ]; then
            echo "$set: already present"
            continue
        fi
        echo "$set: downloading"
        curl -sS -o "$set.tar.gz" "$base/$set.tar.gz"
        mkdir -p "$set"
        tar xzf "$set.tar.gz" -C "$set"
        rm "$set.tar.gz"
    done
    echo "instances: $(find . -name '*.cnf' | wc -l)"

# Run the solvers over the SATLIB sets. Release mode: a debug build is ~20x
# slower, which matters for the naive solver (~0.2 s per 20-variable instance
# optimized, so ~4 s unoptimized).
satlib-test *args:
    cargo test --release --test satlib -- --ignored --nocapture --test-threads=1 {{args}}

# Extract sat_naive/sat_dpll/sat_cdcl (and their dependencies) to proofs/lean.
# Every function in those modules is translated: aeneas rejects a `return` out of an
# *inner* loop, which is why `sat_cdcl::Solver::propagate` is one flat loop with a
# wrapping cursor rather than nested passes, and why `status` indexes its clause
# instead of iterating it. Charon's `--exclude` does not match inherent-impl methods,
# so a function aeneas cannot translate cannot simply be skipped -- it would land in
# `Funs.lean` as a `sorry`.
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
        --exclude crate::dimacs \
        --exclude crate::sat \
        --exclude crate::sat_naive::SAT_SOLVER_NAIVE \
        --exclude crate::sat_dpll::SAT_SOLVER_DPLL \
        --exclude crate::sat_dpll::SAT_SOLVER_DPLL_NAIVE \
        --exclude crate::sat_dpll::SAT_SOLVER_DPLL_TSEITIN \
        --exclude crate::sat_dpll::SAT_SOLVER_DPLL_HYBRID \
        --exclude crate::sat_cdcl::SAT_SOLVER_CDCL \
        --opaque 'crate::expr::{impl core::fmt::Debug for crate::expr::Map}' \
        --opaque 'crate::expr::{impl core::fmt::Debug for crate::expr::Expr}' \
        --opaque 'crate::expr::{impl core::fmt::Display for crate::expr::Expr}' \
        --opaque 'crate::cnf::{impl core::fmt::Debug for crate::cnf::Literal}' \
        --opaque 'crate::cnf::{impl core::fmt::Debug for crate::cnf::Clause}' \
        --opaque 'crate::cnf::{impl core::fmt::Debug for crate::cnf::Cnf}' \
        --opaque 'crate::sat_dpll::{impl core::fmt::Debug for crate::sat_dpll::Transform}'" \
        --aeneas-args="-loops-to-rec"
    # The --opaque flags above stop charon from attempting to translate the
    # derived Debug impls / the handwritten Display impl for Entry/Map/Expr
    # (and, same story, the derived Debug impls for cnf.rs's Literal/Clause/
    # Cnf and for sat_dpll.rs's Transform): doing so hits an internal
    # "Unreachable" aeneas error (their
    # bodies use unsupported alloc::fmt machinery anyway, same reason
    # evaluate's error type is `()` instead of `String` -- see justfile
    # history). Opaque items still get properly seeded into Assumptions/ as
    # axiom stubs below; this just avoids the crash on the way there.

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

    # On every *later* run the seeding above is a no-op, so an extraction that
    # newly needs an axiom -- a fresh --opaque item, e.g. the derived Debug impl
    # on a type that did not exist before -- leaves Assumptions/ one entry short.
    # Lean then fails on the *instance* with "failed to set reducibility status,
    # CoreFmtDebug is not a definition", which says nothing about the real cause.
    # Compare the axiom names and say it plainly instead.
    for f in TypesExternal FunsExternal; do
        tmpl="SatSolver/Extraction/${f}_Template.lean"
        have="SatSolver/Assumptions/$f.lean"
        if [ ! -f "$tmpl" ] || [ ! -f "$have" ]; then continue; fi
        missing=$(comm -23 \
            <(grep -oE '^axiom [A-Za-z0-9_.]+' "$tmpl" | awk '{print $2}' | sort) \
            <(grep -oE '^axiom [A-Za-z0-9_.]+' "$have" | awk '{print $2}' | sort))
        if [ -n "$missing" ]; then
            echo "WARNING: $have is missing axioms this extraction needs:"
            echo "$missing" | sed 's/^/  /'
            echo "  Copy them across from $tmpl, dropping the spurious trailing"
            echo "  '× (core.fmt.Formatter → core.fmt.Formatter)' tuple component."
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

# Walk the SATLIB scaling ladder with one solver, one process per set. Each
# instance gets a `cap`-second budget of its own (a worker process, killed when it
# runs out), so a single pathological instance costs its cap rather than the set,
# and a set reports "solved k of n". The ladder stops for a solver once a set
# solves none of its instances, since every set above it is strictly harder.
# The larger sets are not downloaded by `just satlib` -- see `just satlib-fetch`.
satlib-ladder solver="cdcl" limit="25" cap="10":
    #!/usr/bin/env bash
    set -u
    for set in uf20-91 uf50-218 uf75-325 uf100-430 uf125-538 uf150-645 \
               uf175-753 uf200-860 uf225-960 uf250-1065; do
        # The unsatisfiable twin of `ufN-M` is `uufN-M`: one more leading `u`.
        for s in "$set" "u$set"; do
            [ -d "benchmarks/satlib/$s" ] || continue
            line=$(SATLIB_SOLVER={{solver}} SATLIB_SET="$s" SATLIB_LIMIT={{limit}} \
                   SATLIB_CAP={{cap}} cargo test --release --test satlib from_env \
                   -- --ignored --nocapture 2>/dev/null | grep -E '^\[|^{{solver}},')
            [ -n "$line" ] || continue
            echo "$line"
            case "$line" in *"solved 0/"*)
                echo "# {{solver}} solves nothing at $s within {{cap}}s -- stopping"
                exit 0 ;;
            esac
        done
    done

# Download extra SATLIB RND3SAT sets by name, e.g. `just satlib-fetch uf100-430 uuf100-430`.
# The full ladder: uf{75-325,100-430,125-538,150-645,175-753,200-860,225-960,250-1065}
# and the uuf* counterpart of each.
satlib-fetch *sets:
    #!/usr/bin/env bash
    set -eu
    base=https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT
    mkdir -p benchmarks/satlib
    cd benchmarks/satlib
    for set in {{sets}}; do
        if [ -d "$set" ]; then echo "$set: already present"; continue; fi
        curl -sS -o "$set.tar.gz" "$base/$set.tar.gz"
        mkdir -p "$set"
        tar xzf "$set.tar.gz" -C "$set"
        rm "$set.tar.gz"
        echo "$set: $(find "$set" -name '*.cnf' | wc -l) instances"
    done

# Regenerate docs/scaling.csv and redraw the two scaling SVGs from it. `naive`
# enumerates 2^n valuations, so its ladder ends early; it is in the figure so the
# figure can say where.
satlib-scaling cap="10" limit="25":
    #!/usr/bin/env bash
    set -eu
    {
      echo "solver,set,vars,verdict,solved,attempted,median_ms,mean_ms,worst_ms"
      for solver in cdcl dpll naive; do
        just satlib-ladder "$solver" {{limit}} {{cap}} | grep -E "^$solver," || true
      done
    } > docs/scaling.csv
    python3 docs/make_scaling_svg.py
    python3 docs/make_scaling_svg.py --check
