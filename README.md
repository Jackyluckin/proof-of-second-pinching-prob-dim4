# A proof of the second pinching theorem in dimension four

Jinxi Zhang, University of Cambridge

The paper concerns a smooth minimal immersion of a nonempty closed
connected four-manifold into the unit sphere. It proves that constant
squared second-fundamental-form norm S > 4 implies S > 8.

- [paper/second_pinching_dim4.pdf](paper/second_pinching_dim4.pdf) is the
  paper; [its TeX source](paper/second_pinching_dim4.tex) is standalone.
- [mathematica/Verification.nb](mathematica/Verification.nb) explains
  and executes the exact calculation in Appendix A.
  [Verification.pdf](mathematica/Verification.pdf) is its static export.
- [lean/README.md](lean/README.md) identifies the Lean entry theorem,
  its hypotheses, the finite computational premise and the build.
- [DATA_SPEC.md](DATA_SPEC.md) specifies the coefficient and witness data.

Read the paper first, then the notebook for the finite calculation.
The Lean theorem retains the explicit finite acceptance premise
described in its README.

## Mathematica

From this directory, with an activated Wolfram installation:

```sh
wolframscript -file mathematica/run_verification.wls
```

Alternatively, open `mathematica/Verification.nb` and evaluate its input
cells in order in a fresh kernel. The command-line entry requires no
front end. Both methods use the supplied data and no Python dependency.
The default run performs both complete Bernstein replays. Its result
must report `Status -> PASS`, `EndpointCertified -> True` and
`TotalIntegerMatrixChecks -> 86400`, with process exit code zero.
The notebook explains the two separate counts of 43200 blocks.

Run in a writable working copy. Results are written under
`mathematica/runs/`; the latest result is also written to
`mathematica/verification_result.wl`. Static certificate data remain
in `mathematica/data/`. The notebook and command-line entry were tested
with Wolfram 15.0.1 on macOS ARM.

## Lean

Install Elan, then follow [lean/README.md](lean/README.md). The project
pins Lean 4.34.1 and its Mathlib revision. Building the project does not
invoke Mathematica. The original Python verification assets are retained
in the development archive as a regression baseline and are not included
in this distribution.

## Paper source and data integrity

With TeX Live, compile from `paper/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error second_pinching_dim4.tex
```

No external figure, bibliography file or custom style is needed.
`input_manifest.json` records SHA-256 identities for all static files
and the source provenance. Runtime records and dependency caches are
excluded from the distribution.

To check the static file hashes, optionally run `python3 verify_files.py`
from the repository root. This uses the Python standard library and checks
file integrity only; it does not replay the mathematical calculation.
