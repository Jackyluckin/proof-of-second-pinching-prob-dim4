# A proof of the second pinching theorem in dimension four

Jinxi Zhang, University of Cambridge

The paper concerns a smooth minimal immersion of a nonempty closed
connected four-manifold into the unit five-sphere. It proves that constant
squared second-fundamental-form norm S > 4 implies S > 8.

## Contents and proof status

- [The paper](paper/second_pinching_dim4.pdf) and its
  [standalone TeX source](paper/second_pinching_dim4.tex).
- [The Mathematica notebook](mathematica/Verification.nb) and its
  [PDF export](mathematica/Verification.pdf), explaining the exact
  calculation in Appendix A. The implementation and all required data
  are in `mathematica/`.
- [The Lean development](lean/README.md), including its entry theorem,
  hypotheses, fixed finite data and build instructions.
- [The data specification](DATA_SPEC.md), giving coefficient, witness
  and indexing conventions.

Read the paper first, then the notebook for the finite calculation.
The Lean entry theorem derives the second-pinching conclusion from the
paper's geometric hypotheses and an explicit finite verification premise.
Mathematica checks the finite coefficient identities and integer positivity
conditions, but a Lean proof of that premise is not included. The Lean
formalisation therefore remains conditional. The cited classical first
pinching classification and the corollary's full image classification are
also outside its scope. [lean/README.md](lean/README.md) states the precise
five-part premise and identifies the relevant declarations.

## Getting the files

[Download the ZIP archive](https://github.com/Jackyluckin/proof-of-second-pinching-prob-dim4/archive/refs/heads/main.zip)
and extract it, or clone the repository:

```sh
git clone https://github.com/Jackyluckin/proof-of-second-pinching-prob-dim4.git
cd proof-of-second-pinching-prob-dim4
```

The repository root is the extracted or cloned directory containing this
README. Use a writable working copy and keep the directory structure intact.
The PDF files can be read without installing Mathematica or Lean.

With Python 3 installed, the optional integrity check is:

```sh
python3 verify_files.py
```

It must report `PASS: 241 static-file hashes match.` and exit with code zero.
This checks the bytes recorded in `input_manifest.json`; it does not execute
the mathematical verification. A mismatch identifies files that differ from
the recorded distribution. Obtain a clean copy if the change was unintended;
do not replace the expected hash merely to suppress the failure.

## Mathematica

Use an activated local Wolfram installation. The notebook and command-line
entry were tested with Wolfram 15.0.1 on macOS ARM. For command-line use,
ensure [`wolframscript`](https://reference.wolfram.com/language/ref/program/wolframscript.html)
is available in the terminal. From the repository root, run:

```sh
wolframscript -file mathematica/run_verification.wls
```

Alternatively, open `mathematica/Verification.nb` in Mathematica and
evaluate its input cells in order in a fresh kernel. The command-line entry
requires no front end. Both routes use the supplied data and no Python
dependency. The saved notebook outputs identify their original run;
opening the notebook or reading its PDF does not start a new verification.

The default run performs both complete Bernstein replays. Its result must
report `Status -> PASS`, `EndpointCertified -> True` and
`TotalIntegerMatrixChecks -> 86400`, with process exit code zero. The
notebook explains the two separate counts of 43200 blocks. Each replay
also checks 5400 Gram identities and 421200 strict row inequalities.

Results are written under `mathematica/runs/<run identifier>/`; the latest
result is also written to `mathematica/verification_result.wl`. Static
certificate data remain in `mathematica/data/`. These runtime reports are
excluded from Git and from the static-file manifest.

## Lean

Install [Elan](https://github.com/leanprover/elan#installation) and Git.
Initial setup needs internet access to obtain the pinned toolchain and
dependencies. Starting from the repository root:

```sh
cd lean
lake exe cache get
lake build
cd ..
```

The project pins Lean 4.34.1 and its Mathlib revision; transitive revisions
are fixed by `lake-manifest.json`. The cache command obtains compiled
Mathlib dependencies. Building does not invoke Mathematica or require the
external certificate JSON files: the fixed integer data are already
included in the Lean sources. A successful build checks the conditional
theorem described above; it does not discharge its finite premise.

The original Python verification programs and NPZ files are retained in
the development archive as an auxiliary regression baseline. They are not
included here and are not required by either public verification route.

## Building the paper

With [TeX Live](https://tug.org/texlive/) and `latexmk` installed, start from
the repository root:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error second_pinching_dim4.tex
cd ..
```

No external figure, bibliography file or custom style is needed. A local
rebuild can change the PDF's byte hash through compiler metadata even when
its content is unchanged; the integrity manifest describes the distributed
PDF. Compile a separate working copy if the original bytes must be retained.

## Citation and version information

Please cite the accompanying manuscript when using these materials.
[CITATION.cff](CITATION.cff) supplies the author, paper title, repository URL
and distribution version. [input_manifest.json](input_manifest.json)
records the file identities, source provenance and publication updates.
When reporting a verification run, record the repository commit as well as
the run identifier and Wolfram version shown in its output.
