# Lean development

The entry theorem is
`SecondPinching.secondPinching_dim4_of_released_certificate` in
[ReleasedPaperTheorem.lean](SecondPinching/ReleasedPaperTheorem.lean).
It concludes `8 < S` for the smooth minimal sphere immersion and constant
second-fundamental-form norm in the paper, assuming `4 < S` and
`FiniteEndpointAccepted releasedEndpointData`.

## Build

The configuration pins Lean **4.34.1** and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`; transitive revisions are
fixed by `lake-manifest.json`. With Elan installed, run from this directory:

```sh
lake exe cache get
lake build
```

The first command obtains Mathlib's compiled dependency cache. The
project builds from the supplied sources and requires neither a Wolfram
installation nor the external certificate JSON files. The fixed integer
literals used by `releasedEndpointData` are already in the existing
`ReleasedEndpointLiterals.lean`, `ReleasedLeaf00.lean` through
`ReleasedLeaf23.lean`, and their supporting modules.

## Scope of the formalisation

The main theorem is conditional on the five finite assertions defined
below. Its geometric hypotheses are the original manifold, immersion,
minimality and constant-norm hypotheses of the paper. In the included
source, Simons' identity is a proved theorem rather than an additional
external premise: see `immersionFrameFourth_simons` and
`immersionScalarLaplacian_simons` in
[ImmersionSimons.lean](SecondPinching/ImmersionSimons.lean).
The entry theorem has no separate Simons or Peng--Terng parameter.

### Geometric inputs

| Declaration or input | Mathematical content | Paper | Form in the project |
| --- | --- | --- | --- |
| `SphereImmersion M` | Smooth map to the unit five-sphere with injective derivative | `thm:main` | Structure in [NativeSphereImmersion.lean](SecondPinching/NativeSphereImmersion.lean); fields `map`, `smooth`, `immersion` |
| `hminimal`, `hSnorm`, `hS` | Minimality, actual squared second-fundamental-form norm equal to S, and 4 < S | `thm:main` | Parameters of the entry theorem |
| `immersionFrameFourth_simons`, `immersionScalarLaplacian_simons` | Tensor and scalar Simons identities for the actual local immersion | `eq:simons`, citing Simons | Proved theorems in `ImmersionSimons.lean`, not external premises |

The source manifold has the four-dimensional boundaryless model,
`T2Space`, `CompactSpace` and `ConnectedSpace`; the last includes
nonemptiness. The cited classical first pinching classification and the
corollary's full image classification are not re-proved by this project
and are not inputs to its second-pinching entry theorem.

### Finite verification assertions

[FiniteEndpointData.lean](SecondPinching/FiniteEndpointData.lean) defines
`FiniteEndpointAccepted D` as the conjunction of the five assertions
below. In the entry theorem, `D` is the fixed instance
`releasedEndpointData` from
[ReleasedCertificate.lean](SecondPinching/ReleasedCertificate.lean).
Each assertion enters through the theorem parameter `hcertificate`;
they are not axioms or newly inserted proof terms. Their external
mathematical basis is the exact polynomial reconstruction and integer
verification described in the Mathematica supplement and Appendix A.

| Conjunct | Exact assertion | Paper correspondence |
| --- | --- | --- |
| First | `exactCoefficientCheck 14 D.polynomial endpointPolynomial = true` | Full endpoint polynomial identity, `eq:Pidentity` |
| Second | For every leaf, equality of `D.polynomial` with `certificateExpansionPolynomial leaf (D.controls leaf)` under `exactCoefficientCheck 14` | Bernstein expansion on every rectangle, `eq:Bernstein` |
| Third | `0 < D.bernsteinIntegerScale leaf ij` for every leaf and control index | Positive integer denominator clearing |
| Fourth | Under `exactCoefficientCheck 12`, each control quartic equals `integerBlockQuartic` of its Gram numerator with denominator `compressedGramConstant * bernsteinIntegerScale` | Complete Gram coefficient identity, `eq:Gramcertificate` |
| Fifth | `integerCertificateCheck` is true for every control's eight Gram blocks and their supplied congruence witnesses | Symmetry and strict integer row inequalities, `eq:integercriterion` |

Here `leaf : Fin 24`, `ij : ControlIndex` ranges over 15 by 15 controls,
and `b : Fin 8` selects a block. The coordinate and normalization
conventions are in [DATA_SPEC.md](../DATA_SPEC.md). In particular,
the control quartic is the scaled P coefficient divided by the positive
Bernstein scale sigma. Its Lean Gram denominator is
`compressedGramConstant * sigma`; the normalized Gram representation in
the data specification uses `compressedGramConstant * d`. These
denominators have different roles and have not been identified.

`releasedEndpoint_bound` derives the bound W_(1/2) <= -1/10000 from
this finite premise. The final theorem then derives the geometric
contradiction. An external Wolfram success result establishes the
corresponding finite mathematical assertions; it does not insert a
Lean proof term discharging `hcertificate`.
