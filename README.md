# Besov verification

Lean 4 / Mathlib formalization of the averaged Besov-energy equivalence for
an Ahlfors-regular measure supported in the Euclidean unit cube.

## Verification status

Status A: fully verified.

The complete theorem has been formalized and accepted by Lean. The final
theorem contains no unfinished proof terms or custom axioms asserting
substantive mathematical claims.

The final declaration is:

```lean
BesovVerification.exists_exactCube_besovEnergy_equivalence_constants
```

## Full proof document

- [Exact proof as PDF](output/pdf/besov-energy-equivalence-proof.pdf)
- [Complete LaTeX source](paper/besov-energy-equivalence-proof.tex)

The paper gives the complete mathematical proof, including the structural
constants, the exact-diameter open-ball endpoint argument, the extended-value
and Tonelli details, and a map from every proof stage to its Lean source file.

For fixed

```text
d > 0, α > 0, s > 0, s < α/2, cA > 0, cA ≤ CA,
```

Lean constructs positive finite `c,C : ℝ≥0∞` before quantifying over the
measure and function. For every measurable `u` and every measure `ν` that is
`α`-Ahlfors regular through `R = sqrt d` and whose support lies in
`[0,1]^d`, it proves

```text
c * besovEnergy ν α s u
  ≤ averagedEnergy ν s (sqrt d) u

averagedEnergy ν s (sqrt d) u
  ≤ C * besovEnergy ν α s u.
```

Quantifying the constants before `ν` and `u` machine-checks that they depend
only on `d, α, s, cA, CA`.

## What was formalized

- Euclidean ambient space and unit cube;
- Ahlfors lower and upper open-ball estimates;
- atomlessness from upper Ahlfors regularity;
- measurability of all moving-ball and scale integrands;
- normalization by the Ahlfors ball-mass bounds;
- the scalar scale integral and its Tonelli expansion;
- exact decomposition into truncated singular energy and global variation;
- a quantitative corner-avoidance construction using all `2^d` cube corners;
- a positive-measure anchor ball at a scale strictly below `sqrt d`;
- global-variation control through the anchor;
- scale-tail control using monotonicity in the radius;
- automatic finiteness and `SFinite` for cube-supported Ahlfors measures;
- both final comparison inequalities, including the zero-measure case;
- positivity and finiteness of both structural constants.

## Representation choices

- Energies take values in `ℝ≥0∞`, so infinite energies are allowed.
- `u` is assumed measurable. No `MemLp` hypothesis is needed; the result is
  therefore stronger than the requested result for measurable `L²`
  representatives.
- Integrals are over the ambient Euclidean space. The support hypothesis makes
  this equivalent to integrating over the support.
- The singular kernel is explicitly zero on the diagonal.
- The final theorem retains `s < α/2` for fidelity. The proof itself only
  needs `α > 0` and `s > 0`.
- `d > 0`, `cA > 0`, and `cA ≤ CA` are explicit.

## The open-ball endpoint

The proof does not assume that an open ball of radius `sqrt d` contains the
entire cube. Instead it:

1. chooses a structural corner scale `δ`;
2. proves that the union of small neighborhoods of all cube corners cannot
   contain the support;
3. finds a supported point uniformly away from every corner;
4. shows the cube is contained in a ball of radius
   `sqrt (d - δ²) < sqrt d` around that point;
5. constructs a positive-measure anchor ball whose scale is still strictly
   below `sqrt d`.

This supplies a nonempty terminal interval of scales and resolves the
endpoint rigorously.

## Pinned environment

- OS: macOS 26.5.2, Darwin 25.5.0, arm64
- Lean: 4.32.1
- Lake: 5.0.0
- Elan: 4.2.3
- Mathlib commit: `520045ab14e26149ee970e2e617ca04b09bde5d6`
- Toolchain: `leanprover/lean4:v4.32.1`

## Build and audit

```bash
lake build
lake env lean Main.lean
grep -RInE '\bsor''ry\b|\bad''mit\b|sor''ryAx' \
  --exclude-dir=.lake --exclude-dir=.git .
```

With [Tectonic](https://tectonic-typesetting.github.io/) installed, rebuild
the paper from the repository root with:

```bash
mkdir -p output/pdf
tectonic --outdir output/pdf paper/besov-energy-equivalence-proof.tex
```

The split shell literals in the scan command prevent the command from
matching its own text while evaluating to the ordinary requested audit.

See [DESIGN.md](DESIGN.md) for the formal statement and proof architecture,
and [VERIFICATION.md](VERIFICATION.md) for exact captured output.

## Source layout

The principal final-stage files are:

```text
BesovVerification/
├── FullEnergyDecomposition.lean
├── AnchorEstimate.lean
├── TailEstimate.lean
├── CubeAnchor.lean
├── FixedCornerScaleAnchor.lean
├── StructuralAnchorEstimate.lean
├── ExactCubeConstants.lean
└── ExactCubeMainTheorem.lean
```

The earlier definition, measurability, Ahlfors, normalization, scale-integral,
and Tonelli modules remain separate and are imported by these files.
