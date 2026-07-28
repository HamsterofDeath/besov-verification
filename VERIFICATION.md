# Verification record

Initially captured on 2026-07-27 and independently rechecked after the
publication cleanup on 2026-07-28 from the repository root.

## Environment

Commands:

```bash
sw_vers
uname -a
lean --version
lake --version
elan --version
git --version
git -C .lake/packages/mathlib rev-parse HEAD
cat lean-toolchain
```

Output:

```text
ProductName:		macOS
ProductVersion:		26.5.2
BuildVersion:		25F84
Darwin VEACTMAC24.local 25.5.0 Darwin Kernel Version 25.5.0: Tue Jun  9 22:28:24 PDT 2026; root:xnu-12377.121.10~1/RELEASE_ARM64_T6020 arm64
Lean (version 4.32.1, arm64-apple-darwin24.6.0, commit f054605aea4b840552cca2e725580bffd1e1b704, Release)
Lake version 5.0.0-src+f054605 (Lean version 4.32.1)
elan 4.2.3 (b6cec7e10 2026-06-08)
git version 2.50.1 (Apple Git-155)
520045ab14e26149ee970e2e617ca04b09bde5d6
leanprover/lean4:v4.32.1
```

Lean was initially absent. Elan was installed using its official installer.
The project was created and prepared with:

```bash
lake +leanprover/lean4:stable new besov_verification math
cd besov_verification
lake update
lake exe cache get
```

## Full build

Command:

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd besov_verification
lake build
```

Exact output from the independent post-cleanup rebuild:

```text
✔ [8672/8676] Built BesovVerification.MainTheorem (77s)
✔ [8673/8676] Built BesovVerification.WideCutoffMainTheorem (81s)
✔ [8674/8676] Built BesovVerification.ExactCubeMainTheorem (81s)
✔ [8675/8676] Built BesovVerification (70s)
Build completed successfully (8676 jobs).
```

## Final theorem

`Main.lean` contains:

```lean
#print BesovVerification.exists_exactCube_besovEnergy_equivalence_constants
#print axioms BesovVerification.exists_exactCube_besovEnergy_equivalence_constants
```

Command:

```bash
lake env lean Main.lean
```

The printed type begins:

```text
theorem BesovVerification.exists_exactCube_besovEnergy_equivalence_constants : ∀ (d : ℕ) (α s cA CA : ℝ),
  0 < d →
    0 < α →
      0 < s →
        s < α / 2 →
          0 < cA →
            cA ≤ CA →
              ∃ c C,
                0 < c ∧
                  c < ⊤ ∧
                    0 < C ∧
                      C < ⊤ ∧
                        ∀ (ν : MeasureTheory.Measure (BesovVerification.Ambient d))
                          (u : BesovVerification.Ambient d → ℝ),
                          Measurable u →
                            BesovVerification.AhlforsRegular ν α cA CA √↑d →
                              ν.support ⊆ BesovVerification.unitCube d →
                                c * BesovVerification.besovEnergy ν α s u ≤
                                    BesovVerification.averagedEnergy ν s (√↑d) u ∧
                                  BesovVerification.averagedEnergy ν s (√↑d) u ≤
                                    C * BesovVerification.besovEnergy ν α s u
```

Exact dependency output:

```text
'BesovVerification.exists_exactCube_besovEnergy_equivalence_constants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are standard Lean axioms. The dependency list contains no
unfinished-proof axiom and no custom mathematical axiom.

## Source audit

Project-only command:

```bash
grep -RInE '\bsor''ry\b|\bad''mit\b|sor''ryAx' \
  --exclude-dir=.lake --exclude-dir=.git .
scan_status=$?
echo "PROJECT_SCAN_EXIT=$scan_status"
```

Exact output:

```text
PROJECT_SCAN_EXIT=1
```

For `grep`, exit status 1 means no matching line was found. The split shell
literals evaluate to the ordinary requested search terms without making this
record match its own command.

The requested unscoped scan was also run. It finds occurrences in downloaded
Mathlib test fixtures, tactic documentation, generated C files, and metadata
under `.lake/packages`; those dependency matches are not project source.

An additional declaration scan was run:

```bash
rg -n '^[[:space:]]*(axiom|opaque)([[:space:]]|$)' \
  --glob '*.lean' --glob '!.lake/**' --glob '!.git/**' .
```

It produced no output.

## Proof document

The complete proof was compiled from
`paper/besov-energy-equivalence-proof.tex` with Tectonic 0.17.0. The final
artifact is `output/pdf/besov-energy-equivalence-proof.pdf`.

Validation performed:

- the TeX engine completed with no warnings, errors, missing characters,
  overfull boxes, or underfull boxes;
- PDF metadata reports 17 A4 pages, no encryption, no forms, no JavaScript,
  and no suspect objects;
- text was extracted from every page and checked for empty pages, replacement
  characters, unresolved references, and placeholder text;
- all 17 pages were rendered to PNG and visually inspected.

## Result

Status A: fully verified.

The complete exact-diameter theorem compiles, both structural constants are
positive and finite, the constants are quantified before the measure and
function, the project-source audit is clean, and the final theorem depends
only on Lean's standard classical axioms.
