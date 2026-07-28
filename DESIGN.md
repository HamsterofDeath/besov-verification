# Formalization design and exact theorem

## Informal target

For an `α`-Ahlfors-regular Borel measure `ν` supported in
`Q = [0,1]^d`, with `R = sqrt d`, prove

```text
c * besovEnergy ν α s u ≤ averagedEnergy ν s R u
averagedEnergy ν s R u ≤ C * besovEnergy ν α s u
```

for positive finite constants depending only on
`d, α, s, cA, CA`.

## Formal representation

- Ambient space:
  `Ambient d := EuclideanSpace ℝ (Fin d)`.
- Cube:
  `unitCube d := {x | ∀ i, x i ∈ Set.Icc 0 1}`.
- Ahlfors regularity:

  ```lean
  AhlforsRegular ν α cA CA R
  ```

  stores the lower and upper open-ball estimates at every support point for
  every `0 < r ≤ R`.
- Function: an ambient measurable `u : Ambient d → ℝ`.
- Energies: `ℝ≥0∞`, allowing infinite values.
- Scale interval: Lebesgue measure restricted to `Set.Ioc 0 R`.
- Diagonal: `besovEnergy` assigns the singular integrand value zero when
  `x = y`.

## Final compiled theorem

```lean
theorem exists_exactCube_besovEnergy_equivalence_constants
    (d : ℕ) (α s cA CA : ℝ)
    (hd : 0 < d) (hα : 0 < α) (hs : 0 < s)
    (hsα : s < α / 2)
    (hcA : 0 < cA) (hcACA : cA ≤ CA) :
    ∃ c C : ℝ≥0∞,
      0 < c ∧ c < ∞ ∧ 0 < C ∧ C < ∞ ∧
      ∀ (ν : Measure (Ambient d)) (u : Ambient d → ℝ),
        Measurable u →
        AhlforsRegular ν α cA CA (Real.sqrt d) →
        Measure.support ν ⊆ unitCube d →
        c * besovEnergy ν α s u ≤
            averagedEnergy ν s (Real.sqrt d) u ∧
          averagedEnergy ν s (Real.sqrt d) u ≤
            C * besovEnergy ν α s u
```

The order of quantifiers is important: `c` and `C` are selected before `ν`
and `u`. Thus their structural dependence is part of the theorem, not merely
an explanation outside Lean.

## Proof architecture

### 1. Normalization and Tonelli

Ahlfors bounds give

```text
CA⁻¹ * scaleEnergy ≤ averagedEnergy ≤ cA⁻¹ * scaleEnergy.
```

Tonelli and the scalar scale integral identify `scaleEnergy` with an exact
truncated double-integral kernel.

### 2. Full-energy decomposition

For `p = α + 2s`,

```text
besovEnergy
  ≤ ofReal(p) * truncatedEnergy
    + ofReal(R)^(-p) * globalVariation.
```

The corresponding equality is also proved when almost every pair has
distance at most `R`.

### 3. Structural corner scale

`exists_cornerScale` chooses `δ > 0` using only the numerical structural
parameters, so that all `2^d` corner neighborhoods have total upper mass
strictly below one Ahlfors lower bound.

`exists_fixedCornerScale_unitCube_anchor_ball` then works for every qualifying
nonzero measure while keeping that same `δ`. It returns a measurable anchor
set `S` with

```text
ofReal (cA * ε^α) ≤ ν S
```

and

```text
dist x z < λ * sqrt d
```

for every supported `x` and every `z ∈ S`, where

```text
ε = (sqrt d - sqrt (d - δ²)) / 2
λ = (sqrt d + sqrt (d - δ²)) / (2 * sqrt d)
0 < λ < 1.
```

### 4. Uniform mass and oscillation bounds

The anchor property gives the structural total-mass estimate

```text
ν univ ≤ ofReal (CA * (sqrt d)^α).
```

The three-point squared-difference inequality then yields a bound for
`globalVariation` using only the structural upper and lower mass bounds, not
the actual values of `ν univ` or `ν S`.

### 5. Terminal scale interval

Monotonicity of `localEnergy` and integration over
`(λ sqrt d, sqrt d]` control the anchor-scale local energy by `scaleEnergy`.
The interval has positive weight because `λ < 1`.

### 6. Assembly

The global-variation bound closes the reverse Besov comparison through the
full-energy decomposition. Ahlfors normalization supplies the final averaged
energy bound. All divisions are by proved positive finite quantities.

The zero-measure case is handled separately; all energies then vanish.

## Relation to the informal statement

The mathematical claim is fully represented. The following are
representational or strengthening differences:

| Topic | Informal formulation | Compiled formulation |
|---|---|---|
| Values | Nonnegative seminorm squares | Extended nonnegative energies |
| Function | `u ∈ L²(E,ν)` | Any measurable ambient `u` |
| Domain of integration | Support `E` | Ambient space, with support conull |
| Constants | Depend only on structural data | Quantified before `ν,u` |
| `SFinite` | Not mentioned | Derived from Ahlfors regularity and cube support |
| Diagonal | Implicit | Explicitly zero |
| Exponent restriction | `s < α/2` | Retained, though unused after positivity |

Removing `MemLp` does not weaken the result: the extended-valued comparison
holds for a larger class of functions, including measurable `L²`
representatives.

## Additional verified theorem

`exists_wideCutoff_besovEnergy_equivalence_constants` proves a second complete
equivalence when the cutoff is strictly larger than `sqrt d`. It is no longer
needed to repair the endpoint, but remains a useful independent
generalization and cross-check.
