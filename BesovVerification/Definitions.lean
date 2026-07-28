import Mathlib

/-!
# Definitions for the Besov-energy verification

All energies take values in `ℝ≥0∞`, so no finiteness assumption on `u` is
built into the definitions.  The ambient space is Mathlib's genuine
Euclidean `ℓ²` space, rather than the supremum metric on a plain function
type.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- Euclidean `d`-space with its Borel measurable structure. -/
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The coordinate cube `[0,1]^d`. -/
def unitCube (d : ℕ) : Set (Ambient d) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/--
The Ahlfors bounds used in the informal theorem.  Real powers are formed in
`ℝ` and then embedded in `ℝ≥0∞`.
-/
structure AhlforsRegular {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (α cA CA R : ℝ) : Prop where
  lower :
    ∀ x ∈ Measure.support ν, ∀ r : ℝ, 0 < r → r ≤ R →
      ENNReal.ofReal (cA * r ^ α) ≤ ν (Metric.ball x r)
  upper :
    ∀ x ∈ Measure.support ν, ∀ r : ℝ, 0 < r → r ≤ R →
      ν (Metric.ball x r) ≤ ENNReal.ofReal (CA * r ^ α)

/-- The nonnegative squared oscillation `|u(x)-u(y)|²`. -/
def differenceSq {X : Type*} (u : X → ℝ) (x y : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((u x - u y) ^ 2)

/-- The unnormalised local energy at radius `r`. -/
def ballEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (u : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ∫⁻ y in Metric.ball x r, differenceSq u x y ∂ν

/-- The unnormalised local energy at radius `r`, integrated in the center. -/
def localEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (u : X → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ballEnergy ν u r x ∂ν

/-- The ball-measure-normalised local energy at radius `r`. -/
def normalizedLocalEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (u : X → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (ν (Metric.ball x r))⁻¹ * ballEnergy ν u r x ∂ν

/--
The averaged seminorm squared from the question.  The scale integral is
restricted to `(0,R]`; changing the single endpoint is immaterial for
Lebesgue measure, but this convention makes the formal cutoff explicit.
-/
def averagedEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (s R : ℝ) (u : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioc 0 R,
    (ENNReal.ofReal r).rpow (-1 - 2 * s) *
      normalizedLocalEnergy ν u r

/--
The scale-weighted unnormalised local energy.  With `p = α + 2s`, its
weight is `r⁻¹⁻ᵖ`.
-/
def scaleEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (α s R : ℝ) (u : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioc 0 R,
    (ENNReal.ofReal r).rpow (-1 - α - 2 * s) * localEnergy ν u r

/--
The singular Besov energy.  The diagonal value is defined to be zero
explicitly, avoiding an implicit `0 · ∞` convention.
-/
def besovEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (α s : ℝ) (u : X → ℝ) : ℝ≥0∞ := by
  classical
  exact
    ∫⁻ x, ∫⁻ y,
      if x = y then 0
      else differenceSq u x y *
        (ENNReal.ofReal (dist x y)).rpow (-(α + 2 * s)) ∂ν ∂ν

/-- The unweighted global oscillation energy. -/
def globalVariation {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (u : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, differenceSq u x y ∂ν ∂ν

end BesovVerification
