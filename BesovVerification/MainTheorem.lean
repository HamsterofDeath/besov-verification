import BesovVerification.Ahlfors
import BesovVerification.EnergyIdentity
import BesovVerification.Normalization

/-!
# Assembled verified comparisons

The main theorem in this file compares the averaged energy with the exact
truncated kernel produced by the scale integration.  A second theorem proves
the upper bound by the full singular Besov energy.  The exact two-sided
full-energy result, including the quantitative anchor-set argument, is assembled
in `ExactCubeMainTheorem`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/--
The scale kernel is bounded by `p⁻¹ t⁻ᵖ`.  This is the pointwise estimate that
gives the easy direction from the truncated energy to the full Besov energy.
-/
theorem truncatedScaleKernel_le_singular
    {p R t : ℝ} (hp : 0 < p) :
    truncatedScaleKernel p R t ≤
      (ENNReal.ofReal p)⁻¹ * (ENNReal.ofReal t).rpow (-p) := by
  unfold truncatedScaleKernel
  split_ifs with h
  · have ht : 0 < t := h.1
    have hR : 0 ≤ R := le_trans ht.le h.2
    calc
      ENNReal.ofReal ((t ^ (-p) - R ^ (-p)) / p) ≤
          ENNReal.ofReal (t ^ (-p) / p) := by
            apply ENNReal.ofReal_le_ofReal
            have hnonneg := Real.rpow_nonneg hR (-p)
            exact (div_le_div_iff_of_pos_right hp).2 (sub_le_self _ hnonneg)
      _ = (ENNReal.ofReal p)⁻¹ *
          (ENNReal.ofReal t).rpow (-p) := by
            rw [ENNReal.ofReal_div_of_pos hp,
              ← ENNReal.ofReal_rpow_of_pos ht]
            simp only [div_eq_mul_inv]
            exact mul_comm _ _
  · exact bot_le

/--
The exact comparison obtained from Ahlfors normalization and Tonelli.  This
theorem needs only `p = α + 2s > 0`; it does not use `s < α/2` or `MemLp`.
-/
theorem averagedEnergy_truncated_comparison
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hcA : 0 < cA) (hCA : 0 < CA)
    (hp : 0 < α + 2 * s) :
    (ENNReal.ofReal CA)⁻¹ *
        truncatedEnergy ν (α + 2 * s) R u ≤
        averagedEnergy ν s R u ∧
      averagedEnergy ν s R u ≤
        (ENNReal.ofReal cA)⁻¹ *
          truncatedEnergy ν (α + 2 * s) R u := by
  have hnorm :=
    normalization_comparison (s := s) ν hu hreg hcA hCA
  rw [scaleEnergy_eq_truncatedEnergy ν hp hu] at hnorm
  exact hnorm

/-- The combined exponent `α + 2s` is only a repackaging of `besovEnergy`'s parameters. -/
theorem besovEnergy_repackage
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (α s : ℝ) (u : X → ℝ) :
    besovEnergy ν (α + 2 * s) 0 u = besovEnergy ν α s u := by
  unfold besovEnergy
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, ↓reduceIte]
    congr 2
    ring

/--
The full, nontruncated upper estimate.  It is one direction of the requested
equivalence and does not require cube geometry or an anchor set.
-/
theorem truncatedEnergy_le_besovEnergy
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {p R : ℝ} (hp : 0 < p) :
    truncatedEnergy ν p R u ≤
      (ENNReal.ofReal p)⁻¹ * besovEnergy ν p 0 u := by
  let raw : X × X → ℝ≥0∞ := fun q =>
    differenceSq u q.1 q.2 *
      (ENNReal.ofReal (dist q.1 q.2)).rpow (-p)
  have hraw : Measurable raw := by
    apply Measurable.mul
    · exact measurable_differenceSq_uncurry hu
    · exact
        (ENNReal.continuous_rpow_const (y := -p)).measurable.comp
          (ENNReal.measurable_ofReal.comp measurable_dist)
  have hinner :
      Measurable (fun x => ∫⁻ y, raw (x, y) ∂ν) :=
    hraw.lintegral_prod_right'
  have hbesov :
      besovEnergy ν p 0 u =
        ∫⁻ x, ∫⁻ y, raw (x, y) ∂ν ∂ν := by
    unfold besovEnergy
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    by_cases hxy : x = y
    · subst y
      simp [raw, differenceSq]
    · simp [raw, hxy]
  rw [hbesov, ← lintegral_const_mul _ hinner]
  unfold truncatedEnergy
  apply lintegral_mono
  intro x
  have hrawx : Measurable (fun y => raw (x, y)) :=
    hraw.comp (by fun_prop)
  change
    (∫⁻ y, truncatedScaleKernel p R (dist x y) *
      differenceSq u x y ∂ν) ≤
      (ENNReal.ofReal p)⁻¹ * (∫⁻ y, raw (x, y) ∂ν)
  rw [← lintegral_const_mul _ hrawx]
  apply lintegral_mono
  intro y
  calc
    truncatedScaleKernel p R (dist x y) * differenceSq u x y ≤
        ((ENNReal.ofReal p)⁻¹ *
          (ENNReal.ofReal (dist x y)).rpow (-p)) *
            differenceSq u x y :=
      mul_le_mul_left (truncatedScaleKernel_le_singular hp) _
    _ = (ENNReal.ofReal p)⁻¹ * raw (x, y) := by
      simp only [raw]
      ac_rfl

/--
Verified upper half of the original claimed equivalence.
-/
theorem averagedEnergy_le_besovEnergy
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hcA : 0 < cA) (hCA : 0 < CA)
    (hp : 0 < α + 2 * s) :
    averagedEnergy ν s R u ≤
      ((ENNReal.ofReal cA)⁻¹ * (ENNReal.ofReal (α + 2 * s))⁻¹) *
        besovEnergy ν α s u := by
  calc
    averagedEnergy ν s R u ≤
        (ENNReal.ofReal cA)⁻¹ *
          truncatedEnergy ν (α + 2 * s) R u :=
      (averagedEnergy_truncated_comparison ν hu hreg hcA hCA hp).2
    _ ≤ (ENNReal.ofReal cA)⁻¹ *
          ((ENNReal.ofReal (α + 2 * s))⁻¹ *
            besovEnergy ν (α + 2 * s) 0 u) :=
      mul_le_mul_right
        (truncatedEnergy_le_besovEnergy ν hu hp) _
    _ = ((ENNReal.ofReal cA)⁻¹ *
          (ENNReal.ofReal (α + 2 * s))⁻¹) *
        besovEnergy ν (α + 2 * s) 0 u := by
      rw [mul_assoc]
    _ = ((ENNReal.ofReal cA)⁻¹ *
          (ENNReal.ofReal (α + 2 * s))⁻¹) *
        besovEnergy ν α s u := by
      rw [besovEnergy_repackage]

/--
Existential finite-positive-constant form of the verified upper half, matching
the quantifier style requested in the handover.
-/
theorem exists_finite_upper_comparison_constant
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hcA : 0 < cA) (hCA : 0 < CA)
    (hp : 0 < α + 2 * s) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧
      averagedEnergy ν s R u ≤ C * besovEnergy ν α s u := by
  refine ⟨(ENNReal.ofReal cA)⁻¹ *
      (ENNReal.ofReal (α + 2 * s))⁻¹, ?_, ?_, ?_⟩
  · exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
  · apply ENNReal.mul_lt_top
    · exact (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.2 hcA))
    · exact (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.2 hp))
  · exact averagedEnergy_le_besovEnergy ν hu hreg hcA hCA hp

end BesovVerification
