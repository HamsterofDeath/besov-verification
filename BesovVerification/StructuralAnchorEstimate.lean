import BesovVerification.AnchorEstimate

/-!
# Structural anchor estimate

This file replaces the actual anchor and total masses in the anchor estimate
by uniform structural lower and upper bounds.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- A positive lower anchor-mass bound forces the structural total-mass bound to be positive. -/
theorem structuralTotalMass_pos
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (S : Set X) {L U : ℝ≥0∞}
    (hL : L ≤ ν S) (hLpos : 0 < L) (hU : ν Set.univ ≤ U) :
    0 < U := by
  have hSuniv : ν S ≤ ν Set.univ :=
    measure_mono (Set.subset_univ S)
  exact hLpos.trans_le (hL.trans (hSuniv.trans hU))

/-- Positivity and finiteness of the uniform anchor coefficient. -/
theorem structuralAnchorCoefficient_pos_finite
    {L U : ℝ≥0∞} (hLpos : 0 < L) (hLU : L ≤ U) (hUfin : U < ∞) :
    0 < 4 * U / L ∧ 4 * U / L < ∞ := by
  have hUpos : 0 < U := hLpos.trans_le hLU
  have hLfin : L < ∞ := lt_of_le_of_lt hLU hUfin
  have hnumpos : 0 < 4 * U :=
    ENNReal.mul_pos (by norm_num) hUpos.ne'
  have hnumfin : 4 * U < ∞ :=
    ENNReal.mul_lt_top (by norm_num) hUfin
  exact ⟨ENNReal.div_pos hnumpos.ne' hLfin.ne,
    ENNReal.div_lt_top hnumfin.ne hLpos.ne'⟩

/--
Uniform anchor estimate.  A structural lower bound `L` for the anchor mass
and upper bound `U` for the total mass replace the measure-dependent ratio.
-/
theorem globalVariation_le_structural_anchor_localEnergy
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    (S : Set X) {ρ : ℝ}
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ)
    {L U : ℝ≥0∞}
    (hL : L ≤ ν S) (hLpos : 0 < L)
    (hU : ν Set.univ ≤ U) (hUfin : U < ∞) :
    globalVariation ν u ≤
      (4 * U / L) * localEnergy ν u ρ := by
  have hSuniv : ν S ≤ ν Set.univ :=
    measure_mono (Set.subset_univ S)
  have hSpos : 0 < ν S :=
    hLpos.trans_le hL
  have hSfin : ν S < ∞ :=
    lt_of_le_of_lt (hSuniv.trans hU) hUfin
  have hbase :=
    globalVariation_le_anchor_localEnergy
      ν hu S hanchor hSpos hSfin
  have hratio :
      4 * ν Set.univ / ν S ≤ 4 * U / L := by
    apply ENNReal.div_le_div
    · gcongr
    · exact hL
  calc
    globalVariation ν u ≤
        (4 * ν Set.univ / ν S) * localEnergy ν u ρ := hbase
    _ ≤ (4 * U / L) * localEnergy ν u ρ := by
      gcongr

/--
Bundled form: the displayed structural coefficient is positive and finite and
controls global variation by the local energy.
-/
theorem structural_anchor_comparison
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    (S : Set X) {ρ : ℝ}
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ)
    {L U : ℝ≥0∞}
    (hL : L ≤ ν S) (hLpos : 0 < L)
    (hU : ν Set.univ ≤ U) (hUfin : U < ∞) :
    0 < 4 * U / L ∧ 4 * U / L < ∞ ∧
      globalVariation ν u ≤
        (4 * U / L) * localEnergy ν u ρ := by
  have hSuniv : ν S ≤ ν Set.univ :=
    measure_mono (Set.subset_univ S)
  have hLU : L ≤ U :=
    hL.trans (hSuniv.trans hU)
  exact ⟨(structuralAnchorCoefficient_pos_finite hLpos hLU hUfin).1,
    (structuralAnchorCoefficient_pos_finite hLpos hLU hUfin).2,
    globalVariation_le_structural_anchor_localEnergy
      ν hu S hanchor hL hLpos hU hUfin⟩

end BesovVerification
