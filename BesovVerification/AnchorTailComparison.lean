import BesovVerification.AnchorEstimate
import BesovVerification.Normalization
import BesovVerification.TailEstimate

/-!
# Anchor-set control by the scale and averaged energies

This file composes the geometric anchor estimate with the positive mass of a
terminal scale interval.  It also records the one-sided normalization estimate
needed to pass from the unnormalised scale energy to the averaged energy.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- The explicit coefficient in the anchor-set bound by `scaleEnergy`. -/
def anchorTailScaleConstant
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (S : Set X) (p ρ R : ℝ) : ℝ≥0∞ :=
  (4 * ν Set.univ / ν S) *
    (ENNReal.ofReal ((ρ ^ (-p) - R ^ (-p)) / p))⁻¹

/-- The corresponding coefficient after Ahlfors normalization. -/
def anchorTailAveragedConstant
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (S : Set X) (p ρ R CA : ℝ) : ℝ≥0∞ :=
  anchorTailScaleConstant ν S p ρ R * ENNReal.ofReal CA

/--
The anchor-set estimate and the terminal-scale estimate combine to control
the complete global oscillation by the scale energy.
-/
theorem globalVariation_le_anchorTailScaleConstant_mul_scaleEnergy
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    (S : Set X) {α s ρ R : ℝ}
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ)
    (hSpos : 0 < ν S) (hSfin : ν S < ∞)
    (hp : 0 < α + 2 * s) (hρ : 0 < ρ) (hρR : ρ < R) :
    globalVariation ν u ≤
      anchorTailScaleConstant ν S (α + 2 * s) ρ R *
        scaleEnergy ν α s R u := by
  calc
    globalVariation ν u ≤
        (4 * ν Set.univ / ν S) * localEnergy ν u ρ :=
      globalVariation_le_anchor_localEnergy
        ν hu S hanchor hSpos hSfin
    _ ≤ (4 * ν Set.univ / ν S) *
          ((ENNReal.ofReal
            ((ρ ^ (-(α + 2 * s)) - R ^ (-(α + 2 * s))) /
              (α + 2 * s)))⁻¹ *
            scaleEnergy ν α s R u) :=
      mul_le_mul_right
        (localEnergy_le_inv_scaleTailMass_mul_scaleEnergy
          ν hp hρ hρR) _
    _ = anchorTailScaleConstant ν S (α + 2 * s) ρ R *
          scaleEnergy ν α s R u := by
      unfold anchorTailScaleConstant
      rw [mul_assoc]

/--
Only the upper Ahlfors bound is needed to recover `scaleEnergy` from
`averagedEnergy`.
-/
theorem inv_upperAhlfors_mul_scaleEnergy_le_averagedEnergy
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hCA : 0 < CA) :
    (ENNReal.ofReal CA)⁻¹ * scaleEnergy ν α s R u ≤
      averagedEnergy ν s R u := by
  have hlocal : Measurable (localEnergy ν u) :=
    measurable_localEnergy_radius ν hu
  have hscale :
      Measurable
        (fun r : ℝ =>
          (ENNReal.ofReal r).rpow (-1 - α - 2 * s) *
            localEnergy ν u r) := by
    exact
      ((ENNReal.continuous_rpow_const
        (y := -1 - α - 2 * s)).measurable.comp
          ENNReal.measurable_ofReal).mul hlocal
  rw [scaleEnergy, averagedEnergy, ← lintegral_const_mul _ hscale]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hnorm :=
    normalizedLocalEnergy_lower ν hu hreg hr.1 hr.2
  calc
    (ENNReal.ofReal CA)⁻¹ *
        ((ENNReal.ofReal r).rpow (-1 - α - 2 * s) *
          localEnergy ν u r) =
        ((ENNReal.ofReal r).rpow (-1 - 2 * s) *
          (ENNReal.ofReal (CA * r ^ α))⁻¹) *
            localEnergy ν u r := by
              rw [normalization_weight_identity hCA hr.1]
              ac_rfl
    _ ≤ (ENNReal.ofReal r).rpow (-1 - 2 * s) *
          normalizedLocalEnergy ν u r := by
            rw [mul_assoc]
            exact mul_le_mul_right hnorm _

/-- Cancellation of the positive finite upper Ahlfors constant. -/
theorem scaleEnergy_le_upperAhlfors_mul_averagedEnergy
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hCA : 0 < CA) :
    scaleEnergy ν α s R u ≤
      ENNReal.ofReal CA * averagedEnergy ν s R u := by
  let A : ℝ≥0∞ := ENNReal.ofReal CA
  have hA0 : A ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hCA
  have hAtop : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hnorm :
      A⁻¹ * scaleEnergy ν α s R u ≤ averagedEnergy ν s R u := by
    exact inv_upperAhlfors_mul_scaleEnergy_le_averagedEnergy
      ν hu hreg hCA
  calc
    scaleEnergy ν α s R u =
        A * (A⁻¹ * scaleEnergy ν α s R u) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, one_mul]
    _ ≤ A * averagedEnergy ν s R u :=
      mul_le_mul_right hnorm A

/--
The full global variation is bounded by the averaged energy with an explicit
anchor/scale/Ahlfors coefficient.
-/
theorem globalVariation_le_anchorTailAveragedConstant_mul_averagedEnergy
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    (S : Set X) {α s cA CA ρ R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ)
    (hSpos : 0 < ν S) (hSfin : ν S < ∞)
    (hp : 0 < α + 2 * s) (hρ : 0 < ρ) (hρR : ρ < R)
    (hCA : 0 < CA) :
    globalVariation ν u ≤
      anchorTailAveragedConstant ν S (α + 2 * s) ρ R CA *
        averagedEnergy ν s R u := by
  calc
    globalVariation ν u ≤
        anchorTailScaleConstant ν S (α + 2 * s) ρ R *
          scaleEnergy ν α s R u :=
      globalVariation_le_anchorTailScaleConstant_mul_scaleEnergy
        ν hu S hanchor hSpos hSfin hp hρ hρR
    _ ≤ anchorTailScaleConstant ν S (α + 2 * s) ρ R *
          (ENNReal.ofReal CA * averagedEnergy ν s R u) :=
      mul_le_mul_right
        (scaleEnergy_le_upperAhlfors_mul_averagedEnergy
          ν hu hreg hCA) _
    _ = anchorTailAveragedConstant ν S (α + 2 * s) ρ R CA *
          averagedEnergy ν s R u := by
      unfold anchorTailAveragedConstant
      rw [mul_assoc]

/--
Under finite total mass, the explicit scale-energy coefficient is positive and
finite.
-/
theorem anchorTailScaleConstant_pos_and_lt_top
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (S : Set X) {p ρ R : ℝ}
    (hSpos : 0 < ν S) (hSfin : ν S < ∞)
    (hunivfin : ν Set.univ < ∞)
    (hp : 0 < p) (hρ : 0 < ρ) (hρR : ρ < R) :
    0 < anchorTailScaleConstant ν S p ρ R ∧
      anchorTailScaleConstant ν S p ρ R < ∞ := by
  have hSuniv : ν S ≤ ν Set.univ :=
    measure_mono (Set.subset_univ S)
  have hunivpos : 0 < ν Set.univ :=
    hSpos.trans_le hSuniv
  have hnumpos : 0 < 4 * ν Set.univ :=
    ENNReal.mul_pos (by norm_num) hunivpos.ne'
  have hnumfin : 4 * ν Set.univ < ∞ :=
    ENNReal.mul_lt_top (by norm_num) hunivfin
  have hratioPos : 0 < 4 * ν Set.univ / ν S :=
    ENNReal.div_pos hnumpos.ne' hSfin.ne
  have hratioFin : 4 * ν Set.univ / ν S < ∞ :=
    ENNReal.div_lt_top hnumfin.ne hSpos.ne'
  let K : ℝ≥0∞ :=
    ENNReal.ofReal ((ρ ^ (-p) - R ^ (-p)) / p)
  have hpow : R ^ (-p) < ρ ^ (-p) :=
    Real.rpow_lt_rpow_of_neg hρ hρR (neg_neg_of_pos hp)
  have hKpos : 0 < K :=
    ENNReal.ofReal_pos.2 (div_pos (sub_pos.2 hpow) hp)
  have hKinv0 : K⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hKinvfin : K⁻¹ < ∞ :=
    ENNReal.inv_lt_top.mpr hKpos
  unfold anchorTailScaleConstant
  change
    0 < (4 * ν Set.univ / ν S) * K⁻¹ ∧
      (4 * ν Set.univ / ν S) * K⁻¹ < ∞
  exact
    ⟨ENNReal.mul_pos hratioPos.ne' hKinv0,
      ENNReal.mul_lt_top hratioFin hKinvfin⟩

/-- The averaged-energy coefficient is likewise positive and finite. -/
theorem anchorTailAveragedConstant_pos_and_lt_top
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (S : Set X) {p ρ R CA : ℝ}
    (hSpos : 0 < ν S) (hSfin : ν S < ∞)
    (hunivfin : ν Set.univ < ∞)
    (hp : 0 < p) (hρ : 0 < ρ) (hρR : ρ < R)
    (hCA : 0 < CA) :
    0 < anchorTailAveragedConstant ν S p ρ R CA ∧
      anchorTailAveragedConstant ν S p ρ R CA < ∞ := by
  have hscale :=
    anchorTailScaleConstant_pos_and_lt_top
      ν S hSpos hSfin hunivfin hp hρ hρR
  unfold anchorTailAveragedConstant
  constructor
  · exact ENNReal.mul_pos hscale.1.ne'
      (ENNReal.ofReal_ne_zero_iff.2 hCA)
  · exact ENNReal.mul_lt_top hscale.2
      ENNReal.ofReal_ne_top.lt_top

/--
Existential packaging of the complete structural comparison with the averaged
energy.  The witness is the explicit `anchorTailAveragedConstant`.
-/
theorem exists_finite_anchorTail_averaged_comparison_constant
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    (S : Set X) {α s cA CA ρ R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ)
    (hSpos : 0 < ν S) (hSfin : ν S < ∞)
    (hunivfin : ν Set.univ < ∞)
    (hp : 0 < α + 2 * s) (hρ : 0 < ρ) (hρR : ρ < R)
    (hCA : 0 < CA) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧
      globalVariation ν u ≤ C * averagedEnergy ν s R u := by
  let C :=
    anchorTailAveragedConstant ν S (α + 2 * s) ρ R CA
  have hC :
      0 < C ∧ C < ∞ :=
    anchorTailAveragedConstant_pos_and_lt_top
      ν S hSpos hSfin hunivfin hp hρ hρR hCA
  refine ⟨C, hC.1, hC.2, ?_⟩
  exact
    globalVariation_le_anchorTailAveragedConstant_mul_averagedEnergy
      ν hu S hreg hanchor hSpos hSfin hp hρ hρR hCA

end BesovVerification
