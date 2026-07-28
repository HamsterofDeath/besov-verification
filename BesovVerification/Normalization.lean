import BesovVerification.Ahlfors
import BesovVerification.Measurability

/-!
# Comparison with the unnormalised local energy

The two lemmas here are the fixed-scale pointwise-integral comparison required
for the normalization step.  They use the conullity of the measure support and
do not assume the Ahlfors estimates away from the support.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- Algebraic separation of the Ahlfors constant from the scale power. -/
theorem normalization_weight_identity
    {C r α s : ℝ} (hC : 0 < C) (hr : 0 < r) :
    (ENNReal.ofReal r).rpow (-1 - 2 * s) *
        (ENNReal.ofReal (C * r ^ α))⁻¹ =
      (ENNReal.ofReal C)⁻¹ *
        (ENNReal.ofReal r).rpow (-1 - α - 2 * s) := by
  have hC0 : ENNReal.ofReal C ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 hC
  have hCt : ENNReal.ofReal C ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hr0 : ENNReal.ofReal r ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 hr
  have hrt : ENNReal.ofReal r ≠ ∞ :=
    ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_rpow_of_pos hr,
    ENNReal.mul_inv (Or.inl hC0) (Or.inl hCt), ← ENNReal.rpow_neg]
  calc
    (ENNReal.ofReal r).rpow (-1 - 2 * s) *
        ((ENNReal.ofReal C)⁻¹ * (ENNReal.ofReal r).rpow (-α)) =
      (ENNReal.ofReal C)⁻¹ *
        ((ENNReal.ofReal r).rpow (-1 - 2 * s) *
          (ENNReal.ofReal r).rpow (-α)) := by ac_rfl
    _ = (ENNReal.ofReal C)⁻¹ *
        (ENNReal.ofReal r).rpow ((-1 - 2 * s) + (-α)) := by
          congr 1
          exact
            (ENNReal.rpow_add (-1 - 2 * s) (-α) hr0 hrt).symm
    _ = (ENNReal.ofReal C)⁻¹ *
        (ENNReal.ofReal r).rpow (-1 - α - 2 * s) := by
          congr 2
          ring

theorem normalizedLocalEnergy_lower
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {α cA CA R r : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hr : 0 < r) (hrR : r ≤ R) :
    (ENNReal.ofReal (CA * r ^ α))⁻¹ * localEnergy ν u r ≤
      normalizedLocalEnergy ν u r := by
  have hmeas : Measurable (ballEnergy ν u r) := by
    change Measurable
      (fun x => ∫⁻ y in Metric.ball x r, differenceSq u x y ∂ν)
    exact measurable_ballEnergy ν hu r
  rw [localEnergy, normalizedLocalEnergy, ← lintegral_const_mul _ hmeas]
  apply lintegral_mono_ae
  filter_upwards [Measure.support_mem_ae] with x hx
  exact mul_le_mul_left
    ((ENNReal.inv_le_inv).2 (hreg.upper x hx r hr hrR))
    (ballEnergy ν u r x)

theorem normalizedLocalEnergy_upper
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {α cA CA R r : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hr : 0 < r) (hrR : r ≤ R) :
    normalizedLocalEnergy ν u r ≤
      (ENNReal.ofReal (cA * r ^ α))⁻¹ * localEnergy ν u r := by
  have hmeas : Measurable (ballEnergy ν u r) := by
    change Measurable
      (fun x => ∫⁻ y in Metric.ball x r, differenceSq u x y ∂ν)
    exact measurable_ballEnergy ν hu r
  rw [localEnergy, normalizedLocalEnergy, ← lintegral_const_mul _ hmeas]
  apply lintegral_mono_ae
  filter_upwards [Measure.support_mem_ae] with x hx
  exact mul_le_mul_left
    ((ENNReal.inv_le_inv).2 (hreg.lower x hx r hr hrR))
    (ballEnergy ν u r x)

/--
The scale-integrated normalization comparison.  This is Lemma 2 from the
handover, with explicit positive Ahlfors constants.
-/
theorem normalization_comparison
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hcA : 0 < cA) (hCA : 0 < CA) :
    (ENNReal.ofReal CA)⁻¹ * scaleEnergy ν α s R u ≤
        averagedEnergy ν s R u ∧
      averagedEnergy ν s R u ≤
        (ENNReal.ofReal cA)⁻¹ * scaleEnergy ν α s R u := by
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
  constructor
  · rw [scaleEnergy, averagedEnergy,
      ← lintegral_const_mul _ hscale]
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
  · rw [scaleEnergy, averagedEnergy,
      ← lintegral_const_mul _ hscale]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hnorm :=
      normalizedLocalEnergy_upper ν hu hreg hr.1 hr.2
    calc
      (ENNReal.ofReal r).rpow (-1 - 2 * s) *
          normalizedLocalEnergy ν u r ≤
          (ENNReal.ofReal r).rpow (-1 - 2 * s) *
            ((ENNReal.ofReal (cA * r ^ α))⁻¹ *
              localEnergy ν u r) := mul_le_mul_right hnorm _
      _ = (ENNReal.ofReal cA)⁻¹ *
          ((ENNReal.ofReal r).rpow (-1 - α - 2 * s) *
            localEnergy ν u r) := by
              calc
                (ENNReal.ofReal r).rpow (-1 - 2 * s) *
                    ((ENNReal.ofReal (cA * r ^ α))⁻¹ *
                      localEnergy ν u r) =
                  ((ENNReal.ofReal r).rpow (-1 - 2 * s) *
                    (ENNReal.ofReal (cA * r ^ α))⁻¹) *
                      localEnergy ν u r := by rw [← mul_assoc]
                _ = ((ENNReal.ofReal cA)⁻¹ *
                    (ENNReal.ofReal r).rpow (-1 - α - 2 * s)) *
                      localEnergy ν u r := by
                        rw [normalization_weight_identity hcA hr.1]
                _ = (ENNReal.ofReal cA)⁻¹ *
                    ((ENNReal.ofReal r).rpow (-1 - α - 2 * s) *
                      localEnergy ν u r) := by rw [mul_assoc]

end BesovVerification
