import BesovVerification.CoreLemmas
import BesovVerification.EnergyIdentity

/-!
# Recovering one local scale from the scale integral

This file formalizes the monotonicity argument on a terminal scale interval.
It is the analytic half of the long-distance estimate: once geometry bounds
the global oscillation by `localEnergy ν u ρ`, this result bounds that local
energy by the complete scale energy.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/--
If almost every pair lies in the open `ρ`-ball, then the local energy at `ρ`
is exactly the global oscillation.
-/
theorem localEnergy_eq_globalVariation_of_ae_mem_ball
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) (u : X → ℝ) {ρ : ℝ}
    (hcover : ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, y ∈ Metric.ball x ρ) :
    localEnergy ν u ρ = globalVariation ν u := by
  unfold localEnergy ballEnergy globalVariation
  apply lintegral_congr_ae
  filter_upwards [hcover] with x hx
  rw [← MeasureTheory.lintegral_indicator measurableSet_ball]
  apply lintegral_congr_ae
  filter_upwards [hx] with y hy
  simp [Set.indicator, hy]

/--
The mass of the scale weight on `(ρ,R]`, multiplied by the local energy at
`ρ`, is bounded by the complete scale energy.
-/
theorem scaleTailMass_mul_localEnergy_le
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) {u : X → ℝ}
    {p ρ R : ℝ} (hp : 0 < p) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    ENNReal.ofReal ((ρ ^ (-p) - R ^ (-p)) / p) *
        localEnergy ν u ρ ≤
      pScaleEnergy ν p R u := by
  have hweight :
      Measurable
        (fun r : ℝ => (ENNReal.ofReal r).rpow (-1 - p)) :=
    (ENNReal.continuous_rpow_const (y := -1 - p)).measurable.comp
      ENNReal.measurable_ofReal
  have hindicator :
      Measurable
        ((Set.Ioi ρ).indicator
          (fun r : ℝ => (ENNReal.ofReal r).rpow (-1 - p))) :=
    hweight.indicator measurableSet_Ioi
  rw [← lintegral_scale_indicator hp hρ hρR,
    ← lintegral_mul_const (localEnergy ν u ρ) hindicator]
  unfold pScaleEnergy
  apply lintegral_mono
  intro r
  change
    (Set.Ioi ρ).indicator
        (fun q : ℝ => (ENNReal.ofReal q).rpow (-1 - p)) r *
          localEnergy ν u ρ ≤
      (ENNReal.ofReal r).rpow (-1 - p) * localEnergy ν u r
  by_cases hr : r ∈ Set.Ioi ρ
  · rw [Set.indicator_of_mem hr]
    exact mul_le_mul_right (localEnergy_mono ν u hr.le) _
  · simp [Set.indicator, hr]

/--
When `ρ < R`, the terminal scale interval has positive finite weight.  Hence a
single local energy is bounded by an explicit structural multiple of the scale
energy.
-/
theorem localEnergy_le_inv_scaleTailMass_mul
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) {u : X → ℝ}
    {p ρ R : ℝ} (hp : 0 < p) (hρ : 0 < ρ) (hρR : ρ < R) :
    localEnergy ν u ρ ≤
      (ENNReal.ofReal ((ρ ^ (-p) - R ^ (-p)) / p))⁻¹ *
        pScaleEnergy ν p R u := by
  let K : ℝ≥0∞ :=
    ENNReal.ofReal ((ρ ^ (-p) - R ^ (-p)) / p)
  have hpow :
      R ^ (-p) < ρ ^ (-p) :=
    Real.rpow_lt_rpow_of_neg hρ hρR (neg_neg_of_pos hp)
  have hKpos : 0 < K := by
    exact ENNReal.ofReal_pos.2 (div_pos (sub_pos.2 hpow) hp)
  have hK0 : K ≠ 0 := hKpos.ne'
  have hKtop : K ≠ ∞ := ENNReal.ofReal_ne_top
  have hmul :
      K * localEnergy ν u ρ ≤ pScaleEnergy ν p R u :=
    scaleTailMass_mul_localEnergy_le ν hp hρ hρR.le
  calc
    localEnergy ν u ρ =
        K⁻¹ * (K * localEnergy ν u ρ) := by
          symm
          exact ENNReal.inv_mul_cancel_left hK0 hKtop
    _ ≤ K⁻¹ * pScaleEnergy ν p R u :=
      mul_le_mul_right hmul _

/-- The same estimate in the original `scaleEnergy` parameters. -/
theorem localEnergy_le_inv_scaleTailMass_mul_scaleEnergy
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) {u : X → ℝ}
    {α s ρ R : ℝ} (hp : 0 < α + 2 * s)
    (hρ : 0 < ρ) (hρR : ρ < R) :
    localEnergy ν u ρ ≤
      (ENNReal.ofReal
        ((ρ ^ (-(α + 2 * s)) - R ^ (-(α + 2 * s))) /
          (α + 2 * s)))⁻¹ *
        scaleEnergy ν α s R u := by
  rw [scaleEnergy_eq_pScaleEnergy]
  exact localEnergy_le_inv_scaleTailMass_mul ν hp hρ hρR

end BesovVerification
