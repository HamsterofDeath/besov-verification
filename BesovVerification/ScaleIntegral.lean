import BesovVerification.Definitions

/-!
# The one-dimensional scale integral

This file proves the real-valued scalar identity underlying the Tonelli step.
The interval is bounded away from zero, so the negative real power is
integrable.
-/

open MeasureTheory Set
open scoped Interval ENNReal

noncomputable section

namespace BesovVerification

/--
For `p > 0` and `0 < t ≤ R`, integrating `r⁻¹⁻ᵖ` from `t` to `R` gives the
truncated singular kernel.
-/
theorem integral_scale_power
    {p t R : ℝ} (hp : 0 < p) (ht : 0 < t) (htR : t ≤ R) :
    (∫ r in Set.Ioc t R, r ^ (-1 - p)) =
      (t ^ (-p) - R ^ (-p)) / p := by
  rw [← intervalIntegral.integral_of_le htR]
  have hzero : (0 : ℝ) ∉ Set.uIcc t R := by
    rw [Set.uIcc_of_le htR]
    simp only [Set.mem_Icc, not_and_or]
    exact Or.inl (not_le_of_gt ht)
  rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
  have hp0 : p ≠ 0 := hp.ne'
  rw [show -1 - p + 1 = -p by ring]
  field_simp
  ring

/--
Indicator form of `integral_scale_power`, matching the scalar identity in the
handover.  The outer scale domain is `(0,R]`, and the indicator imposes
`t < r`.
-/
theorem integral_scale_indicator
    {p t R : ℝ} (hp : 0 < p) (ht : 0 < t) (htR : t ≤ R) :
    (∫ r in Set.Ioc 0 R,
      (Set.Ioi t).indicator (fun r : ℝ => r ^ (-1 - p)) r) =
      (t ^ (-p) - R ^ (-p)) / p := by
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  change
    (∫ r : ℝ,
      r ^ (-1 - p)
        ∂((volume.restrict (Set.Ioc 0 R)).restrict (Set.Ioi t))) =
      (t ^ (-p) - R ^ (-p)) / p
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hset : Set.Ioi t ∩ Set.Ioc 0 R = Set.Ioc t R := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, lt_trans ht h.1, h.2⟩
  rw [hset]
  exact integral_scale_power hp ht htR

/--
The same scalar identity as a nonnegative extended integral.  This is the form
used by Tonelli in the energy calculation.
-/
theorem lintegral_scale_indicator
    {p t R : ℝ} (hp : 0 < p) (ht : 0 < t) (htR : t ≤ R) :
    (∫⁻ r in Set.Ioc 0 R,
      (Set.Ioi t).indicator
        (fun r : ℝ => (ENNReal.ofReal r).rpow (-1 - p)) r) =
      ENNReal.ofReal ((t ^ (-p) - R ^ (-p)) / p) := by
  rw [MeasureTheory.lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have hset : Set.Ioi t ∩ Set.Ioc 0 R = Set.Ioc t R := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, lt_trans ht h.1, h.2⟩
  rw [hset]
  have hzero : (0 : ℝ) ∉ Set.uIcc t R := by
    rw [Set.uIcc_of_le htR]
    simp only [Set.mem_Icc, not_and_or]
    exact Or.inl (not_le_of_gt ht)
  have hint :
      Integrable (fun r : ℝ => r ^ (-1 - p))
        (volume.restrict (Set.Ioc t R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le htR).1
      (intervalIntegral.intervalIntegrable_rpow (Or.inr hzero))
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc t R)]
        (fun r : ℝ => r ^ (-1 - p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Real.rpow_nonneg (le_trans ht.le hr.1.le) _
  calc
    (∫⁻ r : ℝ in Set.Ioc t R,
        (ENNReal.ofReal r).rpow (-1 - p)) =
        ∫⁻ r : ℝ in Set.Ioc t R,
          ENNReal.ofReal (r ^ (-1 - p)) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
            exact ENNReal.ofReal_rpow_of_pos (lt_trans ht hr.1)
    _ = ENNReal.ofReal
        (∫ r : ℝ in Set.Ioc t R, r ^ (-1 - p)) := by
          exact (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal ((t ^ (-p) - R ^ (-p)) / p) := by
          rw [integral_scale_power hp ht htR]

end BesovVerification
