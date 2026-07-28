import BesovVerification.Definitions

/-!
# Consequences of the Ahlfors bounds

The principal result in this file is the atomlessness consequence requested
in the handover.  It uses the upper estimate only at radii at most `R`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace BesovVerification

/--
An upper Ahlfors estimate with positive exponent forces every supported point
to have zero singleton mass.
-/
theorem measure_singleton_eq_zero_of_upper_ahlfors
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (α CA R : ℝ)
    (hα : 0 < α) (hCA : 0 ≤ CA) (hR : 0 < R)
    (hupper :
      ∀ x ∈ Measure.support ν, ∀ r : ℝ, 0 < r → r ≤ R →
        ν (Metric.ball x r) ≤ ENNReal.ofReal (CA * r ^ α))
    {x : X} (hx : x ∈ Measure.support ν) :
    ν {x} = 0 := by
  have hpow :
      Tendsto (fun r : ℝ => r ^ α) (𝓝 0) (𝓝 0) := by
    have hc :
        Tendsto (fun r : ℝ => r ^ α) (𝓝 0) (𝓝 ((0 : ℝ) ^ α)) :=
      Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
    simpa only [Real.zero_rpow hα.ne'] using hc
  have hscaled :
      Tendsto (fun r : ℝ => CA * r ^ α) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow)
  by_contra hzero
  have hfinite : ν {x} ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact
      (measure_mono
        ((singleton_subset_iff).2 (Metric.mem_ball_self hR))).trans
        (hupper x hx R hR le_rfl)
  have hmass : 0 < (ν {x}).toReal :=
    ENNReal.toReal_pos hzero hfinite
  have hsmall_nhds :
      ∀ᶠ r : ℝ in 𝓝 0, CA * r ^ α < (ν {x}).toReal :=
    hscaled.eventually (Iio_mem_nhds hmass)
  have hsmall :
      ∀ᶠ r : ℝ in 𝓝[>] 0, CA * r ^ α < (ν {x}).toReal :=
    hsmall_nhds.filter_mono inf_le_left
  have hbelowR_nhds : ∀ᶠ r : ℝ in 𝓝 0, r < R :=
    Iio_mem_nhds hR
  have hbelowR : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R :=
    hbelowR_nhds.filter_mono inf_le_left
  have hpositive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0
    exact self_mem_nhdsWithin
  have hexists :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        CA * r ^ α < (ν {x}).toReal ∧ r < R ∧ 0 < r := by
    filter_upwards [hsmall, hbelowR, hpositive] with r hr hrR hr0
    exact ⟨hr, hrR, hr0⟩
  obtain ⟨r, hrsmall, hrR, hr0⟩ := hexists.exists
  have hsingleton_ball : ν {x} ≤ ν (Metric.ball x r) :=
    measure_mono ((singleton_subset_iff).2 (Metric.mem_ball_self hr0))
  have hmeasure :
      ν {x} ≤ ENNReal.ofReal (CA * r ^ α) :=
    hsingleton_ball.trans (hupper x hx r hr0 hrR.le)
  have hnonneg : 0 ≤ CA * r ^ α :=
    mul_nonneg hCA (Real.rpow_nonneg hr0.le α)
  have hreal :
      (ν {x}).toReal ≤ CA * r ^ α := by
    simpa [ENNReal.toReal_ofReal hnonneg] using
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure)
  exact (not_lt_of_ge hreal) hrsmall

/-- The preceding result specialized to the bundled Ahlfors predicate. -/
theorem AhlforsRegular.measure_singleton_eq_zero
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {ν : Measure X} {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hα : 0 < α) (hCA : 0 ≤ CA) (hR : 0 < R)
    {x : X} (hx : x ∈ Measure.support ν) :
    ν {x} = 0 :=
  measure_singleton_eq_zero_of_upper_ahlfors
    ν α CA R hα hCA hR hreg.upper hx

end BesovVerification
