import BesovVerification.EnergyIdentity

/-!
# Full energy decomposition

The scale integral produces a kernel truncated at `R`.  This file compares
that kernel with the full singular kernel.  The missing tail is bounded by the
unweighted global variation, and the comparison is an exact identity whenever
the measure is almost everywhere supported in a set of diameter at most `R`.

All statements are in `ℝ≥0∞`; no subtraction of infinite energies occurs.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- On `0 < t ≤ R`, the singular kernel is exactly the truncated kernel plus its tail value. -/
theorem singularKernel_eq_truncated_add
    {p R t : ℝ} (hp : 0 < p) (hR : 0 < R)
    (ht : 0 < t) (htR : t ≤ R) :
    (ENNReal.ofReal t).rpow (-p) =
      ENNReal.ofReal p * truncatedScaleKernel p R t +
        (ENNReal.ofReal R).rpow (-p) := by
  have htconv :
      (ENNReal.ofReal t).rpow (-p) = ENNReal.ofReal (t ^ (-p)) := by
    exact ENNReal.ofReal_rpow_of_pos ht
  have hRconv :
      (ENNReal.ofReal R).rpow (-p) = ENNReal.ofReal (R ^ (-p)) := by
    exact ENNReal.ofReal_rpow_of_pos hR
  rw [htconv, hRconv]
  rw [truncatedScaleKernel]
  simp only [ht, htR, and_self, if_pos]
  have hRp : 0 ≤ R ^ (-p) := Real.rpow_nonneg hR.le _
  have hmono : R ^ (-p) ≤ t ^ (-p) := by
    exact Real.rpow_le_rpow_of_nonpos ht htR (by linarith)
  rw [ENNReal.ofReal_div_of_pos hp]
  rw [ENNReal.mul_div_cancel (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top]
  rw [ENNReal.ofReal_sub _ hRp]
  exact (tsub_add_cancel_of_le (ENNReal.ofReal_le_ofReal hmono)).symm

/-- At every positive distance, the full singular kernel is bounded by the truncated part plus
the constant tail value `R⁻ᵖ`. -/
theorem singularKernel_le_truncated_add
    {p R t : ℝ} (hp : 0 < p) (hR : 0 < R) (ht : 0 < t) :
    (ENNReal.ofReal t).rpow (-p) ≤
      ENNReal.ofReal p * truncatedScaleKernel p R t +
        (ENNReal.ofReal R).rpow (-p) := by
  by_cases htR : t ≤ R
  · exact (singularKernel_eq_truncated_add hp hR ht htR).le
  · have hRt : R < t := lt_of_not_ge htR
    have htconv :
        (ENNReal.ofReal t).rpow (-p) = ENNReal.ofReal (t ^ (-p)) := by
      exact ENNReal.ofReal_rpow_of_pos ht
    have hRconv :
        (ENNReal.ofReal R).rpow (-p) = ENNReal.ofReal (R ^ (-p)) := by
      exact ENNReal.ofReal_rpow_of_pos hR
    rw [htconv, hRconv]
    have hpow : t ^ (-p) ≤ R ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos hR hRt.le (by linarith)
    simpa [truncatedScaleKernel, ht, htR] using
      (ENNReal.ofReal_le_ofReal hpow)

/-- The exact truncated scale kernel is measurable when its exponent is positive. -/
theorem measurable_truncatedScaleKernel
    {p R : ℝ} (hp : 0 < p) :
    Measurable (truncatedScaleKernel p R) := by
  let k : ℝ → ℝ≥0∞ := fun t =>
    if 0 < t ∧ t ≤ R then
      ((ENNReal.ofReal t).rpow (-p) -
        (ENNReal.ofReal R).rpow (-p)) / ENNReal.ofReal p
    else 0
  have hk : Measurable k := by
    dsimp only [k]
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_le measurable_id measurable_const)
    · have hm :
          Measurable (fun t : ℝ => (ENNReal.ofReal t).rpow (-p)) :=
        (ENNReal.continuous_rpow_const (y := -p)).measurable.comp
          ENNReal.measurable_ofReal
      exact (hm.sub measurable_const).div measurable_const
    · exact measurable_const
  have heq : truncatedScaleKernel p R = k := by
    funext t
    unfold truncatedScaleKernel
    dsimp only [k]
    split_ifs with h
    · have ht : 0 < t := h.1
      have hR : 0 < R := lt_of_lt_of_le ht h.2
      rw [ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_sub _
        (Real.rpow_nonneg hR.le _)]
      have htconv :
          (ENNReal.ofReal t).rpow (-p) = ENNReal.ofReal (t ^ (-p)) := by
        exact ENNReal.ofReal_rpow_of_pos ht
      have hRconv :
          (ENNReal.ofReal R).rpow (-p) = ENNReal.ofReal (R ^ (-p)) := by
        exact ENNReal.ofReal_rpow_of_pos hR
      rw [← htconv, ← hRconv]
    · rfl
  rw [heq]
  exact hk

/-- The full singular energy is bounded by the truncated energy and the global variation tail.
This estimate does not require a diameter bound. -/
theorem besovEnergy_le_truncated_add_globalVariation
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {p R : ℝ} (hp : 0 < p) (hR : 0 < R) :
    besovEnergy ν p 0 u ≤
      ENNReal.ofReal p * truncatedEnergy ν p R u +
        (ENNReal.ofReal R).rpow (-p) * globalVariation ν u := by
  let tk : X × X → ℝ≥0∞ := fun q =>
    truncatedScaleKernel p R (dist q.1 q.2) *
      differenceSq u q.1 q.2
  let dv : X × X → ℝ≥0∞ := fun q =>
    differenceSq u q.1 q.2
  have htk : Measurable tk := by
    apply Measurable.mul
    · exact (measurable_truncatedScaleKernel hp).comp measurable_dist
    · exact measurable_differenceSq_uncurry hu
  have hdv : Measurable dv :=
    measurable_differenceSq_uncurry hu
  have htkInner : Measurable (fun x => ∫⁻ y, tk (x, y) ∂ν) :=
    htk.lintegral_prod_right'
  have hdvInner : Measurable (fun x => ∫⁻ y, dv (x, y) ∂ν) :=
    hdv.lintegral_prod_right'
  calc
    besovEnergy ν p 0 u ≤
        ∫⁻ x, ∫⁻ y,
          ENNReal.ofReal p * tk (x, y) +
            (ENNReal.ofReal R).rpow (-p) * dv (x, y) ∂ν ∂ν := by
      unfold besovEnergy
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      dsimp only
      by_cases hxy : x = y
      · subst y
        simp [tk, dv, differenceSq]
      · have ht : 0 < dist x y := dist_pos.mpr hxy
        rw [if_neg hxy]
        have hexp : -(p + 2 * 0) = -p := by ring
        rw [hexp]
        calc
          differenceSq u x y *
              (ENNReal.ofReal (dist x y)).rpow (-p) ≤
              differenceSq u x y *
                (ENNReal.ofReal p *
                    truncatedScaleKernel p R (dist x y) +
                  (ENNReal.ofReal R).rpow (-p)) :=
            by
              gcongr
              exact singularKernel_le_truncated_add hp hR ht
          _ = ENNReal.ofReal p * tk (x, y) +
                (ENNReal.ofReal R).rpow (-p) * dv (x, y) := by
            simp only [tk, dv]
            rw [mul_add]
            ac_rfl
    _ = ∫⁻ x,
          ENNReal.ofReal p * (∫⁻ y, tk (x, y) ∂ν) +
            (ENNReal.ofReal R).rpow (-p) *
              (∫⁻ y, dv (x, y) ∂ν) ∂ν := by
      apply lintegral_congr
      intro x
      have htkx : Measurable (fun y => tk (x, y)) :=
        htk.comp (by fun_prop)
      have hdvx : Measurable (fun y => dv (x, y)) :=
        hdv.comp (by fun_prop)
      calc
        (∫⁻ y, ENNReal.ofReal p * tk (x, y) +
            (ENNReal.ofReal R).rpow (-p) * dv (x, y) ∂ν) =
            (∫⁻ y, ENNReal.ofReal p * tk (x, y) ∂ν) +
              (∫⁻ y, (ENNReal.ofReal R).rpow (-p) * dv (x, y) ∂ν) :=
          lintegral_add_left (measurable_const.mul htkx) _
        _ = ENNReal.ofReal p * (∫⁻ y, tk (x, y) ∂ν) +
              (ENNReal.ofReal R).rpow (-p) *
                (∫⁻ y, dv (x, y) ∂ν) := by
          rw [lintegral_const_mul _ htkx, lintegral_const_mul _ hdvx]
    _ = ENNReal.ofReal p * (∫⁻ x, ∫⁻ y, tk (x, y) ∂ν ∂ν) +
          (ENNReal.ofReal R).rpow (-p) *
            (∫⁻ x, ∫⁻ y, dv (x, y) ∂ν ∂ν) := by
      calc
        (∫⁻ x, ENNReal.ofReal p * (∫⁻ y, tk (x, y) ∂ν) +
            (ENNReal.ofReal R).rpow (-p) *
              (∫⁻ y, dv (x, y) ∂ν) ∂ν) =
            (∫⁻ x, ENNReal.ofReal p * (∫⁻ y, tk (x, y) ∂ν) ∂ν) +
              (∫⁻ x, (ENNReal.ofReal R).rpow (-p) *
                (∫⁻ y, dv (x, y) ∂ν) ∂ν) :=
          lintegral_add_left (measurable_const.mul htkInner) _
        _ = ENNReal.ofReal p * (∫⁻ x, ∫⁻ y, tk (x, y) ∂ν ∂ν) +
              (ENNReal.ofReal R).rpow (-p) *
                (∫⁻ x, ∫⁻ y, dv (x, y) ∂ν ∂ν) := by
          rw [lintegral_const_mul _ htkInner,
            lintegral_const_mul _ hdvInner]
    _ = ENNReal.ofReal p * truncatedEnergy ν p R u +
          (ENNReal.ofReal R).rpow (-p) * globalVariation ν u := by
      rfl

/-- The full-energy decomposition is exact when almost every pair is at distance at most `R`. -/
theorem besovEnergy_eq_truncated_add_globalVariation_ae
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {p R : ℝ} (hp : 0 < p) (hR : 0 < R)
    (hdiam : ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, dist x y ≤ R) :
    besovEnergy ν p 0 u =
      ENNReal.ofReal p * truncatedEnergy ν p R u +
        (ENNReal.ofReal R).rpow (-p) * globalVariation ν u := by
  let tk : X × X → ℝ≥0∞ := fun q =>
    truncatedScaleKernel p R (dist q.1 q.2) *
      differenceSq u q.1 q.2
  let dv : X × X → ℝ≥0∞ := fun q =>
    differenceSq u q.1 q.2
  have htk : Measurable tk := by
    apply Measurable.mul
    · exact (measurable_truncatedScaleKernel hp).comp measurable_dist
    · exact measurable_differenceSq_uncurry hu
  have hdv : Measurable dv :=
    measurable_differenceSq_uncurry hu
  have htkInner : Measurable (fun x => ∫⁻ y, tk (x, y) ∂ν) :=
    htk.lintegral_prod_right'
  have hdvInner : Measurable (fun x => ∫⁻ y, dv (x, y) ∂ν) :=
    hdv.lintegral_prod_right'
  calc
    besovEnergy ν p 0 u =
        ∫⁻ x, ∫⁻ y,
          ENNReal.ofReal p * tk (x, y) +
            (ENNReal.ofReal R).rpow (-p) * dv (x, y) ∂ν ∂ν := by
      unfold besovEnergy
      apply lintegral_congr_ae
      filter_upwards [hdiam] with x hx
      apply lintegral_congr_ae
      filter_upwards [hx] with y hy
      by_cases hxy : x = y
      · subst y
        simp [tk, dv, differenceSq]
      · have ht : 0 < dist x y := dist_pos.mpr hxy
        rw [if_neg hxy]
        have hexp : -(p + 2 * 0) = -p := by ring
        rw [hexp, singularKernel_eq_truncated_add hp hR ht hy]
        simp only [tk, dv]
        rw [mul_add]
        ac_rfl
    _ = ∫⁻ x,
          ENNReal.ofReal p * (∫⁻ y, tk (x, y) ∂ν) +
            (ENNReal.ofReal R).rpow (-p) *
              (∫⁻ y, dv (x, y) ∂ν) ∂ν := by
      apply lintegral_congr
      intro x
      have htkx : Measurable (fun y => tk (x, y)) :=
        htk.comp (by fun_prop)
      have hdvx : Measurable (fun y => dv (x, y)) :=
        hdv.comp (by fun_prop)
      calc
        (∫⁻ y, ENNReal.ofReal p * tk (x, y) +
            (ENNReal.ofReal R).rpow (-p) * dv (x, y) ∂ν) =
            (∫⁻ y, ENNReal.ofReal p * tk (x, y) ∂ν) +
              (∫⁻ y, (ENNReal.ofReal R).rpow (-p) * dv (x, y) ∂ν) :=
          lintegral_add_left (measurable_const.mul htkx) _
        _ = ENNReal.ofReal p * (∫⁻ y, tk (x, y) ∂ν) +
              (ENNReal.ofReal R).rpow (-p) *
                (∫⁻ y, dv (x, y) ∂ν) := by
          rw [lintegral_const_mul _ htkx, lintegral_const_mul _ hdvx]
    _ = ENNReal.ofReal p * (∫⁻ x, ∫⁻ y, tk (x, y) ∂ν ∂ν) +
          (ENNReal.ofReal R).rpow (-p) *
            (∫⁻ x, ∫⁻ y, dv (x, y) ∂ν ∂ν) := by
      calc
        (∫⁻ x, ENNReal.ofReal p * (∫⁻ y, tk (x, y) ∂ν) +
            (ENNReal.ofReal R).rpow (-p) *
              (∫⁻ y, dv (x, y) ∂ν) ∂ν) =
            (∫⁻ x, ENNReal.ofReal p * (∫⁻ y, tk (x, y) ∂ν) ∂ν) +
              (∫⁻ x, (ENNReal.ofReal R).rpow (-p) *
                (∫⁻ y, dv (x, y) ∂ν) ∂ν) :=
          lintegral_add_left (measurable_const.mul htkInner) _
        _ = ENNReal.ofReal p * (∫⁻ x, ∫⁻ y, tk (x, y) ∂ν ∂ν) +
              (ENNReal.ofReal R).rpow (-p) *
                (∫⁻ x, ∫⁻ y, dv (x, y) ∂ν ∂ν) := by
          rw [lintegral_const_mul _ htkInner,
            lintegral_const_mul _ hdvInner]
    _ = ENNReal.ofReal p * truncatedEnergy ν p R u +
          (ENNReal.ofReal R).rpow (-p) * globalVariation ν u := by
      rfl

/-- Support-diameter form of the exact full-energy decomposition. -/
theorem besovEnergy_eq_truncated_add_globalVariation_support
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {p R : ℝ} (hp : 0 < p) (hR : 0 < R)
    (hdiam :
      ∀ x ∈ Measure.support ν, ∀ y ∈ Measure.support ν, dist x y ≤ R) :
    besovEnergy ν p 0 u =
      ENNReal.ofReal p * truncatedEnergy ν p R u +
        (ENNReal.ofReal R).rpow (-p) * globalVariation ν u := by
  apply besovEnergy_eq_truncated_add_globalVariation_ae ν hu hp hR
  filter_upwards [Measure.support_mem_ae (μ := ν)] with x hx
  filter_upwards [Measure.support_mem_ae (μ := ν)] with y hy
  exact hdiam x hx y hy

/-- Any estimate of global variation by truncated energy closes the reverse Besov comparison. -/
theorem besovEnergy_le_truncated_of_globalVariation_le
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    {p R : ℝ} (hp : 0 < p) (hR : 0 < R)
    {G : ℝ≥0∞}
    (hglobal :
      globalVariation ν u ≤ G * truncatedEnergy ν p R u) :
    besovEnergy ν p 0 u ≤
      (ENNReal.ofReal p + (ENNReal.ofReal R).rpow (-p) * G) *
        truncatedEnergy ν p R u := by
  calc
    besovEnergy ν p 0 u ≤
        ENNReal.ofReal p * truncatedEnergy ν p R u +
          (ENNReal.ofReal R).rpow (-p) * globalVariation ν u :=
      besovEnergy_le_truncated_add_globalVariation ν hu hp hR
    _ ≤ ENNReal.ofReal p * truncatedEnergy ν p R u +
          (ENNReal.ofReal R).rpow (-p) *
            (G * truncatedEnergy ν p R u) := by
      gcongr
    _ = (ENNReal.ofReal p + (ENNReal.ofReal R).rpow (-p) * G) *
          truncatedEnergy ν p R u := by
      rw [add_mul]
      ac_rfl

end BesovVerification
