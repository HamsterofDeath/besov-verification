import BesovVerification.CoreLemmas
import BesovVerification.Measurability

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- The oscillation from a point to an anchor set. -/
def anchorEnergy {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (u : X → ℝ) (S : Set X) (x : X) : ℝ≥0∞ :=
  ∫⁻ z in S, differenceSq u x z ∂ν

theorem differenceSq_comm {X : Type*} (u : X → ℝ) (x y : X) :
    differenceSq u x y = differenceSq u y x := by
  unfold differenceSq
  congr 1
  ring

theorem measurable_anchorEnergy
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u) (S : Set X) :
    Measurable (anchorEnergy ν u S) := by
  exact
    (measurable_differenceSq_uncurry hu).lintegral_prod_right'
      (ν := ν.restrict S)

set_option maxHeartbeats 1000000 in
-- Elaborating the restricted-integral comparison exceeds the default heartbeat budget.
theorem anchor_mass_mul_differenceSq_le
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u) (S : Set X) (x y : X) :
    ν S * differenceSq u x y ≤
      2 * anchorEnergy ν u S x + 2 * anchorEnergy ν u S y := by
  have hD : Measurable (fun p : X × X => differenceSq u p.1 p.2) :=
    measurable_differenceSq_uncurry hu
  have hxz0 : Measurable (fun z => differenceSq u x z) :=
    hD.comp (Measurable.prodMk measurable_const measurable_id)
  have hzy0 : Measurable (fun z => differenceSq u z y) :=
    hD.comp (Measurable.prodMk measurable_id measurable_const)
  have hxz : Measurable (fun z => 2 * differenceSq u x z) :=
    measurable_const.mul hxz0
  calc
    ν S * differenceSq u x y =
        ∫⁻ _z in S, differenceSq u x y ∂ν := by
          rw [setLIntegral_const]
          exact mul_comm _ _
    _ ≤ ∫⁻ z in S,
          (2 * differenceSq u x z + 2 * differenceSq u z y) ∂ν := by
      apply lintegral_mono
      intro z
      exact differenceSq_triangle u x y z
    _ = (∫⁻ z in S, 2 * differenceSq u x z ∂ν) +
          ∫⁻ z in S, 2 * differenceSq u z y ∂ν := by
      exact lintegral_add_left hxz _
    _ = 2 * anchorEnergy ν u S x + 2 * anchorEnergy ν u S y := by
      unfold anchorEnergy
      rw [lintegral_const_mul 2 hxz0]
      rw [lintegral_const_mul 2 hzy0]
      congr 2
      apply lintegral_congr
      intro z
      exact differenceSq_comm u z y

theorem anchorEnergy_le_ballEnergy_ae
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (S : Set X) {ρ : ℝ}
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ) :
    ∀ᵐ x ∂ν, anchorEnergy ν u S x ≤ ballEnergy ν u ρ x := by
  filter_upwards [Measure.support_mem_ae] with x hx
  unfold anchorEnergy ballEnergy
  apply lintegral_mono'
  · apply Measure.restrict_mono_set
    intro z hz
    simpa only [Metric.mem_ball, dist_comm] using hanchor x hx z hz
  · exact le_rfl

theorem integral_anchorEnergy_le_localEnergy
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (S : Set X) {ρ : ℝ}
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ) :
    (∫⁻ x, anchorEnergy ν u S x ∂ν) ≤ localEnergy ν u ρ := by
  exact lintegral_mono_ae (anchorEnergy_le_ballEnergy_ae ν S hanchor)

set_option maxHeartbeats 1000000 in
-- Elaborating the nested `lintegral` rearrangement exceeds the default heartbeat budget.
theorem anchor_mass_mul_globalVariation_le
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    (S : Set X) {ρ : ℝ}
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ) :
    ν S * globalVariation ν u ≤
      4 * ν Set.univ * localEnergy ν u ρ := by
  let A : X → ℝ≥0∞ := anchorEnergy ν u S
  have hA : Measurable A := measurable_anchorEnergy ν hu S
  have hD : Measurable (fun p : X × X => differenceSq u p.1 p.2) :=
    measurable_differenceSq_uncurry hu
  have hDinner : Measurable (fun x => ∫⁻ y, differenceSq u x y ∂ν) :=
    hD.lintegral_prod_right'
  have hpoint :
      ∀ x y, ν S * differenceSq u x y ≤ 2 * A x + 2 * A y :=
    anchor_mass_mul_differenceSq_le ν hu S
  have hIA :
      (∫⁻ x, A x ∂ν) ≤ localEnergy ν u ρ := by
    exact integral_anchorEnergy_le_localEnergy ν S hanchor
  calc
    ν S * globalVariation ν u =
        ∫⁻ x, ν S * (∫⁻ y, differenceSq u x y ∂ν) ∂ν := by
      unfold globalVariation
      rw [lintegral_const_mul _ hDinner]
    _ = ∫⁻ x, ∫⁻ y, ν S * differenceSq u x y ∂ν ∂ν := by
      apply lintegral_congr
      intro x
      have hDx : Measurable (fun y => differenceSq u x y) :=
        hD.comp (Measurable.prodMk measurable_const measurable_id)
      rw [lintegral_const_mul _ hDx]
    _ ≤ ∫⁻ x, ∫⁻ y, (2 * A x + 2 * A y) ∂ν ∂ν := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      exact hpoint x y
    _ = ∫⁻ x,
          ((2 * A x) * ν Set.univ + 2 * (∫⁻ y, A y ∂ν)) ∂ν := by
      apply lintegral_congr
      intro x
      rw [lintegral_add_left measurable_const]
      rw [lintegral_const]
      rw [lintegral_const_mul 2 hA]
    _ = 4 * ν Set.univ * (∫⁻ x, A x ∂ν) := by
      have htwoA : Measurable (fun x => 2 * A x) :=
        measurable_const.mul hA
      have hfirst : Measurable (fun x => (2 * A x) * ν Set.univ) :=
        htwoA.mul measurable_const
      rw [lintegral_add_left hfirst]
      rw [lintegral_mul_const _ htwoA]
      rw [lintegral_const_mul 2 hA]
      rw [lintegral_const]
      ring
    _ ≤ 4 * ν Set.univ * localEnergy ν u ρ := by
      exact mul_le_mul_right hIA _

/--
After cancelling the positive finite anchor mass, the global oscillation is
controlled by one local energy.  The coefficient is the total-to-anchor mass
ratio, with the universal factor `4` from the squared triangle inequality.
-/
theorem globalVariation_le_anchor_localEnergy
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    (S : Set X) {ρ : ℝ}
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ)
    (hSpos : 0 < ν S) (hSfin : ν S < ∞) :
    globalVariation ν u ≤
      (4 * ν Set.univ / ν S) * localEnergy ν u ρ := by
  have hmul :=
    anchor_mass_mul_globalVariation_le ν hu S hanchor
  have hquot :
      globalVariation ν u ≤
        (4 * ν Set.univ * localEnergy ν u ρ) / ν S := by
    apply
      (ENNReal.le_div_iff_mul_le
        (Or.inl hSpos.ne') (Or.inl hSfin.ne)).2
    simpa only [mul_comm] using hmul
  calc
    globalVariation ν u ≤
        (4 * ν Set.univ * localEnergy ν u ρ) / ν S := hquot
    _ = (4 * ν Set.univ / ν S) * localEnergy ν u ρ := by
      simp only [div_eq_mul_inv]
      ac_rfl

/--
With finite total mass and a positive finite anchor set, the structural
comparison has a positive finite constant.
-/
theorem exists_finite_anchor_comparison_constant
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {u : X → ℝ} (hu : Measurable u)
    (S : Set X) {ρ : ℝ}
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ)
    (hSpos : 0 < ν S) (hSfin : ν S < ∞)
    (hunivfin : ν Set.univ < ∞) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧
      globalVariation ν u ≤ C * localEnergy ν u ρ := by
  have hSuniv : ν S ≤ ν Set.univ :=
    measure_mono (Set.subset_univ S)
  have hunivpos : 0 < ν Set.univ :=
    hSpos.trans_le hSuniv
  have hnumpos : 0 < 4 * ν Set.univ :=
    ENNReal.mul_pos (by norm_num) hunivpos.ne'
  have hnumfin : 4 * ν Set.univ < ∞ :=
    ENNReal.mul_lt_top (by norm_num) hunivfin
  refine ⟨4 * ν Set.univ / ν S, ?_, ?_, ?_⟩
  · exact ENNReal.div_pos hnumpos.ne' hSfin.ne
  · exact ENNReal.div_lt_top hnumfin.ne hSpos.ne'
  · exact globalVariation_le_anchor_localEnergy ν hu S hanchor hSpos hSfin

end BesovVerification
