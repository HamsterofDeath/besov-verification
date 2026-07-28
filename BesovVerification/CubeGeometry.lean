import BesovVerification.Ahlfors

/-!
# Elementary unit-cube geometry

The exact-diameter endpoint is delicate for open balls.  The lemmas here also
provide the strict containment needed when a cutoff is chosen larger than the
Euclidean cube diameter.
-/

open MeasureTheory Set

noncomputable section

namespace BesovVerification

/-- Any two points of `[0,1]^d` are at distance at most `sqrt d`. -/
theorem dist_le_sqrt_nat_of_mem_unitCube
    {d : ℕ} {x y : Ambient d}
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) :
    dist x y ≤ Real.sqrt d := by
  rw [EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  calc
    ∑ i : Fin d, dist (x i) (y i) ^ 2 ≤
        ∑ _i : Fin d, (1 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact pow_le_pow_left₀ dist_nonneg
        (Real.dist_le_of_mem_Icc_01 (hx i) (hy i)) 2
    _ = (d : ℝ) := by simp

/--
If the measure support lies in the cube and `ρ > sqrt d`, then almost every
pair lies in the corresponding open ball.
-/
theorem ae_pair_mem_ball_of_unitCube_support
    {d : ℕ} (ν : Measure (Ambient d))
    (hsupport : Measure.support ν ⊆ unitCube d)
    {ρ : ℝ} (hρ : Real.sqrt d < ρ) :
    ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, y ∈ Metric.ball x ρ := by
  filter_upwards [Measure.support_mem_ae] with x hx
  filter_upwards [Measure.support_mem_ae] with y hy
  exact Metric.mem_ball.mpr
    ((dist_le_sqrt_nat_of_mem_unitCube
      (hsupport hy) (hsupport hx)).trans_lt hρ)

/--
For a cutoff strictly larger than the cube diameter, the upper Ahlfors bound
at that cutoff makes the entire measure finite.  Thus `SFinite` need not be an
extra assumption in the cube specialization with a wide cutoff.
-/
theorem isFiniteMeasure_of_ahlfors_unitCube
    {d : ℕ} (ν : Measure (Ambient d))
    {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hsupport : Measure.support ν ⊆ unitCube d)
    (hR : Real.sqrt d < R) :
    IsFiniteMeasure ν := by
  by_cases hν : ν = 0
  · subst ν
    infer_instance
  obtain ⟨x, hx⟩ := Measure.nonempty_support hν
  have hRpos : 0 < R := (Real.sqrt_nonneg d).trans_lt hR
  have hball : ∀ᵐ y ∂ν, y ∈ Metric.ball x R := by
    filter_upwards [Measure.support_mem_ae] with y hy
    exact Metric.mem_ball.mpr
      ((dist_le_sqrt_nat_of_mem_unitCube
        (hsupport hy) (hsupport hx)).trans_lt hR)
  refine ⟨?_⟩
  calc
    ν Set.univ ≤ ν (Metric.ball x R) := by
      apply measure_mono_ae
      filter_upwards [hball] with y hy
      exact fun _hyuniv => hy
    _ ≤ ENNReal.ofReal (CA * R ^ α) :=
      hreg.upper x hx R hRpos le_rfl
    _ < ⊤ := by finiteness

end BesovVerification
