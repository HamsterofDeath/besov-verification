import BesovVerification.Ahlfors

/-!
# Cube support and anchor-point lemmas

This file isolates the geometric and measure-theoretic ingredients needed for
the missing long-range estimate.  In particular, it proves that the Ahlfors
upper estimate makes the measure locally finite, that cube-supported measures
are finite, and that a nonzero Ahlfors-regular measure has a supported point
which is not a cube corner.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace BesovVerification

/-- The `2^d` vertices of the coordinate cube, parametrized by Boolean vectors. -/
def cubeCorner (d : ℕ) (v : Fin d → Bool) : Ambient d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => if v i then 1 else 0)

/-- The finite set of vertices of the coordinate cube. -/
def cubeCorners (d : ℕ) : Set (Ambient d) :=
  Set.range (cubeCorner d)

/-- The union of radius-`δ` balls about all cube vertices. -/
def cornerNeighborhood (d : ℕ) (δ : ℝ) : Set (Ambient d) :=
  ⋃ v : Fin d → Bool, Metric.ball (cubeCorner d v) δ

theorem cubeCorners_countable (d : ℕ) : (cubeCorners d).Countable := by
  exact Set.countable_range (cubeCorner d)

theorem cubeCorner_apply (d : ℕ) (v : Fin d → Bool) (i : Fin d) :
    cubeCorner d v i = if v i then 1 else 0 := by
  simp [cubeCorner]

theorem cubeCorner_mem_unitCube (d : ℕ) (v : Fin d → Bool) :
    cubeCorner d v ∈ unitCube d := by
  intro i
  cases hvi : v i <;> simp [cubeCorner_apply, hvi]

theorem isOpen_cornerNeighborhood (d : ℕ) (δ : ℝ) :
    IsOpen (cornerNeighborhood d δ) := by
  exact isOpen_iUnion fun _ => Metric.isOpen_ball

/--
A ball centered at a cube vertex has the same Ahlfors upper bound, with
radius doubled, even when the vertex itself is not in the support.
-/
theorem measure_ball_cubeCorner_le
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA R δ : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hδ : 0 < δ) (h2δR : 2 * δ ≤ R)
    (v : Fin d → Bool) :
    ν (Metric.ball (cubeCorner d v) δ) ≤
      ENNReal.ofReal (CA * (2 * δ) ^ α) := by
  by_cases hzero : ν (Metric.ball (cubeCorner d v) δ) = 0
  · simp [hzero]
  · have hpos : 0 < ν (Metric.ball (cubeCorner d v) δ) :=
      bot_lt_iff_ne_bot.mpr hzero
    obtain ⟨q, hqBall, hqSupport⟩ :=
      Measure.nonempty_inter_support_of_pos hpos
    have hsubset :
        Metric.ball (cubeCorner d v) δ ⊆ Metric.ball q (2 * δ) := by
      intro y hy
      rw [Metric.mem_ball] at hy hqBall ⊢
      calc
        dist y q ≤ dist y (cubeCorner d v) +
            dist (cubeCorner d v) q :=
          dist_triangle y (cubeCorner d v) q
        _ < δ + δ := add_lt_add hy (by simpa [dist_comm] using hqBall)
        _ = 2 * δ := by ring
    exact
      (measure_mono hsubset).trans
        (hreg.upper q hqSupport (2 * δ) (by linarith) h2δR)

/-- The whole corner neighborhood is bounded by the sum of `2^d` upper estimates. -/
theorem measure_cornerNeighborhood_le
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA R δ : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hδ : 0 < δ) (h2δR : 2 * δ ≤ R) :
    ν (cornerNeighborhood d δ) ≤
      ∑ _v : Fin d → Bool,
        ENNReal.ofReal (CA * (2 * δ) ^ α) := by
  calc
    ν (cornerNeighborhood d δ)
        ≤ ∑ v : Fin d → Bool,
            ν (Metric.ball (cubeCorner d v) δ) := by
          exact measure_iUnion_fintype_le ν _
    _ ≤ ∑ _v : Fin d → Bool,
          ENNReal.ofReal (CA * (2 * δ) ^ α) :=
      Finset.sum_le_sum fun v _ =>
        measure_ball_cubeCorner_le hreg hδ h2δR v

/--
Positive structural Ahlfors constants always provide a sufficiently small
corner radius for which all `2^d` corner neighborhoods have total upper
bound below the radius-`R` lower bound.
-/
theorem exists_cornerScale
    (d : ℕ) {α cA CA R : ℝ}
    (hα : 0 < α) (hcA : 0 < cA) (hCA : 0 ≤ CA) (hR : 0 < R) :
    ∃ δ : ℝ,
      0 < δ ∧ 2 * δ ≤ R ∧
      (∑ _v : Fin d → Bool,
        ENNReal.ofReal (CA * (2 * δ) ^ α)) <
          ENNReal.ofReal (cA * R ^ α) := by
  have hpow :
      Tendsto (fun r : ℝ => r ^ α) (𝓝 0) (𝓝 0) := by
    have hc :
        Tendsto (fun r : ℝ => r ^ α) (𝓝 0) (𝓝 ((0 : ℝ) ^ α)) :=
      Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
    simpa only [Real.zero_rpow hα.ne'] using hc
  have htwo :
      Tendsto (fun δ : ℝ => 2 * δ) (𝓝 0) (𝓝 0) := by
    have hconst :
        Tendsto (fun _δ : ℝ => (2 : ℝ)) (𝓝 0) (𝓝 2) :=
      tendsto_const_nhds
    simpa using hconst.mul tendsto_id
  have hpowTwo :
      Tendsto (fun δ : ℝ => (2 * δ) ^ α) (𝓝 0) (𝓝 0) :=
    hpow.comp htwo
  have hsum :
      Tendsto
        (fun δ : ℝ =>
          ∑ _v : Fin d → Bool, CA * (2 * δ) ^ α)
        (𝓝 0) (𝓝 0) := by
    have hterm :
        Tendsto (fun δ : ℝ => CA * (2 * δ) ^ α)
          (𝓝 0) (𝓝 0) := by
      have hconst :
          Tendsto (fun _δ : ℝ => CA) (𝓝 0) (𝓝 CA) :=
        tendsto_const_nhds
      simpa using hconst.mul hpowTwo
    have hcard :
        Tendsto
          (fun δ : ℝ =>
            (Fintype.card (Fin d → Bool) : ℝ) *
              (CA * (2 * δ) ^ α))
          (𝓝 0) (𝓝 0) := by
      have hconst :
          Tendsto
            (fun _δ : ℝ => (Fintype.card (Fin d → Bool) : ℝ))
            (𝓝 0) (𝓝 (Fintype.card (Fin d → Bool) : ℝ)) :=
        tendsto_const_nhds
      simpa using hconst.mul hterm
    simpa [nsmul_eq_mul] using hcard
  have htarget : 0 < cA * R ^ α :=
    mul_pos hcA (Real.rpow_pos_of_pos hR α)
  have hsmallNhds :
      ∀ᶠ δ : ℝ in 𝓝 0,
        (∑ _v : Fin d → Bool, CA * (2 * δ) ^ α) <
          cA * R ^ α :=
    hsum.eventually (Iio_mem_nhds htarget)
  have hsmall :
      ∀ᶠ δ : ℝ in 𝓝[>] 0,
        (∑ _v : Fin d → Bool, CA * (2 * δ) ^ α) <
          cA * R ^ α :=
    hsmallNhds.filter_mono inf_le_left
  have hbelowNhds : ∀ᶠ δ : ℝ in 𝓝 0, δ < R / 2 :=
    Iio_mem_nhds (half_pos hR)
  have hbelow : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < R / 2 :=
    hbelowNhds.filter_mono inf_le_left
  have hpositive : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0
    exact self_mem_nhdsWithin
  have hall :
      ∀ᶠ δ : ℝ in 𝓝[>] 0,
        (∑ _v : Fin d → Bool, CA * (2 * δ) ^ α) <
            cA * R ^ α ∧
          δ < R / 2 ∧ 0 < δ := by
    filter_upwards [hsmall, hbelow, hpositive] with δ hδsmall hδR hδ
    exact ⟨hδsmall, hδR, hδ⟩
  obtain ⟨δ, hδsmall, hδR, hδ⟩ := hall.exists
  refine ⟨δ, hδ, by linarith, ?_⟩
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · exact (ENNReal.ofReal_lt_ofReal_iff htarget).2 hδsmall
  · intro _v _
    exact mul_nonneg hCA (Real.rpow_nonneg (by linarith) α)

/--
If the explicit sum of corner-ball upper bounds is smaller than one Ahlfors
lower bound at radius `R`, some supported point stays at least `δ` away from
every cube vertex.
-/
theorem exists_support_away_from_cubeCorners
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA R δ : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hR : 0 < R) (hδ : 0 < δ) (h2δR : 2 * δ ≤ R)
    (hν : ν ≠ 0)
    (hsmall :
      (∑ _v : Fin d → Bool,
        ENNReal.ofReal (CA * (2 * δ) ^ α)) <
          ENNReal.ofReal (cA * R ^ α)) :
    ∃ q ∈ Measure.support ν,
      ∀ v : Fin d → Bool, δ ≤ dist q (cubeCorner d v) := by
  obtain ⟨x, hxSupport⟩ := Measure.nonempty_support hν
  have hunivLower :
      ENNReal.ofReal (cA * R ^ α) ≤ ν Set.univ :=
    (hreg.lower x hxSupport R hR le_rfl).trans
      (measure_mono (subset_univ _))
  have hnear :
      ν (cornerNeighborhood d δ) < ν Set.univ :=
    (measure_cornerNeighborhood_le hreg hδ h2δR).trans_lt
      (hsmall.trans_le hunivLower)
  have hexists :
      ∃ q ∈ Measure.support ν, q ∉ cornerNeighborhood d δ := by
    by_contra h
    have hsupportNear :
        Measure.support ν ⊆ cornerNeighborhood d δ := by
      intro q hq
      by_contra hqNear
      exact h ⟨q, hq, hqNear⟩
    have hsupportMeasure :
        ν (Measure.support ν) = ν Set.univ := by
      simpa using
        (measure_inter_conull (μ := ν) (s := Set.univ)
          (t := Measure.support ν) Measure.measure_compl_support)
    have hunivNear : ν Set.univ ≤ ν (cornerNeighborhood d δ) := by
      rw [← hsupportMeasure]
      exact measure_mono hsupportNear
    exact (not_le_of_gt hnear) hunivNear
  obtain ⟨q, hqSupport, hqNear⟩ := hexists
  refine ⟨q, hqSupport, ?_⟩
  intro v
  apply not_lt.mp
  intro hdist
  apply hqNear
  exact Set.mem_iUnion.mpr
    ⟨v, Metric.mem_ball.mpr (by simpa [dist_comm] using hdist)⟩

/-- The coordinate cube is compact in its Euclidean metric. -/
theorem isCompact_unitCube (d : ℕ) : IsCompact (unitCube d) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hpi :
      IsCompact (Set.univ.pi fun _ : Fin d => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hpre :
      IsCompact (e ⁻¹' (Set.univ.pi fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
    e.toHomeomorph.isCompact_preimage.mpr hpi
  have heq :
      unitCube d =
        e ⁻¹' (Set.univ.pi fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp only [unitCube, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_univ_pi, Set.mem_Icc, e,
      PiLp.coe_continuousLinearEquiv]
  rwa [heq]

/--
The upper Ahlfors estimate at one positive radius gives a finite-measure
neighborhood of every point.  Outside the support a null neighborhood exists
by definition of support.
-/
theorem AhlforsRegular.finiteAt_nhds
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {ν : Measure X} {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R) (hR : 0 < R) :
    ∀ x : X, ν.FiniteAtFilter (𝓝 x) := by
  intro x
  by_cases hx : x ∈ Measure.support ν
  · refine ⟨Metric.ball x R, Metric.ball_mem_nhds x hR, ?_⟩
    exact
      (hreg.upper x hx R hR le_rfl).trans_lt
        ENNReal.ofReal_lt_top
  · obtain ⟨U, hU, hνU⟩ :=
      Measure.notMem_support_iff_exists.mp hx
    exact ⟨U, hU, by simp [hνU]⟩

/--
An Ahlfors-regular measure whose support is compact has finite total mass.
This packages the local upper bound into the finiteness hypothesis required by
Tonelli and related measure-theory results.
-/
theorem AhlforsRegular.measure_univ_lt_top_of_compact_support
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [HereditarilyLindelofSpace X]
    {ν : Measure X} {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R) (hR : 0 < R)
    (hcompact : IsCompact (Measure.support ν)) :
    ν Set.univ < ∞ := by
  have hsupport :
      ν (Measure.support ν) < ∞ :=
    hcompact.measure_lt_top_of_nhdsWithin fun x _ =>
      (hreg.finiteAt_nhds hR x).inf_of_left
  calc
    ν Set.univ = ν (Measure.support ν ∪ (Measure.support ν)ᶜ) := by simp
    _ ≤ ν (Measure.support ν) + ν (Measure.support ν)ᶜ := measure_union_le _ _
    _ = ν (Measure.support ν) := by simp
    _ < ∞ := hsupport

/-- Cube support specializes the preceding compact-support finiteness result. -/
theorem AhlforsRegular.measure_univ_lt_top_of_unitCube_support
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R) (hR : 0 < R)
    (hsupport : Measure.support ν ⊆ unitCube d) :
    ν Set.univ < ∞ := by
  apply hreg.measure_univ_lt_top_of_compact_support hR
  exact
    IsCompact.of_isClosed_subset
      (isCompact_unitCube d) Measure.isClosed_support hsupport

/-- The cube-support hypotheses produce Mathlib's finite-measure typeclass. -/
theorem AhlforsRegular.isFiniteMeasure_of_unitCube_support
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R) (hR : 0 < R)
    (hsupport : Measure.support ν ⊆ unitCube d) :
    IsFiniteMeasure ν :=
  ⟨hreg.measure_univ_lt_top_of_unitCube_support hR hsupport⟩

/-- In particular, no separate `SFinite ν` hypothesis is needed in the cube theorem. -/
theorem AhlforsRegular.sFinite_of_unitCube_support
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R) (hR : 0 < R)
    (hsupport : Measure.support ν ⊆ unitCube d) :
    SFinite ν := by
  letI : IsFiniteMeasure ν :=
    hreg.isFiniteMeasure_of_unitCube_support hR hsupport
  infer_instance

/--
The supported-point atomlessness theorem extends to all points: a point
outside the support lies in a null neighborhood.
-/
theorem AhlforsRegular.measure_singleton_eq_zero_everywhere
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {ν : Measure X} {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hα : 0 < α) (hCA : 0 ≤ CA) (hR : 0 < R)
    (x : X) :
    ν {x} = 0 := by
  by_cases hx : x ∈ Measure.support ν
  · exact hreg.measure_singleton_eq_zero hα hCA hR hx
  · obtain ⟨U, hU, hνU⟩ :=
      Measure.notMem_support_iff_exists.mp hx
    exact
      measure_mono_null
        ((singleton_subset_iff).2 (mem_of_mem_nhds hU)) hνU

/--
A nonzero Ahlfors-regular measure has a supported point which is not one of
the finitely many cube vertices.  This is the qualitative core of the
corner-avoidance construction.
-/
theorem exists_support_not_cubeCorner
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hα : 0 < α) (hCA : 0 ≤ CA) (hR : 0 < R)
    (hν : ν ≠ 0) :
    ∃ q ∈ Measure.support ν, q ∉ cubeCorners d := by
  letI : NullSingletonClass ν :=
    ⟨hreg.measure_singleton_eq_zero_everywhere hα hCA hR⟩
  have hcorners : ν (cubeCorners d) = 0 :=
    (cubeCorners_countable d).measure_zero ν
  by_contra h
  have hsupport : Measure.support ν ⊆ cubeCorners d := by
    intro q hq
    by_contra hqCorner
    exact h ⟨q, hq, hqCorner⟩
  have hsupport_zero : ν (Measure.support ν) = 0 :=
    measure_mono_null hsupport hcorners
  have huniv : ν Set.univ = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      ν Set.univ = ν (Measure.support ν ∪ (Measure.support ν)ᶜ) := by simp
      _ ≤ ν (Measure.support ν) + ν (Measure.support ν)ᶜ := measure_union_le _ _
      _ = 0 := by simp [hsupport_zero]
  exact hν (Measure.measure_univ_eq_zero.mp huniv)

/-- A cube point which is not a vertex has a genuinely interior coordinate. -/
theorem exists_interior_coordinate_of_not_cubeCorner
    {d : ℕ} {q : Ambient d}
    (hqCube : q ∈ unitCube d) (hqCorner : q ∉ cubeCorners d) :
    ∃ i : Fin d, 0 < q i ∧ q i < 1 := by
  have hendpoint :
      ∃ i : Fin d, q i ≠ 0 ∧ q i ≠ 1 := by
    by_contra h
    have h' : ∀ i : Fin d, q i = 0 ∨ q i = 1 := by
      intro i
      by_cases hi0 : q i = 0
      · exact Or.inl hi0
      · exact Or.inr (by
          by_contra hi1
          exact h ⟨i, hi0, hi1⟩)
    apply hqCorner
    let v : Fin d → Bool := fun i => if q i = 1 then true else false
    refine ⟨v, ?_⟩
    ext i
    rcases h' i with hi | hi
    · simp [cubeCorner_apply, v, hi]
    · simp [cubeCorner_apply, v, hi]
  obtain ⟨i, hi0, hi1⟩ := hendpoint
  exact
    ⟨i,
      lt_of_le_of_ne (hqCube i).1 (Ne.symm hi0),
      lt_of_le_of_ne (hqCube i).2 hi1⟩

/-- The squared Euclidean distance between two cube points is at most `d`. -/
theorem dist_sq_le_dim_of_mem_unitCube
    {d : ℕ} {x y : Ambient d}
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) :
    dist x y ^ 2 ≤ (d : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq]
  calc
    (∑ i, dist (x i) (y i) ^ 2) ≤ ∑ _i : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Real.dist_eq]
      have habs : |x i - y i| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [(hx i).1, (hy i).2]
        · linarith [(hx i).2, (hy i).1]
      exact
        (pow_le_pow_left₀ (abs_nonneg _) habs 2).trans_eq
          (by norm_num)
    _ = (d : ℝ) := by simp

/--
If a cube point is at least `δ > 0` from every vertex, then the entire cube
lies in the explicit ball of radius `√(d - δ²)`, which is strictly smaller
than the cube diameter `√d`.
-/
theorem subdiametral_radius_of_away_from_cubeCorners
    {d : ℕ} {q : Ambient d} {δ : ℝ}
    (hqCube : q ∈ unitCube d) (hδ : 0 < δ)
    (haway : ∀ v : Fin d → Bool, δ ≤ dist q (cubeCorner d v)) :
    0 ≤ Real.sqrt ((d : ℝ) - δ ^ 2) ∧
      Real.sqrt ((d : ℝ) - δ ^ 2) < Real.sqrt d ∧
      ∀ x ∈ unitCube d,
        dist x q ≤ Real.sqrt ((d : ℝ) - δ ^ 2) := by
  let v : Fin d → Bool :=
    fun j => if (2 : ℝ)⁻¹ < q j then true else false
  let a : Ambient d := cubeCorner d v
  have haCube : a ∈ unitCube d := cubeCorner_mem_unitCube d v
  have hδdist : δ ≤ dist q a := haway v
  have hδsq : δ ^ 2 ≤ dist q a ^ 2 :=
    pow_le_pow_left₀ hδ.le hδdist 2
  have hdistqa : dist q a ^ 2 ≤ (d : ℝ) :=
    dist_sq_le_dim_of_mem_unitCube hqCube haCube
  have hbase : 0 ≤ (d : ℝ) - δ ^ 2 := by linarith
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt hbase ?_, ?_⟩
  · nlinarith
  · intro x hxCube
    have hcoord :
        ∀ j : Fin d,
          dist (q j) (a j) ^ 2 + dist (x j) (q j) ^ 2 ≤ 1 := by
      intro j
      have hq0 := (hqCube j).1
      have hq1 := (hqCube j).2
      have hx0 := (hxCube j).1
      have hx1 := (hxCube j).2
      by_cases hj : (2 : ℝ)⁻¹ < q j
      · have haj : a j = 1 := by
          simp [a, v, cubeCorner_apply, hj]
        have habs : |x j - q j| ≤ q j := by
          rw [abs_le]
          constructor <;> linarith
        have hsq : (x j - q j) ^ 2 ≤ (q j) ^ 2 :=
          sq_le_sq.mpr (by simpa [abs_of_nonneg hq0] using habs)
        rw [haj, Real.dist_eq, Real.dist_eq]
        simp only [sq_abs]
        nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
      · have hqhalf : q j ≤ (2 : ℝ)⁻¹ := le_of_not_gt hj
        have haj : a j = 0 := by
          simp [a, v, cubeCorner_apply, hj]
        have habs : |x j - q j| ≤ 1 - q j := by
          rw [abs_le]
          constructor <;> linarith
        have hnonneg : 0 ≤ 1 - q j := sub_nonneg.mpr hq1
        have hsq : (x j - q j) ^ 2 ≤ (1 - q j) ^ 2 :=
          sq_le_sq.mpr (by simpa [abs_of_nonneg hnonneg] using habs)
        rw [haj, Real.dist_eq, Real.dist_eq]
        simp only [sq_abs]
        nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
    have hpairs :
        dist q a ^ 2 + dist x q ^ 2 ≤ (d : ℝ) := by
      rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
      calc
        (∑ j, dist (q j) (a j) ^ 2) +
              ∑ j, dist (x j) (q j) ^ 2
            = ∑ j, (dist (q j) (a j) ^ 2 +
                dist (x j) (q j) ^ 2) := by
              rw [Finset.sum_add_distrib]
        _ ≤ ∑ _j : Fin d, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => hcoord j
        _ = (d : ℝ) := by simp
    apply Real.le_sqrt_of_sq_le
    linarith

/--
Every non-vertex point `q` of the unit cube has an explicit radius strictly
below `√d` which contains the entire cube.

The proof uses one interior coordinate `i`.  In that coordinate the maximum
possible displacement is `M = max (q i) (1 - q i) < 1`; all remaining
coordinate displacements are at most one.
-/
theorem exists_subdiametral_radius_unitCube
    {d : ℕ} {q : Ambient d}
    (hqCube : q ∈ unitCube d) (hqCorner : q ∉ cubeCorners d) :
    ∃ ρ : ℝ,
      0 ≤ ρ ∧ ρ < Real.sqrt d ∧
      ∀ x ∈ unitCube d, dist x q ≤ ρ := by
  obtain ⟨i, hi0, hi1⟩ :=
    exists_interior_coordinate_of_not_cubeCorner hqCube hqCorner
  let M : ℝ := max (q i) (1 - q i)
  let B : ℝ := M ^ 2 + ((Finset.univ.erase i).card : ℝ)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact hi0.le.trans (le_max_left _ _)
  have hM1 : M < 1 := by
    dsimp [M]
    exact max_lt hi1 (by linarith)
  have hM_sq : M ^ 2 < 1 := by
    nlinarith [sq_nonneg M]
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hdpos : 0 < d := Fin.pos_iff_nonempty.mpr ⟨i⟩
  have hcard :
      ((Finset.univ.erase i).card : ℝ) = (d : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hdpos.ne')]
    simp
  have hBd : B < (d : ℝ) := by
    dsimp [B]
    rw [hcard]
    linarith
  refine ⟨Real.sqrt B, Real.sqrt_nonneg B,
    Real.sqrt_lt_sqrt hB0 hBd, ?_⟩
  intro x hxCube
  have hcoordOne :
      ∀ j : Fin d, |x j - q j| ≤ 1 := by
    intro j
    rw [abs_le]
    constructor
    · have hx0 := (hxCube j).1
      have hq1 := (hqCube j).2
      linarith
    · have hx1 := (hxCube j).2
      have hq0 := (hqCube j).1
      linarith
  have hcoordM : |x i - q i| ≤ M := by
    rw [abs_le]
    constructor
    · have hx0 := (hxCube i).1
      have hMq : q i ≤ M := le_max_left _ _
      linarith
    · have hx1 := (hxCube i).2
      have hMone : 1 - q i ≤ M := le_max_right _ _
      linarith
  have hspecial :
      dist (x i) (q i) ^ 2 ≤ M ^ 2 := by
    rw [Real.dist_eq]
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hM0] using hcoordM)
  have hother :
      ∀ j ∈ Finset.univ.erase i, dist (x j) (q j) ^ 2 ≤ 1 := by
    intro j hj
    rw [Real.dist_eq]
    have hjabs := hcoordOne j
    exact
      (pow_le_pow_left₀ (abs_nonneg _) hjabs 2).trans_eq
        (by norm_num)
  have hsum :
      (∑ j, dist (x j) (q j) ^ 2) ≤ B := by
    have hdecomp :
        (∑ j, dist (x j) (q j) ^ 2) =
          dist (x i) (q i) ^ 2 +
            ∑ j ∈ Finset.univ.erase i, dist (x j) (q j) ^ 2 := by
      rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [hdecomp]
    calc
      dist (x i) (q i) ^ 2 +
            ∑ j ∈ Finset.univ.erase i, dist (x j) (q j) ^ 2
          ≤ M ^ 2 + ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) :=
        add_le_add hspecial (Finset.sum_le_sum fun j hj => hother j hj)
      _ = B := by simp [B]
  apply Real.le_sqrt_of_sq_le
  rw [EuclideanSpace.dist_sq_eq]
  exact hsum

/--
Any supported point whose distance to the entire support is bounded by
`ρ < R` yields a measurable, positive-measure anchor ball.  The returned
constants are explicit:

* `ε = (R - ρ) / 2`,
* `λ = (R + ρ) / (2R)`.

Thus every supported `x` and every anchor `z` satisfy
`dist x z < λ R`, with `0 < λ < 1`.
-/
theorem exists_quantitative_anchor_ball_of_subdiametral_point
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [HereditarilyLindelofSpace X]
    {ν : Measure X} {α cA CA R ρ : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (_hα : 0 < α) (hcA : 0 < cA) (hR : 0 < R)
    {q : X} (hq : q ∈ Measure.support ν)
    (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (hsubdiameter :
      ∀ x ∈ Measure.support ν, dist x q ≤ ρ) :
    ∃ (S : Set X) (ε lam : ℝ),
      ε = (R - ρ) / 2 ∧
      lam = (R + ρ) / (2 * R) ∧
      MeasurableSet S ∧
      S ⊆ Measure.support ν ∧
      0 < ε ∧ ε ≤ R ∧
      ENNReal.ofReal (cA * ε ^ α) ≤ ν S ∧
      0 < ν S ∧
      0 < lam ∧ lam < 1 ∧
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < lam * R := by
  let ε : ℝ := (R - ρ) / 2
  let lam : ℝ := (R + ρ) / (2 * R)
  let S : Set X := Metric.ball q ε ∩ Measure.support ν
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hεR : ε ≤ R := by
    dsimp [ε]
    linarith
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hlamOne : lam < 1 := by
    dsimp [lam]
    rw [div_lt_one (by positivity : 0 < 2 * R)]
    linarith
  have hSmeas : MeasurableSet S :=
    measurableSet_ball.inter Measure.isClosed_support.measurableSet
  have hSsubset : S ⊆ Measure.support ν :=
    inter_subset_right
  have hSmeasure : ν S = ν (Metric.ball q ε) := by
    dsimp [S]
    exact measure_inter_conull Measure.measure_compl_support
  have hSlower :
      ENNReal.ofReal (cA * ε ^ α) ≤ ν S := by
    rw [hSmeasure]
    exact hreg.lower q hq ε hε hεR
  have hLowerPos :
      0 < ENNReal.ofReal (cA * ε ^ α) := by
    rw [ENNReal.ofReal_pos]
    exact mul_pos hcA (Real.rpow_pos_of_pos hε α)
  have hSpos : 0 < ν S :=
    hLowerPos.trans_le hSlower
  refine ⟨S, ε, lam, rfl, rfl, hSmeas, hSsubset, hε, hεR, hSlower, hSpos,
    hlam, hlamOne, ?_⟩
  intro x hx z hz
  have hzball : dist q z < ε := by
    simpa [dist_comm] using Metric.mem_ball.mp hz.1
  calc
    dist x z ≤ dist x q + dist q z := dist_triangle x q z
    _ < ρ + ε := add_lt_add_of_le_of_lt (hsubdiameter x hx) hzball
    _ = lam * R := by
      dsimp [ε, lam]
      field_simp
      ring

/--
The fully structural cube anchor theorem.

The scale `δ` is selected using only `d`, `α`, `cA`, `CA`, and `√d`.
Consequently the displayed formulas for `ε` and `lam` are independent of
the particular measure and of the function whose energy will later be
estimated.  Only the location of the measurable anchor set `S` depends on
the measure.
-/
theorem exists_structural_unitCube_anchor_ball
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA : ℝ}
    (hreg : AhlforsRegular ν α cA CA (Real.sqrt d))
    (hd : 0 < d)
    (hα : 0 < α) (hcA : 0 < cA) (hCA : 0 ≤ CA)
    (hν : ν ≠ 0)
    (hsupport : Measure.support ν ⊆ unitCube d) :
    ∃ (δ : ℝ) (S : Set (Ambient d)) (ε lam : ℝ),
      0 < δ ∧
      2 * δ ≤ Real.sqrt d ∧
      ε =
        (Real.sqrt d - Real.sqrt ((d : ℝ) - δ ^ 2)) / 2 ∧
      lam =
        (Real.sqrt d + Real.sqrt ((d : ℝ) - δ ^ 2)) /
          (2 * Real.sqrt d) ∧
      MeasurableSet S ∧
      S ⊆ Measure.support ν ∧
      0 < ε ∧ ε ≤ Real.sqrt d ∧
      ENNReal.ofReal (cA * ε ^ α) ≤ ν S ∧
      0 < ν S ∧
      0 < lam ∧ lam < 1 ∧
      ∀ x ∈ Measure.support ν, ∀ z ∈ S,
        dist x z < lam * Real.sqrt d := by
  have hR : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  obtain ⟨δ, hδ, h2δR, hδsmall⟩ :=
    exists_cornerScale d hα hcA hCA hR
  obtain ⟨q, hqSupport, hqAway⟩ :=
    exists_support_away_from_cubeCorners
      hreg hR hδ h2δR hν hδsmall
  have hqCube : q ∈ unitCube d := hsupport hqSupport
  obtain ⟨hρ, hρR, hcubeρ⟩ :=
    subdiametral_radius_of_away_from_cubeCorners
      hqCube hδ hqAway
  obtain ⟨S, ε, lam, hεeq, hlameq, hSmeas, hSsubset,
      hεpos, hεR, hSlower, hSpos, hlamPos, hlamOne, hanchor⟩ :=
    exists_quantitative_anchor_ball_of_subdiametral_point
      hreg hα hcA hR hqSupport hρ hρR
        (fun x hx => hcubeρ x (hsupport hx))
  exact
    ⟨δ, S, ε, lam, hδ, h2δR, hεeq, hlameq, hSmeas,
      hSsubset, hεpos, hεR, hSlower, hSpos, hlamPos,
      hlamOne, hanchor⟩

/--
A nonzero Ahlfors-regular measure supported in the unit cube admits a
positive-measure anchor ball at a uniformly subdiametral scale.

The values `ε` and `λ` produced here are quantitative once the non-corner
support point is fixed.  The preceding structural theorem strengthens this
statement by using the corner-neighborhood counting argument to make them
depend only on the Ahlfors constants.
-/
theorem exists_unitCube_anchor_ball
    {d : ℕ} {ν : Measure (Ambient d)} {α cA CA : ℝ}
    (hreg : AhlforsRegular ν α cA CA (Real.sqrt d))
    (hd : 0 < d)
    (hα : 0 < α) (hcA : 0 < cA) (hCA : 0 ≤ CA)
    (hν : ν ≠ 0)
    (hsupport : Measure.support ν ⊆ unitCube d) :
    ∃ (S : Set (Ambient d)) (ε lam : ℝ),
      MeasurableSet S ∧
      S ⊆ Measure.support ν ∧
      0 < ε ∧ ε ≤ Real.sqrt d ∧
      ENNReal.ofReal (cA * ε ^ α) ≤ ν S ∧
      0 < ν S ∧
      0 < lam ∧ lam < 1 ∧
      ∀ x ∈ Measure.support ν, ∀ z ∈ S,
        dist x z < lam * Real.sqrt d := by
  have hR : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  obtain ⟨q, hqSupport, hqCorner⟩ :=
    exists_support_not_cubeCorner hreg hα hCA hR hν
  have hqCube : q ∈ unitCube d := hsupport hqSupport
  obtain ⟨ρ, hρ, hρR, hcubeρ⟩ :=
    exists_subdiametral_radius_unitCube hqCube hqCorner
  obtain ⟨S, ε, lam, _hε, _hlam, hSmeas, hSsubset, hεpos, hεR,
      hSlower, hSpos, hlamPos, hlamOne, hanchor⟩ :=
    exists_quantitative_anchor_ball_of_subdiametral_point
      hreg hα hcA hR hqSupport hρ hρR
        (fun x hx => hcubeρ x (hsupport hx))
  exact
    ⟨S, ε, lam, hSmeas, hSsubset, hεpos, hεR, hSlower,
      hSpos, hlamPos, hlamOne, hanchor⟩

end BesovVerification
