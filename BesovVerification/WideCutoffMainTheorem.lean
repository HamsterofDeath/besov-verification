import BesovVerification.AnchorTailComparison
import BesovVerification.FullEnergyDecomposition
import BesovVerification.MainTheorem
import BesovVerification.WideCutoff

/-!
# Full equivalence for a cutoff wider than the cube diameter

This file closes both directions of the Besov-energy comparison when the
averaging cutoff `R` is strictly larger than `sqrt d`.  Unlike the original
endpoint statement, a positive interval of radii remains after every pair of
cube points is visible.  The theorem derives finiteness (and hence `SFinite`)
of the measure from the upper Ahlfors estimate.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- The coefficient controlling global variation by `scaleEnergy`. -/
def wideCutoffTailConstant (d : ℕ) (p R : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal
    (((wideCutoffAnchorRadius d R) ^ (-p) - R ^ (-p)) / p))⁻¹

/-- The coefficient in `besovEnergy ≤ D * averagedEnergy`. -/
def wideCutoffReverseConstant
    (d : ℕ) (p R CA : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal p +
      (ENNReal.ofReal R).rpow (-p) *
        wideCutoffTailConstant d p R) *
    ENNReal.ofReal CA

/-- The lower comparison constant in the conventional orientation. -/
def wideCutoffLowerConstant
    (d : ℕ) (p R CA : ℝ) : ℝ≥0∞ :=
  (wideCutoffReverseConstant d p R CA)⁻¹

/--
The difficult direction of the comparison is complete when the scale cutoff
is strictly larger than the cube diameter.
-/
theorem besovEnergy_le_wideCutoffReverseConstant_mul_averagedEnergy
    {d : ℕ} (ν : Measure (Ambient d))
    {u : Ambient d → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hsupport : Measure.support ν ⊆ unitCube d)
    (hR : Real.sqrt d < R)
    (hp : 0 < α + 2 * s)
    (hCA : 0 < CA) :
    besovEnergy ν α s u ≤
      wideCutoffReverseConstant d (α + 2 * s) R CA *
        averagedEnergy ν s R u := by
  letI : IsFiniteMeasure ν :=
    isFiniteMeasure_of_ahlfors_unitCube ν hreg hsupport hR
  let p := α + 2 * s
  let K := wideCutoffTailConstant d p R
  have hRpos : 0 < R := (Real.sqrt_nonneg d).trans_lt hR
  have hglobal :
      globalVariation ν u ≤ K * scaleEnergy ν α s R u := by
    exact globalVariation_le_scaleEnergy_of_unitCube_wideCutoff
      ν hsupport hR hp
  have hglobalTruncated :
      globalVariation ν u ≤ K * truncatedEnergy ν p R u := by
    simpa only [p, scaleEnergy_eq_truncatedEnergy ν hp hu] using hglobal
  have hfull :
      besovEnergy ν p 0 u ≤
        (ENNReal.ofReal p +
            (ENNReal.ofReal R).rpow (-p) * K) *
          truncatedEnergy ν p R u :=
    besovEnergy_le_truncated_of_globalVariation_le
      ν hu hp hRpos hglobalTruncated
  have hscale :
      scaleEnergy ν α s R u ≤
        ENNReal.ofReal CA * averagedEnergy ν s R u :=
    scaleEnergy_le_upperAhlfors_mul_averagedEnergy
      ν hu hreg hCA
  calc
    besovEnergy ν α s u = besovEnergy ν p 0 u := by
      symm
      exact besovEnergy_repackage ν α s u
    _ ≤ (ENNReal.ofReal p +
          (ENNReal.ofReal R).rpow (-p) * K) *
        truncatedEnergy ν p R u := hfull
    _ = (ENNReal.ofReal p +
          (ENNReal.ofReal R).rpow (-p) * K) *
        scaleEnergy ν α s R u := by
      rw [scaleEnergy_eq_truncatedEnergy ν hp hu]
    _ ≤ (ENNReal.ofReal p +
          (ENNReal.ofReal R).rpow (-p) * K) *
        (ENNReal.ofReal CA * averagedEnergy ν s R u) :=
      mul_le_mul_right hscale _
    _ = wideCutoffReverseConstant d p R CA *
        averagedEnergy ν s R u := by
      unfold wideCutoffReverseConstant
      rw [mul_assoc]

/-- The explicit reverse coefficient is positive and finite. -/
theorem wideCutoffReverseConstant_pos_and_lt_top
    {d : ℕ} {p R CA : ℝ}
    (hR : Real.sqrt d < R) (hp : 0 < p) (hCA : 0 < CA) :
    0 < wideCutoffReverseConstant d p R CA ∧
      wideCutoffReverseConstant d p R CA < ∞ := by
  have hK :=
    wideCutoff_tailCoefficient_pos_finite
      (d := d) (α := p) (s := 0) (R := R) hR (by simpa using hp)
  have hK' :
      0 < wideCutoffTailConstant d p R ∧
        wideCutoffTailConstant d p R < ∞ := by
    simpa [wideCutoffTailConstant] using hK
  have hRpos : 0 < R := (Real.sqrt_nonneg d).trans_lt hR
  have hRpowPos :
      0 < (ENNReal.ofReal R).rpow (-p) :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hRpos)
      ENNReal.ofReal_ne_top
  have hRpowFin :
      (ENNReal.ofReal R).rpow (-p) < ∞ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.ofReal_ne_zero_iff.2 hRpos)
        ENNReal.ofReal_ne_top)
  have hsumPos :
    0 < ENNReal.ofReal p +
          (ENNReal.ofReal R).rpow (-p) *
            wideCutoffTailConstant d p R :=
    (ENNReal.ofReal_pos.2 hp).trans_le le_self_add
  have hsumFin :
      ENNReal.ofReal p +
          (ENNReal.ofReal R).rpow (-p) *
            wideCutoffTailConstant d p R < ∞ := by
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.ofReal_ne_top.lt_top,
      ENNReal.mul_lt_top hRpowFin hK'.2⟩
  unfold wideCutoffReverseConstant
  constructor
  · exact ENNReal.mul_pos hsumPos.ne'
      (ENNReal.ofReal_ne_zero_iff.2 hCA)
  · exact ENNReal.mul_lt_top hsumFin
      ENNReal.ofReal_ne_top.lt_top

/-- Conventional lower-bound orientation for the wide-cutoff theorem. -/
theorem wideCutoffLowerConstant_mul_besovEnergy_le_averagedEnergy
    {d : ℕ} (ν : Measure (Ambient d))
    {u : Ambient d → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hsupport : Measure.support ν ⊆ unitCube d)
    (hR : Real.sqrt d < R)
    (hp : 0 < α + 2 * s)
    (hCA : 0 < CA) :
    wideCutoffLowerConstant d (α + 2 * s) R CA *
        besovEnergy ν α s u ≤
      averagedEnergy ν s R u := by
  let D := wideCutoffReverseConstant d (α + 2 * s) R CA
  have hD :=
    wideCutoffReverseConstant_pos_and_lt_top hR hp hCA
  have hreverse :
      besovEnergy ν α s u ≤ D * averagedEnergy ν s R u :=
    besovEnergy_le_wideCutoffReverseConstant_mul_averagedEnergy
      ν hu hreg hsupport hR hp hCA
  unfold wideCutoffLowerConstant
  change D⁻¹ * besovEnergy ν α s u ≤ averagedEnergy ν s R u
  exact (ENNReal.inv_mul_le_iff hD.1.ne' hD.2.ne).2 hreverse

/--
Full two-sided equivalence, with positive finite constants, for a cutoff
strictly wider than the cube diameter.
-/
theorem exists_wideCutoff_besovEnergy_equivalence_constants
    {d : ℕ} (ν : Measure (Ambient d))
    {u : Ambient d → ℝ} (hu : Measurable u)
    {α s cA CA R : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hsupport : Measure.support ν ⊆ unitCube d)
    (hR : Real.sqrt d < R)
    (hcA : 0 < cA) (hCA : 0 < CA)
    (hp : 0 < α + 2 * s) :
    ∃ c C : ℝ≥0∞,
      0 < c ∧ c < ∞ ∧ 0 < C ∧ C < ∞ ∧
      c * besovEnergy ν α s u ≤ averagedEnergy ν s R u ∧
      averagedEnergy ν s R u ≤ C * besovEnergy ν α s u := by
  letI : IsFiniteMeasure ν :=
    isFiniteMeasure_of_ahlfors_unitCube ν hreg hsupport hR
  let p := α + 2 * s
  let D := wideCutoffReverseConstant d p R CA
  let c : ℝ≥0∞ := D⁻¹
  let C : ℝ≥0∞ :=
    (ENNReal.ofReal cA)⁻¹ * (ENNReal.ofReal p)⁻¹
  have hD : 0 < D ∧ D < ∞ :=
    wideCutoffReverseConstant_pos_and_lt_top hR hp hCA
  have hcpos : 0 < c := ENNReal.inv_pos.2 hD.2.ne
  have hcfin : c < ∞ := ENNReal.inv_lt_top.mpr hD.1
  have hCpos : 0 < C := by
    exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
  have hCfin : C < ∞ := by
    exact ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.2 hcA))
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.2 hp))
  refine ⟨c, C, hcpos, hcfin, hCpos, hCfin, ?_, ?_⟩
  · exact
      wideCutoffLowerConstant_mul_besovEnergy_le_averagedEnergy
        ν hu hreg hsupport hR hp hCA
  · exact averagedEnergy_le_besovEnergy
      ν hu hreg hcA hCA hp

end BesovVerification
