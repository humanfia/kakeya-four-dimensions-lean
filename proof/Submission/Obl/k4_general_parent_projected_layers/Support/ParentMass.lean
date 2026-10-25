/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentMass.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Model
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Full original parent incidence floors and the cancellation of zoom volume. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem incidence_mass_le (p : Parameters) (a : PreparedModel α)
    (hcommon : a.Common p) (k : ℕ) : a.mu k univ ≤ ENNReal.ofReal (p.K k) := by
  have : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  let E : Set (α × ℝ) := univ ×ˢ Icc 0 1
  have hE : MeasurableSet E := MeasurableSet.univ.prod measurableSet_Icc
  have hfull : a.mu k E = a.mu k univ := by
    have h := measure_add_measure_compl (μ := a.mu k) hE
    rw [(hcommon k).2.2.2.2.2.1, add_zero] at h
    exact h
  rw [← hfull]
  have h := (hcommon k).2.2.2.1 E
  simpa only [E, Measure.smul_apply, smul_eq_mul, Measure.prod_prod, measure_univ,
    Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one, one_mul] using h

theorem incidence_finite (p : Parameters) (a : PreparedModel α)
    (hcommon : a.Common p) (k : ℕ) : IsFiniteMeasure (a.mu k) :=
  ⟨(a.incidence_mass_le p hcommon k).trans_lt ENNReal.ofReal_lt_top⟩

/-- The floor is charged to the full original prior and the true block length. -/
theorem original_parent_mass_lower (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    ENNReal.ofReal (width p k s ^ p.d * a.q k s ^ 3 * narrow p k s / p.K k ^ 2) ≤
      a.mu k (a.B k s i ×ˢ a.block k s i) := by
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 k)
  have hq : 0 < a.q k s := by unfold q; positivity
  have hprior := (hatlas.2.2.2.2.1 i).1
  have hinc := (hatlas.2.2.2.2.1 i).2.2.1
  calc
    _ = ENNReal.ofReal (a.q k s / p.K k) *
        ENNReal.ofReal (width p k s ^ p.d * a.q k s ^ 2 * narrow p k s / p.K k) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hq.le hK.le)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (a.q k s / p.K k) * a.nu k (a.A k s i) :=
      mul_le_mul' le_rfl hprior
    _ ≤ _ := hinc

theorem original_parent_mass_pos (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    0 < a.mu k (a.B k s i ×ˢ a.block k s i) := by
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 k)
  have hwidth : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have ha : 0 < width p k s ^ p.d := Real.rpow_pos_of_pos hwidth _
  have hq : 0 < a.q k s := by unfold q; positivity
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  exact (ENNReal.ofReal_pos.mpr (by positivity)).trans_le
    (a.original_parent_mass_lower p hp hatlas i)

theorem original_parent_mass_toReal_lower (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcommon : a.Common p)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    width p k s ^ p.d * a.q k s ^ 3 * narrow p k s / p.K k ^ 2 ≤
      (a.mu k (a.B k s i ×ˢ a.block k s i)).toReal := by
  have : IsFiniteMeasure (a.mu k) := a.incidence_finite p hcommon k
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 k)
  have hq : 0 < a.q k s := by unfold q; positivity
  have hwidth : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have had : 0 < width p k s ^ p.d := Real.rpow_pos_of_pos hwidth _
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (a.original_parent_mass_lower p hp hatlas i)
  simpa only [ENNReal.toReal_ofReal (by positivity :
    0 ≤ width p k s ^ p.d * a.q k s ^ 3 * narrow p k s / p.K k ^ 2)] using h

end PreparedModel

/-- A source base cap from unit signal bins is at most `(4K+2)K`.
Dividing by the full incidence mass and zooming cancels `q^3*g`. -/
theorem parent_filling_bound {K a d q g m : ℝ}
    (hK : 1 ≤ K) (ha : 0 < a) (hq : 0 < q) (hg : 0 < g)
    (hm : a ^ d * q ^ 3 * g / K ^ 2 ≤ m) :
    27 * ((4 * K + 2) * K / m) * (16384 * K ^ 3 * q ^ 3 * g) ≤
      2654208 * K ^ 7 / a ^ d := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have had : 0 < a ^ d := Real.rpow_pos_of_pos ha _
  have hf : 0 < a ^ d * q ^ 3 * g / K ^ 2 := by positivity
  have hm0 : 0 < m := hf.trans_le hm
  have hnum : 0 ≤ 27 * ((4 * K + 2) * K) * (16384 * K ^ 3 * q ^ 3 * g) := by positivity
  calc
    _ = (27 * ((4 * K + 2) * K) * (16384 * K ^ 3 * q ^ 3 * g)) / m := by ring
    _ ≤ (27 * ((4 * K + 2) * K) * (16384 * K ^ 3 * q ^ 3 * g)) /
        (a ^ d * q ^ 3 * g / K ^ 2) := div_le_div_of_nonneg_left hnum hf hm
    _ = 442368 * (4 * K + 2) * K ^ 6 / a ^ d := by
      field_simp
      ring
    _ ≤ _ := by
      apply (div_le_div_iff_of_pos_right had).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * K - 2) (pow_nonneg hK0.le 6)]

def parentFilling (K a : ℝ) : ℝ := 3000000 * K ^ 20 / a

theorem parent_filling_le {K a d : ℝ} (hK : 1 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hd1 : d ≤ 1) : 2654208 * K ^ 7 / a ^ d ≤ parentFilling K a := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have had : a ≤ a ^ d := Real.self_le_rpow_of_le_one ha.le ha1 hd1
  have hpower : K ^ 7 ≤ K ^ 20 := pow_le_pow_right₀ hK (by decide : 7 ≤ 20)
  calc
    _ ≤ 2654208 * K ^ 7 / a := div_le_div_of_nonneg_left (by positivity) ha had
    _ ≤ parentFilling K a := by
      apply (div_le_div_iff_of_pos_right ha).mpr
      nlinarith [pow_nonneg hK0.le 20]

theorem native_power_le_parentFilling {K a : ℝ} (hK : 1 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1) :
    (2 * K) ^ 16 ≤ parentFilling K a := by
  have hpower : K ^ 16 ≤ K ^ 20 := pow_le_pow_right₀ hK (by decide : 16 ≤ 20)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  apply (le_div_iff₀ ha).mpr
  calc
    _ ≤ (2 * K) ^ 16 * 1 := mul_le_mul_of_nonneg_left ha1 (by positivity)
    _ = 65536 * K ^ 16 := by norm_num [mul_pow]
    _ ≤ 3000000 * K ^ 20 := by nlinarith [pow_nonneg hK0.le 20]

end

end Submission.Obl.k4_general_parent_projected_layers
