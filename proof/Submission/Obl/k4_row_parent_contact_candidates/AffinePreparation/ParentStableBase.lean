/- Adapted from: here:o222, session x0774, commit 0d01aa57.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ParentStableBase.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedParentSupport
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentSupportBudget
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.StableBaseBudget
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.StableBaseLaw
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.NativeBaseCellGap

/-! Retain the current row law inside the accepted full-parent partition. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh (rootBaseCoordinates)
open Submission.Obl.k4_stable_native_signal_oscillation (nativeBase)

noncomputable section

/-- The accepted full-parent native partition is charged to the original
parent mass. It therefore retains half of any sufficiently dense current row
event, with the original prior and block length in the floor. -/
theorem parent_stable_current_mass {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcommon : a.Common p)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s))
    (G : Set (α × ℝ)) (hG : G ⊆ a.parentSet k s i) (E : Fin 2 → Set (α × ℝ))
    {M η : ℝ} (hM : 0 < M) (hη : 0 ≤ η)
    (hmass : ENNReal.ofReal (a.q k s / M) * a.nu k (a.A k s i) ≤ a.rho k G)
    (hloss : a.mu k (a.parentSet k s i \ ⋃ e, E e) ≤
      a.mu k (a.parentSet k s i) * ENNReal.ofReal η)
    (hsmall : p.K k * η ≤ 1 / (2 * M)) :
    ENNReal.ofReal (a.q k s / (2 * M)) * a.nu k (a.A k s i) ≤
      a.rho k (G ∩ ⋃ e, E e) := by
  have : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hK : 0 ≤ p.K k := zero_le_one.trans (hp.2.2.1.1 k)
  have hq : 0 < a.q k s := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  let m : ℝ := a.q k s * (a.nu k (a.A k s i)).toReal
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hconvert (D : ℝ) (hD : 0 < D) :
      ENNReal.ofReal (m / D) =
        ENNReal.ofReal (a.q k s / D) * a.nu k (a.A k s i) := by
    calc
      _ = ENNReal.ofReal ((a.q k s / D) * (a.nu k (a.A k s i)).toReal) := by
        congr 1
        dsimp [m]
        ring
      _ = _ := by
        rw [ENNReal.ofReal_mul (div_nonneg hq.le hD.le),
          ENNReal.ofReal_toReal (measure_ne_top (a.nu k) (a.A k s i))]
  have hfloor : ENNReal.ofReal (m / M) ≤ a.rho k G := by
    rw [hconvert M hM]
    exact hmass
  have hparent : a.mu k (a.parentSet k s i) ≤ ENNReal.ofReal (p.K k * m) := by
    apply (a.original_parent_mass_upper p hp hcommon hatlas i).trans_eq
    symm
    calc
      _ = ENNReal.ofReal ((p.K k * a.q k s) * (a.nu k (a.A k s i)).toReal) := by
        congr 1
        dsimp [m]
        ring
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hK hq.le),
          ENNReal.ofReal_toReal (measure_ne_top (a.nu k) (a.A k s i))]
  have h := stable_partition_retains_parent (a.mu k) (a.rho k)
    ((hcommon k).2.2.2.2.1) (a.parentSet k s i) G E hG hK hm hM hη hfloor hparent hloss hsmall
  rw [hconvert (2 * M) (by positivity)] at h
  exact h

/-- The original full-parent prior supplies exactly the scale factors needed
to cancel the recovered native-bin ceiling in a row chart. -/
theorem parent_recovered_base_budget {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcommon : a.Common p)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s))
    {T lam : ℝ} (hT : 0 ≤ T) :
    27 * T * (p.K k * width p k s ^ p.d) *
        (|lam| * a.q k s ^ 3 * narrow p k s) /
        (a.q k s * (a.nu k (a.A k s i)).toReal) ≤
      27 * T * p.K k ^ 2 * |lam| := by
  have : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 0 < p.K k := zero_lt_one.trans_le (hp.2.2.1.1 k)
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have hq : 0 < a.q k s := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  apply row_base_budget_cancel ha hq hg hK hT
  have hprior := ENNReal.toReal_mono (measure_ne_top (a.nu k) (a.A k s i))
    (hatlas.2.2.2.2.1 i).1
  simpa only [ENNReal.toReal_ofReal (by positivity :
    0 ≤ width p k s ^ p.d * a.q k s ^ 2 * narrow p k s / p.K k)] using hprior

/-- A stable full-parent partition recovers the sharp base ceiling in a row
chart for ANY current sublaw it covers. The original native width factor and
the full original parent prior cancel; the velocity numerator is unchanged. -/
theorem parent_stable_affine_base_cap {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcommon : a.Common p)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s))
    (ν : Measure (α × ℝ)) (hν : ν ≤ a.mu k) (E : Fin 2 → Set (α × ℝ))
    (hcover : ∀ᵐ z ∂ν, ∃ e, z ∈ E e) {L delta tau sigma lam : ℝ}
    (hL : 0 ≤ L) (hd : 0 < delta) (hs : 0 < sigma)
    (hresolve : ∀ e, (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * delta) ≤ tau)
    (hsmall : L * (3 * tau) ≤ width p k s)
    (hosc : ∀ e z, z ∈ E e → ∀ w, w ∈ E e →
      |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
        2 * (2 * p.K k) ^ 14 * width p k s + L *
          ‖nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k z)) -
            nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k w))‖)
    (condition : α × ℝ → Prop) (weight : ENNReal) (hw : weight ≠ ⊤)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      a.mu k {z | baseMesh delta (basePoint (a.b k z.1) z.2) = q ∧
        ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋ = j ∧ condition z} ≤
        ENNReal.ofReal (p.K k * width p k s ^ p.d * delta ^ 3) * weight)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hA : A.det ≠ 0)
    (hrow : ∀ e, (∑ j, |A e j| * delta) ≤ sigma)
    (hdet : |A.det|⁻¹ = |lam| * a.q k s ^ 3 * narrow p k s)
    (q : Fin 3 → ℤ) :
    ((ENNReal.ofReal (a.q k s * (a.nu k (a.A k s i)).toReal))⁻¹ • ν)
        {z | baseMesh sigma (affineBase A b (basePoint (a.b k z.1) z.2)) = q ∧ condition z} ≤
      ENNReal.ofReal (27 * (2 * (2 * (2 * (2 * p.K k) ^ 14 + 1) + 2)) *
        p.K k ^ 2 * |lam| * sigma ^ 3) * weight := by
  have : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 0 < p.K k := zero_lt_one.trans_le (hp.2.2.1.1 k)
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have hq : 0 < a.q k s := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  have hprior : a.nu k (a.A k s i) ≠ 0 := by
    apply (lt_of_lt_of_le _ (hatlas.2.2.2.2.1 i).1).ne'
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hpriorp : 0 < (a.nu k (a.A k s i)).toReal :=
    ENNReal.toReal_pos hprior (measure_ne_top _ _)
  have hstable : ∀ e z, z ∈ E e → ∀ w, w ∈ E e →
      baseMesh delta (basePoint (a.b k z.1) z.2) =
        baseMesh delta (basePoint (a.b k w.1) w.2) →
      |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
        (2 * (2 * p.K k) ^ 14 + 1) * width p k s := by
    intro e z hz w hw hcell
    have hcell' : baseMesh delta (rootBaseCoordinates (a.nativePoint k z)) =
        baseMesh delta (rootBaseCoordinates (a.nativePoint k w)) := by
      simpa only [a.nativePoint_base] using hcell
    have hgap := native_base_gap_of_mesh_cell (a.parentSupportZoom p k s i) hd hresolve
      (a.nativePoint k z) (a.nativePoint k w) hcell'
    calc
      _ ≤ 2 * (2 * p.K k) ^ 14 * width p k s + L * (3 * tau) :=
        (hosc e z hz w hw).trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hgap hL))
      _ ≤ 2 * (2 * p.K k) ^ 14 * width p k s + width p k s :=
        add_le_add le_rfl hsmall
      _ = _ := by ring
  have h := normalized_stable_affine_base_cap (a.mu k) ν hν
    (fun z => basePoint (a.b k z.1) z.2) (fun z => eval (a.x k z.1 z.2) (a.P k))
    condition E ha (by positivity : 0 ≤ 2 * (2 * p.K k) ^ 14 + 1)
    (by positivity : 0 ≤ p.K k * width p k s ^ p.d) hd hs (mul_pos hq hpriorp)
    hcover hstable weight hw hcap A b hA hrow q
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  rw [hdet]
  calc
    _ = (27 * (2 * (2 * (2 * (2 * p.K k) ^ 14 + 1) + 2)) *
        (p.K k * width p k s ^ p.d) * (|lam| * a.q k s ^ 3 * narrow p k s) /
        (a.q k s * (a.nu k (a.A k s i)).toReal)) * sigma ^ 3 := by ring
    _ ≤ (27 * (2 * (2 * (2 * (2 * p.K k) ^ 14 + 1) + 2)) * p.K k ^ 2 * |lam|) *
        sigma ^ 3 := mul_le_mul_of_nonneg_right
      (parent_recovered_base_budget p hp a hcommon hatlas i (by positivity)) (by positivity)
    _ = _ := by ring

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
