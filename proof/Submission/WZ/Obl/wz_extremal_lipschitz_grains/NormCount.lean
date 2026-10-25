-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormConflict
import Submission.WZ.Obl.wz_separated_cover_refinement.Selection

/-!
# Conflict graphs of zoomed pieces have degree `O(lam ^ 4)`

`conflict` relates two used tubes whose zoomed pieces nearly coincide in either order. A
non-conflicting pair has half-distinct pieces and no common unit sub-tube; a used tube conflicts
with at most `normBound lam` others, so a proper colouring with `normBound lam + 1` colours exists.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal

/-- If the first original tube lies near the second line, the second tube lies near the first
line (with worse constants). -/
theorem tube_subset_LC_swap {c : Space} {ρ r : ℝ} (hρ : 0 < ρ) {z w z' w' : Space}
    (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) (hcz : ‖c - z‖ ≤ 3) (hcz' : ‖c - z'‖ ≤ 3) (hr : r ≤ 1 / 4)
    (h : tube ρ z w ⊆ LC (foot c z' w') w' 25 r) :
    tube ρ z' w' ⊆ LC (foot c z w) w 61 (117 * r + ρ) := by
  obtain ⟨σ₀, hσ₀, h₀⟩ := h (axis_mem_tube hρ z w (t := 0) ⟨le_rfl, zero_le_one⟩)
  obtain ⟨σ₁, hσ₁, h₁⟩ := h (axis_mem_tube hρ z w (t := 1) ⟨zero_le_one, le_rfl⟩)
  simp only [zero_smul, add_zero, one_smul] at h₀ h₁
  set τ := inner ℝ (c - z) w with hτ
  have hfz : foot c z w = z + τ • w := rfl
  have e₀ : ‖(foot c z' w' + σ₀ • w') - (foot c z w + (-τ) • w)‖ ≤ r := by
    rw [hfz, show z + τ • w + (-τ) • w = z by module, norm_sub_rev]; exact h₀.le
  have e₁ : ‖(foot c z' w' + σ₁ • w') - (foot c z w + (1 - τ) • w)‖ ≤ r := by
    rw [hfz, show z + τ • w + (1 - τ) • w = z + w by module, norm_sub_rev]; exact h₁.le
  have hgap : 1 / 2 ≤ |σ₁ - σ₀| := by
    set A := (foot c z' w' + σ₁ • w') - (foot c z w + (1 - τ) • w) with hA
    set B := (foot c z' w' + σ₀ • w') - (foot c z w + (-τ) • w) with hB
    have he : (σ₁ - σ₀) • w' = A + w - B := by rw [hA, hB]; module
    have h1 : ‖(σ₁ - σ₀) • w'‖ = |σ₁ - σ₀| := by rw [norm_smul, hw', mul_one, Real.norm_eq_abs]
    have h2 : ‖w‖ ≤ ‖A + w - B‖ + ‖A‖ + ‖B‖ := by
      calc ‖w‖ = ‖((A + w - B) - A) + B‖ := by congr 1; abel
        _ ≤ ‖(A + w - B) - A‖ + ‖B‖ := norm_add_le _ _
        _ ≤ ‖A + w - B‖ + ‖A‖ + ‖B‖ := by linarith [norm_sub_le (A + w - B) A]
    rw [← he, h1, hw] at h2
    linarith
  have hne : σ₀ ≠ σ₁ := by
    intro h; rw [h, sub_self, abs_zero] at hgap; linarith
  intro p hp
  obtain ⟨t'', ht'', hpt⟩ := mem_tube_iff.mp hp
  set τ' := inner ℝ (c - z') w' with hτ'
  have hτ'b : |τ'| ≤ 3 := by
    calc |τ'| ≤ ‖c - z'‖ * ‖w'‖ := abs_real_inner_le_norm _ _
      _ ≤ 3 * 1 := by rw [hw']; gcongr
      _ = 3 := by ring
  have hτb : |τ| ≤ 3 := by
    calc |τ| ≤ ‖c - z‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ 3 * 1 := by rw [hw]; gcongr
      _ = 3 := by ring
  set t := t'' - τ' with ht
  have hz' : z' + t'' • w' = foot c z' w' + t • w' := by
    simp only [foot, ht, ← hτ']; module
  have htb : |t| ≤ 4 := by
    rw [ht, abs_le]
    constructor <;> linarith [ht''.1, ht''.2, (abs_le.mp hτ'b).1, (abs_le.mp hτ'b).2]
  have hext := extrap hne e₀ e₁ t
  set μ := (t - σ₀) / (σ₁ - σ₀) with hμ
  have hμb : |μ| ≤ 58 := by
    rw [hμ, abs_div, div_le_iff₀ (by linarith)]
    have : |t - σ₀| ≤ 29 := by
      rw [abs_le]
      constructor <;> linarith [(abs_le.mp htb).1, (abs_le.mp htb).2, hσ₀.1, hσ₀.2]
    nlinarith
  refine ⟨-τ + μ * (1 - τ - -τ), ⟨?_, ?_⟩, ?_⟩
  · have : (1 : ℝ) - τ - -τ = 1 := by ring
    rw [this, mul_one]
    linarith [(abs_le.mp hμb).1, (abs_le.mp hτb).2]
  · have : (1 : ℝ) - τ - -τ = 1 := by ring
    rw [this, mul_one]
    linarith [(abs_le.mp hμb).2, (abs_le.mp hτb).1]
  · have hsplit : p - (foot c z w + (-τ + μ * (1 - τ - -τ)) • w) = (p - (z' + t'' • w')) +
        ((foot c z' w' + t • w') - (foot c z w + (-τ + μ * (1 - τ - -τ)) • w)) := by
      rw [hz']; abel
    rw [hsplit]
    have hr0 : 0 ≤ r := (norm_nonneg _).trans e₀
    calc _ ≤ ‖p - (z' + t'' • w')‖ +
          ‖(foot c z' w' + t • w') - (foot c z w + (-τ + μ * (1 - τ - -τ)) • w)‖ :=
          norm_add_le _ _
      _ < ρ + (1 + 2 * |μ|) * r := add_lt_add_of_lt_of_le hpt hext
      _ ≤ ρ + 117 * r := by
          have : (1 + 2 * |μ|) * r ≤ 117 * r := mul_le_mul_of_nonneg_right (by linarith) hr0
          linarith
      _ = 117 * r + ρ := by ring

/-- Packing of half-distinct unit tubes in a line container. -/
theorem card_le_of_subset_LC {k : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hR1 : R ≤ 1)
    (z w : Fin k → Space) (hw : ∀ j, ‖w j‖ = 1)
    (hsep : ∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (tube ρ (z j) (w j)))
    {a u : Space} (hu : ‖u‖ = 1) (S : Finset (Fin k))
    (hS : ∀ j ∈ S, tube ρ (z j) (w j) ⊆ LC a u 61 R) :
    (S.card : ℝ) * ρ ^ 4 ≤ 10 ^ 6 * (46848 * R ^ 2) ^ 2 := by
  classical
  let e : Fin S.card → Fin k := fun i => (S.equivFin.symm i).val
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hvol := volume_LC_le (a := a) hu (M := 61) (r := R) (by norm_num) hR
  have hvol' : volume (LC a u 61 R) ≤ ENNReal.ofReal (46848 * R ^ 2) :=
    hvol.trans (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg R]))
  have hpack := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hρ
    (fun i => z (e i)) (fun i => w (e i))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol') (fun i => hw (e i))
    (fun i => hS _ (S.equivFin.symm i).property)
    (fun i j hij => hsep (e i) (e j) (he.ne hij))
  have hle : ENNReal.ofReal ((S.card : ℝ) * ρ ^ 4) ≤ ENNReal.ofReal (10 ^ 6 * (46848 * R ^ 2) ^ 2) := by
    calc _ ≤ ENNReal.ofReal 1000000 * (volume (LC a u 61 R)) ^ 2 := hpack
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal (46848 * R ^ 2)) ^ 2 := by gcongr
      _ = ENNReal.ofReal (10 ^ 6 * (46848 * R ^ 2) ^ 2) := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle

/-- The conflict relation between used tubes at zoom `lam` about `c`, zoomed radius `R`. -/
def conflict {k : ℕ} (c : Space) (lam R : ℝ) (z w : Fin k → Space) (U : Fin k → Prop)
    (j j' : Fin k) : Prop :=
  U j ∧ U j' ∧ j ≠ j' ∧
    (TwoNear (10000 * R) (pieceStart c lam (z j) (w j)) (w j)
        (pieceStart c lam (z j') (w j')) (w j') ∨
      TwoNear (10000 * R) (pieceStart c lam (z j') (w j')) (w j')
        (pieceStart c lam (z j) (w j)) (w j))

theorem conflict_symm {k : ℕ} {c : Space} {lam R : ℝ} {z w : Fin k → Space} {U : Fin k → Prop}
    {j j' : Fin k} (h : conflict c lam R z w U j j') : conflict c lam R z w U j' j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h2, h1, Ne.symm h3, h4.symm⟩

/-- Non-conflicting used pieces are half-distinct. -/
theorem half_of_not_conflict {k : ℕ} {c : Space} {lam R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 10000)
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {U : Fin k → Prop} {j j' : Fin k}
    (hj : U j) (hj' : U j') (hne : j ≠ j') (hnc : ¬ conflict c lam R z w U j j') :
    volume (tube R (pieceStart c lam (z j) (w j)) (w j) ∩
        tube R (pieceStart c lam (z j') (w j')) (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (tube R (pieceStart c lam (z j) (w j)) (w j)) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨hj, hj', hne, Or.inl (twoNear_of_overlap hR hR1 (hw j) (hw j') hlt)⟩

/-- Non-conflicting used pieces contain no common unit tube. -/
theorem not_common_of_not_conflict {k : ℕ} {c : Space} {lam R r : ℝ} (hr : 0 < r)
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {U : Fin k → Prop} {j j' : Fin k}
    (hj : U j) (hj' : U j') (hne : j ≠ j') (hnc : ¬ conflict c lam R z w U j j')
    {q u₀ : Space} (hu₀ : ‖u₀‖ = 1)
    (h₁ : tube r q u₀ ⊆ tube R (pieceStart c lam (z j) (w j)) (w j))
    (h₂ : tube r q u₀ ⊆ tube R (pieceStart c lam (z j') (w j')) (w j')) : False :=
  hnc ⟨hj, hj', hne, Or.inl (twoNear_of_common hr hu₀ (hw j) (hw j') h₁ h₂)⟩

/-- The degree bound constant. -/
noncomputable def normBound (lam : ℝ) : ℕ := ⌊(10 : ℝ) ^ 60 * lam ^ 4⌋₊

/-- Conflicting tubes lie in a common line container. -/
theorem subset_LC_of_conflict {k : ℕ} {c : Space} {lam ρ R : ℝ} (hlam : 1 ≤ lam) (hρ : 0 < ρ)
    (hR : 0 ≤ R)
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {U : Fin k → Prop}
    (hU : ∀ j, U j → ‖c - z j‖ ≤ 3)
    (hsmall : (2 + 8 * lam) * (10000 * R / lam) + ρ ≤ 1 / 4) {j j' : Fin k}
    (h : conflict c lam R z w U j j') :
    tube ρ (z j') (w j') ⊆ LC (foot c (z j) (w j)) (w j) 61
      (117 * ((2 + 8 * lam) * (10000 * R / lam) + ρ) + ρ) := by
  obtain ⟨hj, hj', -, h | h⟩ := h
  · refine (tube_subset_LC_of_twoNear hlam hρ (hw j') (hU j' hj') h).trans (LC_mono (by norm_num) ?_)
    have hlam0 : 0 < lam := by linarith
    have h0 : 0 ≤ (2 + 8 * lam) * (10000 * R / lam) + ρ := by positivity
    linarith
  · have h1 := tube_subset_LC_of_twoNear hlam hρ (hw j) (hU j hj) h
    exact tube_subset_LC_swap hρ (hw j) (hw j') (hU j hj) (hU j' hj') hsmall h1

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
