-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_packet_counting_transfer.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Basic

namespace WangZahlLot.Obl.wz_affine_packet_counting_transfer

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Each counted output tube contributes a disjoint fiber of counted input tubes. -/
theorem convex_transfer {δ ρ h t m : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (_hh : 0 < h) (_ht : 0 < t) (hm : 0 ≤ m) {n N q : ℕ} (hq : 0 < q)
    (x v : Fin n → Space) (z w : Fin N → Space)
    (F : Fin N → Finset (Fin n)) (f : AffineEquiv ℝ Space Space)
    (hcard : ∀ a, (F a).card = q)
    (hdisj : ∀ a b, a ≠ b → Disjoint (F a) (F b))
    (hB : ∀ i, Tube δ (x i) (v i) ⊆ Ball)
    (hsub : ∀ a i, i ∈ F a → Tube δ (x i) (v i) ⊆ f '' Tube ρ (z a) (w a))
    (hvol : ∀ Q : Set Space, Convex ℝ Q →
      volume (f '' Q ∩ Ball) ≤ ENNReal.ofReal (t / h) * volume Q)
    (hK : ConvexCount δ m n x v) :
    ConvexCount ρ (m * (t / h) * ρ ^ 2 / ((q : ℝ) * δ ^ 2)) N z w := by
  intro Q hQ
  let S : Set (Fin N) := {a | Tube ρ (z a) (w a) ⊆ Q}
  let A : Set (Fin n) := {i | Tube δ (x i) (v i) ⊆ f '' Q ∩ Ball}
  have hc : S.ncard * q ≤ A.ncard := fiber_count F hcard hdisj S A (by
    intro a ha i hi p hp
    exact ⟨Set.image_mono ha (hsub a i hi hp), hB i hp⟩)
  have hc' : (S.ncard : ℝ) * (q : ℝ) ≤ (A.ncard : ℝ) := by exact_mod_cast hc
  have he : ENNReal.ofReal ((S.ncard : ℝ) * (q : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal (m * (t / h)) * volume Q := by
    calc
      _ ≤ ENNReal.ofReal ((A.ncard : ℝ) * δ ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc' (sq_nonneg δ))
      _ ≤ ENNReal.ofReal m * volume (f '' Q ∩ Ball) := hK _ (convex_pullback f hQ)
      _ ≤ ENNReal.ofReal m * (ENNReal.ofReal (t / h) * volume Q) := by
        gcongr
        exact hvol Q hQ
      _ = _ := by rw [ENNReal.ofReal_mul hm, mul_assoc]
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hc0 : 0 ≤ ρ ^ 2 / ((q : ℝ) * δ ^ 2) := by positivity
  calc
    ENNReal.ofReal ((S.ncard : ℝ) * ρ ^ 2) =
        ENNReal.ofReal (ρ ^ 2 / ((q : ℝ) * δ ^ 2)) *
          ENNReal.ofReal ((S.ncard : ℝ) * (q : ℝ) * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul hc0]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (ρ ^ 2 / ((q : ℝ) * δ ^ 2)) *
        (ENNReal.ofReal (m * (t / h)) * volume Q) := by gcongr
    _ = ENNReal.ofReal (m * (t / h) * ρ ^ 2 / ((q : ℝ) * δ ^ 2)) * volume Q := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hc0]
      congr 2
      ring

/-- Testing the transferred bound on one tube normalizes its counting constant. -/
theorem constant_lower {ρ A : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hA : 0 ≤ A)
    {N : ℕ} (hN : 0 < N) (z w : Fin N → Space) (hw : ∀ a, ‖w a‖ = 1)
    (hK : ConvexCount ρ A N z w) : 1 ≤ 384 * A := by
  let a : Fin N := ⟨0, hN⟩
  let S : Set (Fin N) := {b | Tube ρ (z b) (w b) ⊆ Tube ρ (z a) (w a)}
  have hc : 1 ≤ S.ncard := (Set.ncard_pos (Set.toFinite S)).mpr ⟨a, Subset.rfl⟩
  have hc' : 1 ≤ (S.ncard : ℝ) := by exact_mod_cast hc
  have he : ENNReal.ofReal (ρ ^ 2) ≤ ENNReal.ofReal (A * (384 * ρ ^ 2)) := by
    calc
      _ ≤ ENNReal.ofReal ((S.ncard : ℝ) * ρ ^ 2) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg ρ])
      _ ≤ ENNReal.ofReal A * volume (Tube ρ (z a) (w a)) :=
        hK _ (convex_tube _ _ _)
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (384 * ρ ^ 2) := by
        gcongr
        exact tube_volume_upper hρ hρ1 _ _ (hw a)
      _ = _ := (ENNReal.ofReal_mul hA).symm
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  nlinarith [sq_pos_of_pos hρ]

theorem convex_count_mono {δ m M : ℝ} (hm : m ≤ M) {n : ℕ}
    {x v : Fin n → Space} (hK : ConvexCount δ m n x v) : ConvexCount δ M n x v := by
  intro Q hQ
  apply (hK Q hQ).trans
  gcongr

end WangZahlLot.Obl.wz_affine_packet_counting_transfer
