-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.LocalCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyMultiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

theorem sum_fibre_ncard {n N : ℕ} (f : Fin n → Fin N) (R : Fin n → Prop) :
    ∑ k : Fin N, ({i : Fin n | f i = k ∧ R i}.ncard : ℝ) =
      ({i : Fin n | R i}.ncard : ℝ) := by
  classical
  have h := Finset.sum_fiberwise Finset.univ f (fun i => if R i then (1 : ℝ) else 0)
  simpa only [Finset.sum_boole, ncard_eq_toFinset_card', Set.toFinset_setOf,
    Finset.filter_filter] using h

/-- Covering a family by finitely many classes with local convex count `m`
gives a global convex count with the number of classes as the only loss. -/
theorem body_convex_count_of_cover {n N : ℕ} {U : Fin n → Set Space} {w m : ℝ}
    (hw : 0 ≤ w) (R : Fin N → Fin n → Prop) (hcover : ∀ i, ∃ k, R k i)
    (hlocal : ∀ k W, Convex ℝ W →
      ENNReal.ofReal (({i : Fin n | R k i ∧ U i ⊆ W}.ncard : ℝ) * w) ≤
        ENNReal.ofReal m * volume W) :
    BodyConvexCount U w (N * m) := by
  classical
  choose f hf using hcover
  intro W hW
  have hpart (k : Fin N) :
      ENNReal.ofReal (({i : Fin n | f i = k ∧ U i ⊆ W}.ncard : ℝ) * w) ≤
        ENNReal.ofReal m * volume W := by
    apply le_trans _ (hlocal k W hW)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ hw
    apply Nat.cast_le.mpr
    apply Set.ncard_mono
    intro i hi
    exact ⟨hi.1 ▸ hf i, hi.2⟩
  calc
    ENNReal.ofReal (({i : Fin n | U i ⊆ W}.ncard : ℝ) * w) =
        ∑ k : Fin N, ENNReal.ofReal (({i : Fin n | f i = k ∧ U i ⊆ W}.ncard : ℝ) * w) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← Finset.sum_mul,
        sum_fibre_ncard]
    _ ≤ ∑ _k : Fin N, ENNReal.ofReal m * volume W := Finset.sum_le_sum fun k _ => hpart k
    _ = ENNReal.ofReal (N * m) * volume W := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      exact (mul_assoc _ _ _).symm

/-- The local grain count survives an injective restriction of the index set. -/
theorem local_convex_count_restrict {n l : ℕ} (g : Fin n → Fin l) (hg : Function.Injective g)
    (U : Fin l → Set Space) (R : Fin l → Prop) {w m : ℝ} (hw : 0 ≤ w)
    (hlocal : ∀ W, Convex ℝ W →
      ENNReal.ofReal (({j : Fin l | R j ∧ U j ⊆ W}.ncard : ℝ) * w) ≤
        ENNReal.ofReal m * volume W) :
    ∀ W, Convex ℝ W →
      ENNReal.ofReal (({i : Fin n | R (g i) ∧ U (g i) ⊆ W}.ncard : ℝ) * w) ≤
        ENNReal.ofReal m * volume W := by
  intro W hW
  apply le_trans _ (hlocal W hW)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ hw
  apply Nat.cast_le.mpr
  have hi : Set.InjOn g {i : Fin n | R (g i) ∧ U (g i) ⊆ W} := hg.injOn
  rw [← hi.ncard_image]
  exact Set.ncard_mono (by rintro _ ⟨i, hi, rfl⟩; exact hi)

/-- A finite covering by doubled reference grains converts the exact local
convex-count hypothesis in `G` to the body-estimate input. -/
theorem grain_convex_count_of_anchors {n L K : ℕ} (s : Fin n → Fin L)
    (hs : Function.Injective s) (ref : Fin K → Fin L) {a ρ c m : ℝ}
    (hw : 0 ≤ a * (ρ * c) * c) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V)
    (hcover : ∀ i, ∃ k,
      P (a / ρ) c c (z (s i)) (e (s i)) ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z (ref k)) (e (ref k)))
    (hlocal : ∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W) :
    BodyConvexCount (fun i => P a (ρ * c) c (z (s i)) (e (s i)))
      (a * (ρ * c) * c) (K * m) := by
  apply body_convex_count_of_cover hw
    (fun k i => P (a / ρ) c c (z (s i)) (e (s i)) ⊆
      P (2 * a / ρ) (2 * c) (2 * c) (z (ref k)) (e (ref k))) hcover
  intro k
  exact local_convex_count_restrict s hs (fun j => P a (ρ * c) c (z j) (e j))
    (fun j => P (a / ρ) c c (z j) (e j) ⊆
      P (2 * a / ρ) (2 * c) (2 * c) (z (ref k)) (e (ref k))) hw (hlocal (ref k))

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
