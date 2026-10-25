-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_rigid_copies_volume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_frostman_rigid_copies_volume`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_frostman_rigid_copies_volume`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_frostman_rigid_copies_volume/`
belong to this obligation.
-/

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

namespace WangZahlLot.Obl.wz_frostman_rigid_copies_volume

lemma affine_measurePreserving (A : Space ≃ᵃⁱ[ℝ] Space) :
    MeasurePreserving A := by
  have hA : (fun p : Space => A.linearIsometryEquiv p + A 0) = A := by
    funext p
    simpa using (A.map_vadd (0 : Space) p).symm
  rw [← hA]
  exact (measurePreserving_add_right volume (A 0)).comp A.linearIsometryEquiv.measurePreserving

lemma affine_volume_image (A : Space ≃ᵃⁱ[ℝ] Space) (S : Set Space) :
    volume (A '' S) = volume S := by
  have h := (affine_measurePreserving A).measure_preimage_emb
    A.toHomeomorph.measurableEmbedding (A '' S)
  simpa only [Set.preimage_image_eq _ A.injective] using h.symm

lemma affine_tube_image_subset (A : Space ≃ᵃⁱ[ℝ] Space)
    (d : ℝ) (p q : Space) :
    A '' Metric.thickening d (segment ℝ p (p + q)) ⊆
      Metric.thickening d (segment ℝ (A p) (A p + A.linear q)) := by
  rintro y ⟨u, hu, rfl⟩
  rcases Metric.mem_thickening_iff.mp hu with ⟨z, hz, huz⟩
  refine Metric.mem_thickening_iff.mpr ⟨A z, ?_, by simpa using huz⟩
  have hz' : A z ∈ segment ℝ (A p) (A (p + q)) := by
    have hi := image_segment ℝ A.toAffineEquiv.toAffineMap p (p + q)
    change A '' segment ℝ p (p + q) = segment ℝ (A p) (A (p + q)) at hi
    rw [← hi]
    exact ⟨z, hz, rfl⟩
  have hApq : A (p + q) = A p + A.linear q := by
    simpa only [vadd_eq_add, add_comm, AffineIsometryEquiv.coe_toAffineEquiv] using
      A.toAffineEquiv.map_vadd p q
  rwa [hApq] at hz'

end WangZahlLot.Obl.wz_frostman_rigid_copies_volume

open WangZahlLot.Obl.wz_frostman_rigid_copies_volume

theorem WangZahlLot.wz_frostman_rigid_copies_volume : ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ F, F = (fun (d K : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ ρ₀ : ℝ, d ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ K * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ (z w : Fin k → LeanEval.Analysis.WangZahlKakeya.Space), (∀ j : Fin k, ‖w j‖ = 1) ∧ (∀ j j' : Fin k, j ≠ j' → MeasureTheory.volume (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T ρ (z j) (w j))) ∧ (∀ i : Fin n, ∃! j : Fin k, T d (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j : Fin k, ∃ i : Fin n, T d (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j j' : Fin k, (((Set.ncard {i : Fin n | T d (x i) (v i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ)) ≤ K * (((Set.ncard {i : Fin n | T d (x i) (v i) ⊆ T ρ (z j') (w j')} : ℕ) : ℝ))) ∧ (∀ j : Fin k, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((((Set.ncard {i : Fin n | T d (x i) (v i) ⊆ T ρ (z j) (w j) ∧ T d (x i) (v i) ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤ ENNReal.ofReal (K * (((Set.ncard {i : Fin n | T d (x i) (v i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ))) * MeasureTheory.volume W)) → (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, T δ (x i) (v i) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ T δ (x i) (v i)) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → F δ (δ ^ (-η)) n x v → ENNReal.ofReal (a * δ ^ ε) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)) → ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n N m : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (A : Fin N → (LeanEval.Analysis.WangZahlKakeya.Space ≃ᵃⁱ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space)) (c : Fin m → Fin n) (g : Fin m → Fin N) (x' v' : Fin m → LeanEval.Analysis.WangZahlKakeya.Space), 0 < m → (∀ i : Fin n, ‖v i‖ = 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) → (∀ s : Fin m, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ MeasureTheory.volume (Y (c s)) ∧ x' s = A (g s) (x (c s)) ∧ v' s = (A (g s)).linear (v (c s)) ∧ T δ (x' s) (v' s) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ s t : Fin m, s ≠ t → MeasureTheory.volume (T δ (x' s) (v' s) ∩ T δ (x' t) (v' t)) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T δ (x' s) (v' s))) → F δ (δ ^ (-η)) m x' v' → ENNReal.ofReal (a * δ ^ ε) ≤ (N : ENNReal) * MeasureTheory.volume (⋃ i : Fin n, Y i) := by
  classical
  intro T hT F hF H ε hε
  obtain ⟨a, ha, η, hη, h⟩ := H ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 n N m x v Y A c g x' v' hm hY hcopies hsep hFrost
  let Z : Fin m → Set Space := fun s => A (g s) '' Y (c s)
  have hZvol (s : Fin m) : volume (Z s) = volume (Y (c s)) :=
    affine_volume_image (A (g s)) (Y (c s))
  have hv' (s : Fin m) : ‖v' s‖ = 1 := by
    rw [(hcopies s).2.2.1]
    exact ((A (g s)).norm_map _).trans (hY (c s)).1
  have hZmeas (s : Fin m) : MeasurableSet (Z s) :=
    (A (g s)).toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hY (c s)).2.1
  have hZsub (s : Fin m) : Z s ⊆ T δ (x' s) (v' s) := by
    have hImage : A (g s) '' T δ (x (c s)) (v (c s)) ⊆ T δ (x' s) (v' s) := by
      rw [hT, (hcopies s).2.1, (hcopies s).2.2.1]
      exact affine_tube_image_subset (A (g s)) δ (x (c s)) (v (c s))
    exact (Set.image_mono (hY (c s)).2.2).trans hImage
  have hZsum : ENNReal.ofReal (δ ^ η * (m : ℝ) * δ ^ 2) ≤
      ∑ s : Fin m, volume (Z s) := by
    calc
      ENNReal.ofReal (δ ^ η * (m : ℝ) * δ ^ 2) =
          ∑ _s : Fin m, ENNReal.ofReal (δ ^ η * δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show δ ^ η * (m : ℝ) * δ ^ 2 = (m : ℝ) * (δ ^ η * δ ^ 2) by ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
      _ ≤ ∑ s : Fin m, volume (Z s) := by
        apply Finset.sum_le_sum
        intro s hs
        rw [hZvol]
        exact (hcopies s).1
  have hLower := h δ hδ hδ100 m x' v' Z hm hv'
    (fun s => (hcopies s).2.2.2) hsep hZmeas hZsub hZsum hFrost
  calc
    ENNReal.ofReal (a * δ ^ ε) ≤ volume (⋃ s : Fin m, Z s) := hLower
    _ ≤ volume (⋃ j : Fin N, A j '' (⋃ i : Fin n, Y i)) := by
      apply measure_mono
      refine Set.iUnion_subset fun s => ?_
      exact (Set.image_mono (Set.subset_iUnion Y (c s))).trans
        (Set.subset_iUnion (fun j : Fin N => A j '' (⋃ i : Fin n, Y i)) (g s))
    _ ≤ ∑ j : Fin N, volume (A j '' (⋃ i : Fin n, Y i)) :=
      measure_iUnion_fintype_le volume _
    _ = (N : ENNReal) * volume (⋃ i : Fin n, Y i) := by
      simp only [affine_volume_image, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
