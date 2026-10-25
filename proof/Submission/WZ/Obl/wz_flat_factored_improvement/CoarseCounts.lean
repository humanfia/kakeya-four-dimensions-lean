-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.CoarseCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.CoarseBodies
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseSlabs

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric

theorem BodyConvexCount.scale_weight {n : ℕ} {U : Fin n → Set Space} {w m C : ℝ}
    (hC : 0 ≤ C) (hc : BodyConvexCount U w m) : BodyConvexCount U (C * w) (C * m) := by
  intro Q hQ
  calc
    _ = ENNReal.ofReal C * ENNReal.ofReal ((Set.ncard {i | U i ⊆ Q} : ℝ) * w) := by
      rw [← ENNReal.ofReal_mul hC]; congr 1; ring
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal m * volume Q) := mul_le_mul' le_rfl (hc Q hQ)
    _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]

theorem BodyConvexCount.enlarge {n : ℕ} {U V : Fin n → Set Space} {w m : ℝ}
    (hw : 0 ≤ w) (hc : BodyConvexCount U w m) (hUV : ∀ i, U i ⊆ V i) :
    BodyConvexCount V w m := by
  intro Q hQ
  have hn : Set.ncard {i | V i ⊆ Q} ≤ Set.ncard {i | U i ⊆ Q} :=
    ncard_mono (fun i hi => (hUV i).trans hi)
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hw)).trans (hc Q hQ)

theorem BodyConvexCount.packing {n : ℕ} {U : Fin n → Set Space} {w m : ℝ}
    (hw : 0 ≤ w) (hc : BodyConvexCount U w m) : BodyPacking U w m := by
  intro Q hQ
  have hroot : Real.sqrt (Set.ncard {i | U i ⊆ Q} : ℝ) ≤ Set.ncard {i | U i ⊆ Q} := by
    by_cases hz : Set.ncard {i | U i ⊆ Q} = 0
    · simp [hz]
    · have h1 : (1 : ℝ) ≤ Set.ncard {i | U i ⊆ Q} := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hroot hw)).trans (hc Q hQ)

/-- Balanced incidence counts transfer the original slab estimate to any enlarged
coarse bodies after the fixed contraction. -/
theorem coarse_body_slabs {δ l N D : ℝ} (hl : 0 ≤ l) (hN : 0 < N) (hD : 0 ≤ D)
    {n q : ℕ} (x v : Fin n → Space) (U : Fin q → Set Space) (R : Fin n → Fin q → Prop)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1)
    (hslab : SlabCount δ l n x v)
    (hlower : ∀ j, N ≤ (Set.ncard {i | R i j} : ℝ))
    (hupper : ∀ i, (Set.ncard {j | R i j} : ℝ) ≤ D)
    (hsize : (n : ℝ) ≤ (q : ℝ) * D * N)
    (hcontain : ∀ i j, R i j → coarseMap '' Tube δ (x i) (v i) ⊆ U j) :
    BodySlabCount U (256 * D ^ 2 * l) := by
  intro ν s r hν hr
  let V := ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - 32 * s| ≤ 32 * r}
  let P := fun i => Tube δ (x i) (v i) ⊆ V
  let S := fun j => U j ⊆ {p | |inner ℝ ν p - s| ≤ r}
  have himp : ∀ i j, S j → R i j → P i := by
    intro i j hj hij p hp
    refine ⟨hball i hp, ?_⟩
    have hh := hj (hcontain i j hij ⟨p, hp, rfl⟩)
    have h := (WangZahlLot.Obl.wz_nonflat_factored_improvement.smul_mem_slab_iff
      (by norm_num : (0 : ℝ) < 1 / 32) ν p s r).mp hh
    change |inner ℝ ν p - 32 * s| ≤ 32 * r
    convert h using 1 <;> ring
  have hcount := WangZahlLot.Obl.wz_nonflat_factored_improvement.bounded_incidence_count R P S hD
    (fun j _ => hlower j) hupper himp
  have hraw : (Set.ncard {i | P i} : ℝ) ≤ 256 * l * n * r := by
    have hh := (hslab ν (32 * s) (32 * r) hν (by positivity)).trans
      (mul_le_mul' le_rfl (WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hν
        (32 * s) (32 * r) (by positivity)))
    rw [← ENNReal.ofReal_mul (by positivity)] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    change (Set.ncard {i | P i} : ℝ) ≤ _ at hh'
    nlinarith only [hh']
  apply ENNReal.ofReal_le_ofReal
  change (Set.ncard {j | S j} : ℝ) ≤ (256 * D ^ 2 * l) * (q : ℝ) * r
  apply (mul_le_mul_iff_left₀ hN).mp
  have h1 := mul_le_mul_of_nonneg_left hraw hD
  have h2 := mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 256 * D * l * r)
  nlinarith only [hcount, h1, h2]

end WangZahlLot.Obl.wz_flat_factored_improvement
