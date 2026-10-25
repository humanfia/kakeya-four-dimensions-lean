/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/TerminalSupport.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.MeshProjection
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Finite terminal support from projected cells and bounded signal fibers. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Set

noncomputable section

theorem terminal_support_of_fiber_oscillation {Ω β : Type*}
    (S : Set Ω) (cell : Ω → β) (signal : Ω → ℝ) (F : Finset β)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hcover : ∀ p ∈ S, cell p ∈ F)
    (hosc : ∀ p ∈ S, ∀ q ∈ S, cell p = cell q → |signal p - signal q| ≤ M * a) :
    ∃ G : Finset (β × ℤ), (G.card : ℝ) ≤ (F.card : ℝ) * (2 * M + 2) ∧
      ∀ p ∈ S, (cell p, ⌊signal p / a⌋) ∈ G := by
  classical
  have hchoice (b : β) : ∃ B : Finset ℤ, (B.card : ℝ) ≤ 2 * M + 2 ∧
      ∀ p ∈ S, cell p = b → ⌊signal p / a⌋ ∈ B := by
    let T : Set ℝ := {x | ∃ p ∈ S, cell p = b ∧ signal p = x}
    have hdiam : ∀ x ∈ T, ∀ y ∈ T, dist x y ≤ M * a := by
      rintro x ⟨p, hp, hpc, rfl⟩ y ⟨q, hq, hqc, rfl⟩
      rw [Real.dist_eq]
      exact hosc p hp q hq (hpc.trans hqc.symm)
    obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      T (mul_nonneg hM ha.le) ha 0 hdiam
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · have heq : 2 * (M * a) / a + 2 = 2 * M + 2 := by field_simp
      simpa only [Set.ncard_eq_toFinset_card _ hfin, heq] using hcard
    · intro p hp hpc
      apply hfin.mem_toFinset.mpr
      exact ⟨signal p, ⟨p, hp, hpc, rfl⟩, by simp⟩
  choose B hB hmem using hchoice
  let G := F.biUnion (fun b => (B b).image (fun j => (b, j)))
  refine ⟨G, ?_, ?_⟩
  · calc
      (G.card : ℝ) ≤ ∑ b ∈ F, (((B b).image (fun j => (b, j))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ b ∈ F, ((B b).card : ℝ) := by
        exact_mod_cast Finset.sum_le_sum (fun b hb => Finset.card_image_le)
      _ ≤ ∑ _b ∈ F, (2 * M + 2) := Finset.sum_le_sum (fun b hb => hB b)
      _ = (F.card : ℝ) * (2 * M + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
  · intro p hp
    exact Finset.mem_biUnion.mpr ⟨cell p, hcover p hp,
      Finset.mem_image.mpr ⟨⌊signal p / a⌋, hmem (cell p) p hp rfl, rfl⟩⟩

/-- The artificial third coordinate costs only the slope bound. -/
theorem planar_moving_mesh_cover {sigma radius width L : ℝ}
    (hs : 0 < sigma) (hsr : sigma ≤ radius) (hL : 0 ≤ L)
    (hsw : sigma ≤ width) (hmove : L * sigma ≤ width)
    (time center velocity : ℝ) (hv : |velocity| ≤ L) :
    ∃ F : Finset (Fin 2 → ℤ),
      (F.card : ℝ) * sigma ^ 2 ≤ 600 * (L + 1) * radius * width ∧
      ∀ z : Fin 2 → ℝ, |z 0 - time| ≤ radius → |z 1 - (center + z 0 * velocity)| ≤ width →
        (fun i => ⌊z i / sigma⌋) ∈ F := by
  classical
  let c : Fin 2 → ℝ := ![center, 0]
  let v : Fin 2 → ℝ := ![velocity, 0]
  let w : Fin 2 → ℝ := ![width, (L + 1) * sigma]
  have hv' (i : Fin 2) : |v i| ≤ L := by fin_cases i <;> simp [v, hv, hL]
  have hw' (i : Fin 2) : sigma ≤ w i := by
    fin_cases i
    · exact hsw
    · dsimp [w]
      nlinarith [mul_nonneg hL hs.le]
  have hm' (i : Fin 2) : L * sigma ≤ w i := by
    fin_cases i
    · exact hmove
    · dsimp [w]
      nlinarith
  obtain ⟨G, hG, hcover⟩ := movingBox_mesh_volume hs hsr hL time c v w hv' hw' hm'
  let drop : (Fin 3 → ℤ) → Fin 2 → ℤ := fun q => ![q 0, q 1]
  let F := G.image drop
  refine ⟨F, ?_, ?_⟩
  · have hG' : (G.card : ℝ) * sigma ^ 2 ≤ 600 * (L + 1) * radius * width := by
      apply (mul_le_mul_iff_left₀ hs).mp
      convert hG using 1 <;> (try dsimp [w]) <;> ring
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le)
      (sq_nonneg sigma)).trans hG'
  · intro z ht hz
    let p : Fin 3 → ℝ := ![z 0, z 1, 0]
    have hp : p ∈ movingBox time radius c v w := by
      refine ⟨ht, ?_⟩
      intro i
      fin_cases i
      · exact hz
      · dsimp [p, c, v, w]
        simp only [mul_zero, zero_add, sub_zero, abs_zero]
        positivity
    apply Finset.mem_image.mpr
    refine ⟨baseMesh sigma p, hcover p hp, ?_⟩
    ext i
    fin_cases i <;> rfl

end

end Submission.Obl.k4_general_parent_projected_layers
