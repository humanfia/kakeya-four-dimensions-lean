-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RealCoverAlgebra.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.RadiusTransfer

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- An upper bound for a finite real set's external covering number. -/
def RealCoverBound (δ : ℝ) (A : Finset ℝ) (M : ℝ) : Prop :=
  ∃ (m : ℕ) (cc : Fin m → ℝ), Covers δ (↑A : Set ℝ) cc ∧ (m : ℝ) ≤ M

theorem RealCoverBound.nonneg {δ M : ℝ} {A : Finset ℝ} (h : RealCoverBound δ A M) : 0 ≤ M := by
  obtain ⟨m, cc, hc, hm⟩ := h
  exact (Nat.cast_nonneg m).trans hm

theorem RealCoverBound.mono {δ M N : ℝ} {A B : Finset ℝ}
    (h : RealCoverBound δ B M) (hAB : A ⊆ B) (hMN : M ≤ N) : RealCoverBound δ A N := by
  obtain ⟨m, cc, hc, hm⟩ := h
  exact ⟨m, cc, hc.mono_set hAB, hm.trans hMN⟩

theorem Covers.real_union {δ : ℝ} {A B : Set ℝ} {m n : ℕ}
    {ca : Fin m → ℝ} {cb : Fin n → ℝ} (ha : Covers δ A ca) (hb : Covers δ B cb) :
    Covers δ (A ∪ B) (fun i : Fin (m + n) => Sum.elim ca cb (finSumFinEquiv.symm i)) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ha hx)
    exact Set.mem_iUnion.mpr ⟨finSumFinEquiv (Sum.inl i), by simpa using hi⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hb hx)
    exact Set.mem_iUnion.mpr ⟨finSumFinEquiv (Sum.inr i), by simpa using hi⟩

theorem RealCoverBound.union {δ M N : ℝ} {A B : Finset ℝ}
    (ha : RealCoverBound δ A M) (hb : RealCoverBound δ B N) :
    RealCoverBound δ (A ∪ B) (M + N) := by
  classical
  obtain ⟨m, ca, hca, hm⟩ := ha
  obtain ⟨n, cb, hcb, hn⟩ := hb
  refine ⟨m + n, fun i => Sum.elim ca cb (finSumFinEquiv.symm i), ?_, ?_⟩
  · simpa only [Finset.coe_union] using Covers.real_union hca hcb
  · push_cast
    exact add_le_add hm hn

theorem Covers.real_scale {δ u : ℝ} {A : Set ℝ} {m : ℕ} {cc : Fin m → ℝ}
    (hc : Covers δ A cc) :
    Covers (|u| * δ) ((fun x : ℝ => u * x) '' A) (fun i => u * cc i) := by
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc ha)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  change dist (u * a) (u * cc i) ≤ |u| * δ
  simpa only [Real.dist_eq, ← mul_sub, abs_mul] using
    mul_le_mul_of_nonneg_left hi (abs_nonneg u)

theorem RealCoverBound.scale_contract {δ M u : ℝ} {A : Finset ℝ}
    (hδ : 0 ≤ δ) (hu : |u| ≤ 1) (h : RealCoverBound δ A M) :
    RealCoverBound δ (A.image (fun x => u * x)) M := by
  classical
  obtain ⟨m, cc, hc, hm⟩ := h
  refine ⟨m, fun i => u * cc i, ?_, hm⟩
  have hs := Covers.real_scale (u := u) hc
  have hr : |u| * δ ≤ δ := by nlinarith
  simpa only [Finset.coe_image] using hs.mono_radius hr

theorem RealCoverBound.scale {δ M u U : ℝ} {A : Finset ℝ}
    (hδ : 0 < δ) (hU : 1 ≤ U) (hu : |u| ≤ U) (h : RealCoverBound δ A M) :
    RealCoverBound δ (A.image (fun x => u * x)) (3 * U * M) := by
  classical
  obtain ⟨m, cc, hc, hm⟩ := h
  have hs : Covers (U * δ) (↑(A.image (fun x => u * x)) : Set ℝ) (fun i => u * cc i) := by
    simpa only [Finset.coe_image] using
      (Covers.real_scale (u := u) hc).mono_radius (mul_le_mul_of_nonneg_right hu hδ.le)
  obtain ⟨n, centers, hcov, hn⟩ := hs.refine_radius hδ (by nlinarith)
  refine ⟨n, centers, hcov, ?_⟩
  have hid : U * δ / δ = U := mul_div_cancel_right₀ U hδ.ne'
  rw [hid] at hn
  nlinarith [mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 3 * U)]

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
