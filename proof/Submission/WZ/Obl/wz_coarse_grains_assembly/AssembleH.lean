-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.AssembleH.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.LocalCount

/-!
# Assembling the grains clause `H` from per-fibre grains

`assemble_H`: grains built fibre by fibre (for each coarse tube `k`, a disjoint family
`G k j ⊆ P (16 d) (ρ c) c (z k j) (e k j) ⊆ T ρ (y k) (w k)` partitioning the fibre
`{p | ∃ i ∈ S, f i = k, p ∈ Z i}`, dense, crossed end to end, with one common multiplicity
window `[m, 2m]`) glue together to the grains clause `H` with `a = 16 d` and `b = 0`.
The grains are indexed by `Fin (∑ k, L k)` through `finSigmaFinEquiv`; the local convex
count holds with `g = max 1 (∑ k, L k)` (`local_count_of_le`).
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open MeasureTheory

/-- Two distinct indices of the sigma type over the same fibre carry disjoint grains. -/
theorem assembleH_disjoint_aux {N : ℕ} {L : Fin N → ℕ} (G : (k : Fin N) → Fin (L k) → Set V)
    (hdisj : ∀ k (a a' : Fin (L k)), a ≠ a' → Disjoint (G k a) (G k a'))
    (s s' : (k : Fin N) × Fin (L k)) (hne : s ≠ s') (h1 : s.1 = s'.1) :
    Disjoint (G s.1 s.2) (G s'.1 s'.2) := by
  obtain ⟨k, a⟩ := s
  obtain ⟨k', a'⟩ := s'
  change k = k' at h1
  subst h1
  exact hdisj k a a' (fun hh => hne (by subst hh; rfl))

/-- The grains of fibre `k`, reindexed along an equivalence with the sigma type. -/
theorem assembleH_part_aux {N : ℕ} {L : Fin N → ℕ} (G : (k : Fin N) → Fin (L k) → Set V)
    {Lt : ℕ} (σ : Fin Lt ≃ (k : Fin N) × Fin (L k)) (k : Fin N) :
    {p | ∃ j, (σ j).1 = k ∧ p ∈ G (σ j).1 (σ j).2} = {p | ∃ a, p ∈ G k a} := by
  ext p
  constructor
  · rintro ⟨j, hj, hp⟩
    obtain ⟨⟨k', a⟩, hs⟩ : ∃ s, σ j = s := ⟨_, rfl⟩
    rw [hs] at hj hp
    change k' = k at hj
    change p ∈ G k' a at hp
    subst hj
    exact ⟨a, hp⟩
  · rintro ⟨a, hp⟩
    refine ⟨σ.symm ⟨k, a⟩, ?_, ?_⟩
    · rw [Equiv.apply_symm_apply]
    · rw [Equiv.apply_symm_apply]
      exact hp

/-- Per-fibre grains (common multiplicity window `[m, 2m]`) assemble to the grains clause `H`
with `a = 16 d`, `b = 0` and some `g > 0`. -/
theorem assemble_H {d h ρ c : ℝ} {n N : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N} {m : ℝ}
    (hd : 0 < d) (h16 : 16 * d ≤ ρ * c) (hρc : ρ * c ≤ c) (hc1 : c ≤ 1)
    (hfib : ∀ k : Fin N, ∃ (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (G : Fin L → Set V),
      (∀ j, M (G j) ∧ G j ⊆ P (16*d) (ρ*c) c (z j) (e j) ∧
        P (16*d) (ρ*c) c (z j) (e j) ⊆ T ρ (y k) (w k) ∧
        ι (e j (w k)) 0 ^ 2 + ι (e j (w k)) 1 ^ 2 ≤ (10*ρ) ^ 2) ∧
      (∀ j j', j ≠ j' → Disjoint (G j) (G j')) ∧
      {p | ∃ j, p ∈ G j} = {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i} ∧
      O (d ^ h * L * (16*d) * (ρ*c) * c) ≤ ∑ j, μ (G j) ∧
      (∀ p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
        q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ∈ Set.Icc m (2*m)) ∧
      (∀ i ∈ S, f i = k → ∀ j, (Z i ∩ G j).Nonempty →
        Z i ∩ P (16*d) (ρ*c) c (z j) (e j) ⊆ G j ∧
        (∀ p ∈ T d (x i) (v i) ∩ frontier (P (16*d) (ρ*c) c (z j) (e j)),
          |ι (e j (p - z j)) 2| = c/2) ∧
        ∀ t ∈ ({-c/2, c/2} : Set ℝ), ∃ p ∈ T d (x i) (v i) ∩ P (16*d) (ρ*c) c (z j) (e j),
          ι (e j (p - z j)) 2 = t)) :
    ∃ g : ℝ, 0 < g ∧ H d h n x v S Z ρ N y w f (16*d) c 0 g := by
  have hρc0 : 0 < ρ * c := by linarith
  have hc0 : 0 < c := by linarith
  choose L z e G hgeom hdisj hpart hdens hmult hcross using hfib
  obtain ⟨σ⟩ : Nonempty (Fin (∑ k, L k) ≃ (k : Fin N) × Fin (L k)) :=
    ⟨finSigmaFinEquiv.symm⟩
  -- the total mass of the grains, fibre by fibre
  have hsum : ∑ j, μ (G (σ j).1 (σ j).2) = ∑ k, ∑ a, μ (G k a) :=
    (Equiv.sum_comp σ (fun s : (k : Fin N) × Fin (L k) => μ (G s.1 s.2))).trans
      (Fintype.sum_sigma (fun s : (k : Fin N) × Fin (L k) => μ (G s.1 s.2)))
  have hnn : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ d ^ h * (L k : ℝ) * (16 * d) * (ρ * c) * c := by
    intro k _
    have := Real.rpow_nonneg hd.le h
    positivity
  have hdens' : O (d ^ h * ((∑ k, L k : ℕ) : ℝ) * (16 * d) * (ρ * c) * c) ≤
      ∑ j, μ (G (σ j).1 (σ j).2) := by
    calc O (d ^ h * ((∑ k, L k : ℕ) : ℝ) * (16 * d) * (ρ * c) * c)
        = O (∑ k, d ^ h * (L k : ℝ) * (16 * d) * (ρ * c) * c) := by
          rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      _ = ∑ k, O (d ^ h * (L k : ℝ) * (16 * d) * (ρ * c) * c) :=
          ENNReal.ofReal_sum_of_nonneg hnn
      _ ≤ ∑ k, ∑ a, μ (G k a) := Finset.sum_le_sum (fun k _ => hdens k)
      _ = ∑ j, μ (G (σ j).1 (σ j).2) := hsum.symm
  refine ⟨max 1 ((∑ k, L k : ℕ) : ℝ), lt_of_lt_of_le one_pos (le_max_left _ _),
    ∑ k, L k, fun j => z (σ j).1 (σ j).2, fun j => e (σ j).1 (σ j).2,
    fun j => G (σ j).1 (σ j).2, fun j => (σ j).1, m, ?_⟩
  beta_reduce
  refine ⟨by linarith, h16, hρc, hc1, fun j => hgeom (σ j).1 (σ j).2,
    fun j j' hne hγ => assembleH_disjoint_aux G hdisj (σ j) (σ j') (σ.injective.ne hne) hγ,
    fun k => (assembleH_part_aux G σ k).trans (hpart k), hdens',
    fun k p hp => hmult k p hp, fun i hi j hfj hne => hcross (σ j).1 i hi hfj (σ j).2 hne,
    hc0.le, ?_⟩
  exact local_count_of_le (by linarith) hρc0.le hc0.le (fun j => z (σ j).1 (σ j).2)
    (fun j => e (σ j).1 (σ j).2) (le_max_right _ _)

end WangZahlLot.Obl.wz_coarse_grains_assembly
