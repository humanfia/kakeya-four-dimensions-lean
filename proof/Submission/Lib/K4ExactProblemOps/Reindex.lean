import Submission.Lib.K4ExactProblemOps.Transfer

/-!
# Reindexing exact problems

An exact problem is a sequence indexed by `k`.  Along any reindexing `φ` tending to
infinity (a subsequence, a shift) the problem stays valid, and a terminal system of
the reindexed problem is one of the original problem.  A shift `k ↦ k + k₀` changes
nothing at all: the horizon is unchanged.
-/

noncomputable section

namespace Submission.Lib.K4ExactProblemOps

open MeasureTheory Filter

section

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {f : ℝ → ℝ} {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}

/-- A valid problem stays valid along any reindexing tending to infinity. -/
theorem prob_reindex (hp : prob N K L d S η W ω ν E P B f g G) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    prob (fun k => N (φ k)) (fun k => K (φ k)) L d S η (fun k => W (φ k))
      (fun k => ω (φ k)) (fun k => ν (φ k)) (fun k => E (φ k)) (fun k => P (φ k))
      (fun k => B (φ k)) f (fun k => g (φ k)) (fun k => G (φ k)) := by
  obtain ⟨hN2, hNtend, ⟨hK1, hKε⟩, hL, hd, hd1, hS, hη, ⟨M, D, hMD⟩, hg, hG, hf, htyp,
    hcap, hang⟩ := hp
  refine ⟨fun k => hN2 (φ k), hNtend.comp hφ,
    ⟨fun k => hK1 (φ k), fun ε hε => hφ.eventually (hKε ε hε)⟩, hL, hd, hd1, hS, hη,
    ⟨M, D, fun k => hMD (φ k)⟩, fun k => hg (φ k), fun k => hG (φ k), hf, ?_, hcap, ?_⟩
  · intro r τ hr hrL hτ
    obtain ⟨c, hc, hev⟩ := htyp r τ hr hrL hτ
    exact ⟨c, hc, hφ.eventually hev⟩
  · intro u τ hu huL hτ
    obtain ⟨c, hc, hev⟩ := hang u τ hu huL hτ
    exact ⟨c, hc, hφ.eventually hev⟩

end

section

variable {N K : ℕ → ℝ} {L : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}

/-- A terminal system along a reindexing tending to infinity is one of the original
problem. -/
theorem term_of_term_reindex (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) {h : ℝ}
    (ht : term (fun k => N (φ k)) (fun k => K (φ k)) L (fun k => W (φ k))
      (fun k => ω (φ k)) (fun k => ν (φ k)) (fun k => E (φ k)) (fun k => B (φ k)) f h) :
    term N K L W ω ν E B f h := by
  obtain ⟨M, D, hMD⟩ := ht
  exact ⟨M, D, fun ε hε => hφ.frequently (hMD ε hε)⟩

/-- Frequent events persist under a shift of the index. -/
theorem frequently_shift {p : ℕ → Prop} (k₀ : ℕ) (h : ∃ᶠ k in atTop, p k) :
    ∃ᶠ k in atTop, p (k + k₀) := by
  rw [frequently_atTop] at h ⊢
  intro a
  obtain ⟨b, hb, hpb⟩ := h (a + k₀)
  refine ⟨b - k₀, by omega, ?_⟩
  rwa [Nat.sub_add_cancel (by omega)]

theorem term_shift (k₀ : ℕ) {h : ℝ} (ht : term N K L W ω ν E B f h) :
    term (fun k => N (k + k₀)) (fun k => K (k + k₀)) L (fun k => W (k + k₀))
      (fun k => ω (k + k₀)) (fun k => ν (k + k₀)) (fun k => E (k + k₀))
      (fun k => B (k + k₀)) f h := by
  obtain ⟨M, D, hMD⟩ := ht
  exact ⟨M, D, fun ε hε => frequently_shift k₀ (hMD ε hε)⟩

theorem term_shift_iff (k₀ : ℕ) (h : ℝ) :
    term (fun k => N (k + k₀)) (fun k => K (k + k₀)) L (fun k => W (k + k₀))
      (fun k => ω (k + k₀)) (fun k => ν (k + k₀)) (fun k => E (k + k₀))
      (fun k => B (k + k₀)) f h ↔ term N K L W ω ν E B f h :=
  ⟨term_of_term_reindex (fun k => k + k₀) (tendsto_add_atTop_nat k₀), term_shift k₀⟩

/-- A shift of the index does not change the horizon. -/
theorem H_shift (k₀ : ℕ) :
    H (fun k => N (k + k₀)) (fun k => K (k + k₀)) L (fun k => W (k + k₀))
      (fun k => ω (k + k₀)) (fun k => ν (k + k₀)) (fun k => E (k + k₀))
      (fun k => B (k + k₀)) f = H N K L W ω ν E B f := by
  unfold H
  congr 1
  ext h
  exact term_shift_iff k₀ h

end

end Submission.Lib.K4ExactProblemOps
