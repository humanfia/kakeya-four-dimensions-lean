/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/DiscrepancyBasics.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/DiscrepancyBasics.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Mathlib
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SheetJets
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingApply

/-! Discrepancy groups of paired matching sheets: dyadic discrepancy scales,
jet cubes and group labels. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open Set Metric MeasureTheory

/-- Uniform jet constants for degree-two matching sheets (see `exists_match_jet_constants`). -/
structure JetData where
  q : ℕ
  c : ℝ
  V : Finset (EuclideanSpace ℝ (Fin 3))
  B : ℕ → ℝ
  C₂ : ℝ
  hq : 1 ≤ q
  hc : 0 < c
  hV : ∀ v ∈ V, ‖v‖ = 1
  hB : ∀ m, 0 < B m
  hC₂ : 0 < C₂
  spec : ∀ φ ψ : EuclideanSpace ℂ (Fin 3) → ℂ, IsMatchSheet φ → IsMatchSheet ψ →
    (∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
      ∃ v ∈ V, ∃ j < q, c * ‖φ (emb y) - ψ (emb y)‖ ≤ |sheetJet φ v j - sheetJet ψ v j|) ∧
    (∀ A : ℝ, 0 < A → (∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
        ‖φ (emb y) - ψ (emb y)‖ ≤ A) →
      ∀ v ∈ V, ∀ j : ℕ, |sheetJet φ v j - sheetJet ψ v j| ≤ B j * A) ∧
    (∀ A : ℝ, 0 < A → (∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
        ‖φ (emb y) - ψ (emb y)‖ ≤ A) →
      ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 → ‖φ (emb y) - ψ (emb y)‖ ≤ C₂ * A)

theorem nonempty_jetData : Nonempty JetData := by
  obtain ⟨q, hq, c, hc, V, _, hV, B, hB, C₂, hC₂, spec⟩ := exists_match_jet_constants
  exact ⟨⟨q, c, V, B, C₂, hq, hc, hV, hB, hC₂, spec⟩⟩

/-! ### Discrepancy on the real half ball -/

lemma continuousOn_sheet_emb {φ : EuclideanSpace ℂ (Fin 3) → ℂ} (hφ : IsMatchSheet φ) :
    ContinuousOn (fun y : EuclideanSpace ℝ (Fin 3) => φ (emb y)) (closedBall 0 (1 / 2)) := by
  have hc : Continuous emb :=
    (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3).continuous
  apply hφ.2.1.continuousOn.comp hc.continuousOn
  intro y hy
  rw [mem_ball, dist_zero_right, norm_emb]
  have := mem_closedBall_zero_iff.mp hy
  linarith

/-- The sup norm of the difference of two sheets on the real closed half ball. -/
noncomputable def sheetDisc {ι : Type*} (φ : ι → EuclideanSpace ℂ (Fin 3) → ℂ) (i i' : ι) : ℝ :=
  sSup ((fun y : EuclideanSpace ℝ (Fin 3) => ‖φ i (emb y) - φ i' (emb y)‖) ''
    closedBall 0 (1 / 2))

section Disc

variable {ι : Type*} {φ : ι → EuclideanSpace ℂ (Fin 3) → ℂ}

lemma sheetDisc_bdd (hφ : ∀ i, IsMatchSheet (φ i)) (i i' : ι) :
    BddAbove ((fun y : EuclideanSpace ℝ (Fin 3) => ‖φ i (emb y) - φ i' (emb y)‖) ''
      closedBall 0 (1 / 2)) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)).bddAbove_image
  exact ((continuousOn_sheet_emb (hφ i)).sub (continuousOn_sheet_emb (hφ i'))).norm

lemma le_sheetDisc (hφ : ∀ i, IsMatchSheet (φ i)) (i i' : ι) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : ‖y‖ ≤ 1 / 2) : ‖φ i (emb y) - φ i' (emb y)‖ ≤ sheetDisc φ i i' :=
  le_csSup (sheetDisc_bdd hφ i i') ⟨y, mem_closedBall_zero_iff.mpr hy, rfl⟩

lemma exists_lt_sheetDisc (i i' : ι) {a : ℝ} (ha : a < sheetDisc φ i i') :
    ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧ a < ‖φ i (emb y) - φ i' (emb y)‖ := by
  have hne : ((fun y : EuclideanSpace ℝ (Fin 3) => ‖φ i (emb y) - φ i' (emb y)‖) ''
      closedBall 0 (1 / 2)).Nonempty :=
    ⟨_, ⟨0, by simp only [mem_closedBall, dist_self]; norm_num, rfl⟩⟩
  obtain ⟨b, ⟨y, hy, rfl⟩, hab⟩ := exists_lt_of_lt_csSup hne ha
  exact ⟨y, mem_closedBall_zero_iff.mp hy, hab⟩

lemma sheetDisc_nonneg (hφ : ∀ i, IsMatchSheet (φ i)) (i i' : ι) : 0 ≤ sheetDisc φ i i' :=
  (norm_nonneg _).trans (le_sheetDisc hφ i i' (y := 0) (by simp only [norm_zero]; norm_num))

end Disc

/-! ### Dyadic scales -/

/-- The dyadic scale `k` with `M₀ 2^k ≤ d < M₀ 2^(k+1)`, when `M₀ ≤ d`. -/
noncomputable def discScale (M₀ d : ℝ) : ℕ :=
  if h : 1 ≤ d / M₀ then Classical.choose (exists_nat_pow_near h one_lt_two) else 0

lemma discScale_spec {M₀ d : ℝ} (hM₀ : 0 < M₀) (hd : M₀ ≤ d) :
    M₀ * 2 ^ discScale M₀ d ≤ d ∧ d < M₀ * 2 ^ (discScale M₀ d + 1) := by
  have h1 : 1 ≤ d / M₀ := by rw [le_div_iff₀ hM₀]; linarith
  have hspec := Classical.choose_spec (exists_nat_pow_near h1 one_lt_two)
  simp only [discScale, h1, dite_true]
  constructor
  · have := hspec.1
    rw [le_div_iff₀ hM₀] at this
    linarith
  · have := hspec.2
    rw [div_lt_iff₀ hM₀] at this
    linarith

lemma discScale_le {M₀ d : ℝ} (hM₀ : 0 < M₀) (hd : M₀ ≤ d) {K : ℕ}
    (hK : d < M₀ * 2 ^ (K + 1)) : discScale M₀ d ≤ K := by
  have h := (discScale_spec hM₀ hd).1
  have h2 : (2 : ℝ) ^ discScale M₀ d < 2 ^ (K + 1) := by
    have := lt_of_le_of_lt h hK
    exact lt_of_mul_lt_mul_left this hM₀.le
  have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h2
  omega

/-! ### Jet cubes -/

/-- The cube of the jets of sheet `i` at spacing `c M₀ 2^k / 2`. -/
noncomputable def sheetCube {ι : Type*} (J : JetData) (φ : ι → EuclideanSpace ℂ (Fin 3) → ℂ)
    (M₀ : ℝ) (k : ℕ) (i : ι) : ↥J.V × Fin J.q → ℤ :=
  fun vj => ⌊sheetJet (φ i) vj.1 vj.2 / (J.c * (M₀ * 2 ^ k) / 2)⌋

lemma abs_sub_lt_of_floor_eq {a b s : ℝ} (hs : 0 < s) (h : ⌊a / s⌋ = ⌊b / s⌋) :
    |a - b| < s := by
  have ha1 := Int.floor_le (a / s)
  have ha2 := Int.lt_floor_add_one (a / s)
  have hb1 := Int.floor_le (b / s)
  have hb2 := Int.lt_floor_add_one (b / s)
  rw [h] at ha1 ha2
  have h1 : a / s - b / s < 1 := by linarith
  have h2 : b / s - a / s < 1 := by linarith
  rw [abs_lt]
  constructor
  · have : (b - a) / s < 1 := by rw [sub_div]; linarith
    rw [div_lt_one hs] at this
    linarith
  · have : (a - b) / s < 1 := by rw [sub_div]; linarith
    rwa [div_lt_one hs] at this

lemma abs_floor_sub_le {a b s K : ℝ} (hs : 0 < s) (h : |a - b| ≤ K * s) :
    |((⌊a / s⌋ - ⌊b / s⌋ : ℤ) : ℝ)| ≤ K + 1 := by
  have ha1 := Int.floor_le (a / s)
  have ha2 := Int.lt_floor_add_one (a / s)
  have hb1 := Int.floor_le (b / s)
  have hb2 := Int.lt_floor_add_one (b / s)
  have hab : |a / s - b / s| ≤ K := by
    rw [← sub_div, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact h
  rw [abs_le] at hab ⊢
  push_cast
  constructor <;> linarith [hab.1, hab.2]

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
