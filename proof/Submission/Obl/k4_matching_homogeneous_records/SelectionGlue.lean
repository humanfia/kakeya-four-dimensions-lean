import Submission.Obl.k4_matching_homogeneous_records.Interfaces
import Submission.Obl.k4_matching_gap_regularization.Restriction

namespace Submission.Obl.k4_matching_homogeneous_records

open Set MeasureTheory

lemma cofinal_selected_records (selection : SelectionStatement)
    {J q : ℕ} {d : ℝ} {β : ℕ → ℝ}
    (hs : 0 ≤ d + radius J β 1)
    (hraw : ∀ η : ℝ, 0 < η → ∀ R : ℝ, 2 ≤ R →
      ∃ N : ℝ, R ≤ N ∧ RawRecords J d β q η N) :
    ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧
      ∃ u : ℕ → ℝ,
        ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧
          (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧
          u q ≤ d + radius J β 1 + ε) ∧ Records J d β q u ε N := by
  intro ε hε R hR
  let e : ℝ := ε / 4
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨η, hη, hηe, R₀, hR₀, hselect⟩ := selection q (d + radius J β 1) hs e he
  obtain ⟨N, hRN, hrawN⟩ := hraw η hη (max R R₀) (hR.trans (le_max_left _ _))
  have hN₂ : 2 ≤ N := hR.trans ((le_max_left _ _).trans hRN)
  have hN : 1 ≤ N := by linarith
  have hηε : η ≤ ε := by dsimp [e] at hηe; linarith
  have heε : e ≤ ε := by dsimp [e]; linarith
  rcases hrawN with ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S,
    hn₁, hn₂, hf₁, hf₂, hder₁, hder₂, hπ₁, hπ₂, hsum₁, hsum₂, hprob,
    hmarg₁, hmarg₂, hS, hSzero, hgood, hmono, hbounds, hF, hhist, hcount⟩
  have hnested (a b : ℕ) (hab : a ≤ b) (hb : b ≤ q)
      (x) (hx : x ∈ S) (y) (hy : y ∈ S) (hxy : F b x = F b y) :
      F a x = F a y := by
    apply (hhist a (hab.trans hb) x hx y hy).2
    intro v hv
    exact (hhist b hb x hx y hy).1 hxy v (hv.trans hab)
  obtain ⟨u, ν, T, hu, hνprob, hν, hTS, hT, hTzero, hucount, hudesc⟩ :=
    hselect N ((le_max_right _ _).trans hRN) _ μ F S hprob hS hSzero hF hnested hcount
  refine ⟨N, (le_max_left _ _).trans hRN, u,
    ⟨hu.1, hu.2.1, hu.2.2.trans (by linarith)⟩, ?_⟩
  refine ⟨n₁, n₂, f₁, f₂, π₁, π₂, ν, h, F, T, ?_⟩
  refine ⟨hn₁.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    hn₂.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hf₁, hf₂, ?_, ?_,
    hπ₁, hπ₂, hsum₁, hsum₂, hνprob, ?_, ?_, hT, hTzero, ?_, hmono, hbounds,
    ?_, ?_, ?_, ?_⟩
  · intro i j hj t ht
    exact (hder₁ i j hj t ht).trans (Real.rpow_le_rpow_of_exponent_le hN hηε)
  · intro i j hj t ht
    exact (hder₂ i j hj t ht).trans (Real.rpow_le_rpow_of_exponent_le hN hηε)
  · intro i E hE
    exact Submission.Obl.k4_matching_gap_regularization.marginal_power_loss hN (hπ₁ i) (by dsimp [e] at hηe ⊢; linarith)
      hν (hmarg₁ i E hE)
  · intro i E hE
    exact Submission.Obl.k4_matching_gap_regularization.marginal_power_loss hN (hπ₂ i) (by dsimp [e] at hηe ⊢; linarith)
      hν (hmarg₂ i E hE)
  · intro p hp
    have hg := hgood p (hTS hp)
    refine ⟨hg.1, hg.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), ?_⟩
    intro j hj hjJ
    refine ⟨(hg.2.2 j hj hjJ).1.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), ?_⟩
    intro hjβ
    exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans ((hg.2.2 j hj hjJ).2 hjβ)
  · intro k hk
    exact ⟨(hF k hk).1, (hF k hk).2.subset (Set.image_mono hTS)⟩
  · intro k hk x hx y hy
    exact hhist k hk x (hTS hx) y (hTS hy)
  · intro k hk
    exact (hucount k hk).trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  · intro a b hab hb x hx
    exact (hudesc a b hab hb x hx).trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))

lemma records_stable {J q : ℕ} {d : ℝ} {β : ℕ → ℝ}
    (u v : ℕ → ℝ) (ε δ N : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hN₂ : 2 ≤ N)
    (huv : ∀ k : ℕ, k ≤ q → |u k - v k| ≤ δ)
    (hu : Records J d β q u ε N) : Records J d β q v (ε + 2 * δ) N := by
  have hN : 1 ≤ N := by linarith
  have he : ε ≤ ε + 2 * δ := by linarith
  rcases hu with ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S,
    hn₁, hn₂, hf₁, hf₂, hder₁, hder₂, hπ₁, hπ₂, hsum₁, hsum₂, hprob,
    hmarg₁, hmarg₂, hS, hSzero, hgood, hmono, hbounds, hF, hhist, hcount, hdesc⟩
  refine ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, ?_⟩
  refine ⟨hn₁.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    hn₂.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hf₁, hf₂, ?_, ?_,
    hπ₁, hπ₂, hsum₁, hsum₂, hprob, ?_, ?_, hS, hSzero, ?_, hmono, hbounds,
    hF, hhist, ?_, ?_⟩
  · intro i j hj t ht
    exact (hder₁ i j hj t ht).trans (Real.rpow_le_rpow_of_exponent_le hN he)
  · intro i j hj t ht
    exact (hder₂ i j hj t ht).trans (Real.rpow_le_rpow_of_exponent_le hN he)
  · intro i E hE
    apply (hmarg₁ i E hE).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN he) (hπ₁ i)
  · intro i E hE
    apply (hmarg₂ i E hE).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN he) (hπ₂ i)
  · intro p hp
    have hg := hgood p hp
    refine ⟨hg.1, hg.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), ?_⟩
    intro j hj hjJ
    refine ⟨(hg.2.2 j hj hjJ).1.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), ?_⟩
    intro hjβ
    exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans ((hg.2.2 j hj hjJ).2 hjβ)
  · intro k hk
    exact (hcount k hk).trans (Real.rpow_le_rpow_of_exponent_le hN
      (by have := (abs_le.mp (huv k hk)).2; linarith))
  · intro a b hab hb x hx
    apply (hdesc a b hab hb x hx).trans
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hbu := (abs_le.mp (huv b hb)).2
    have hav := (abs_le.mp (huv a (hab.trans hb))).1
    linarith

end Submission.Obl.k4_matching_homogeneous_records
