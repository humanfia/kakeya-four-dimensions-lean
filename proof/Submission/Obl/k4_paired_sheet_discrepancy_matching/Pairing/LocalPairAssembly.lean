/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/LocalPairAssembly.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/LocalPairAssembly.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.PolynomialSheets

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MvPolynomial Set Metric

/-- Assemble the exact frozen local-pair predicate from the explicit quadratic
sheets. Pair-dependent analytic choices stay in the pair mask. -/
theorem localPair_of_simpleSheets {Nk a δv q : ℝ}
    {P P' : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) (hP' : P'.totalDegree ≤ 2)
    {σ σ' : ℝ} (hσ : σ ^ 2 = 1) (hσ' : σ' ^ 2 = 1)
    {z : EuclideanSpace ℝ (Fin 3)} {zline : ℝ → EuclideanSpace ℝ (Fin 3)}
    {wline : ℝ → ℝ} {t₀ : ℝ} {I : Set ℝ}
    (hD : Nk ^ (-a) ≤ |eval (fun i => z i) (disc P)|)
    (hD' : Nk ^ (-a) ≤ |eval (fun i => z i) (disc P')|)
    (hdisc : ∀ ζ ∈ ball (emb z) (8 * Nk ^ (-a)),
      0 < (eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ))).re)
    (hdisc' : ∀ ζ ∈ ball (emb z) (8 * Nk ^ (-a)),
      0 < (eval (fun i => ζ i) ((disc P').map (algebraMap ℝ ℂ))).re)
    (hmap : ∀ x ∈ ball z (8 * Nk ^ (-a)), emb x ∈ ball (emb z) (8 * Nk ^ (-a)))
    (hnear : ‖simpleSheet P σ (emb z) - (wline t₀ : ℂ)‖ ≤ δv * Nk ^ a)
    (hnear' : ‖simpleSheet P' σ' (emb z) - (wline t₀ : ℂ)‖ ≤ δv * Nk ^ a)
    (hagree : ∀ z' ∈ closedBall z (2 * Nk ^ (-a)),
      ‖simpleSheet P σ (emb z') - simpleSheet P' σ' (emb z')‖ ≤ δv * Nk ^ a)
    (hfit : ∀ t ∈ I ∩ Icc (t₀ - Nk ^ (-a) / (100 * q)) (t₀ + Nk ^ (-a) / (100 * q)),
      ‖(wline t : ℂ) - simpleSheet P σ (emb (zline t))‖ ≤ δv * Nk ^ a) :
    localPair Nk a δv q P P' z zline wline t₀ I := by
  obtain ⟨hF, hroot, hreal⟩ := simpleSheet_spec P hP σ hσ _ hdisc
  obtain ⟨hF', hroot', hreal'⟩ := simpleSheet_spec P' hP' σ' hσ' _ hdisc'
  refine ⟨hD, hD', simpleSheet P σ, simpleSheet P' σ', ?_, hnear, hnear', hagree, hfit⟩
  intro R F h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hF, hroot, fun x hx => hreal x (hmap x hx)⟩
  · exact ⟨hF', hroot', fun x hx => hreal' x (hmap x hx)⟩

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
