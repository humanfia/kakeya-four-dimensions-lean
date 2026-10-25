import Submission.Obl.k4_pair_anchor_jet_bins.Bins

namespace Submission.Obl.k4_pair_anchor_jet_bins

noncomputable section

/-- Only the discriminant and the second hidden derivative require a size bound. -/
def ScaleTest (A δ : ℝ) (P : Test) : Prop :=
  P.totalDegree ≤ 2 ∧
  |MvPolynomial.eval (0 : Fin 4 → ℝ)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ δ⁻¹ ∧
  (disc P).totalDegree ≤ 2 ∧ ∀ d, |(disc P).coeff d| ≤ A

def ScalePair (A δ q : ℝ) (P P' : Test) (z : R3)
    (zline : ℝ → R3) (wline : ℝ → ℝ) (t₀ : ℝ) (I : Set ℝ) : Prop :=
  A⁻¹ ≤ |MvPolynomial.eval (fun i => z i) (disc P)| ∧
  A⁻¹ ≤ |MvPolynomial.eval (fun i => z i) (disc P')| ∧
  ∃ f f' : E3 → ℂ,
    (∀ (R : Test) (F : E3 → ℂ), (R = P ∧ F = f) ∨ (R = P' ∧ F = f') →
      DifferentiableOn ℂ F (Metric.ball (emb z) (8 * A⁻¹)) ∧
      (∀ ζ ∈ Metric.ball (emb z) (8 * A⁻¹),
        MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => ζ i) (F ζ))
          (R.map (algebraMap ℝ ℂ)) = 0 ∧
        MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => ζ i) (F ζ))
          ((MvPolynomial.pderiv (3 : Fin 4) R).map (algebraMap ℝ ℂ)) ≠ 0) ∧
      ∀ z' ∈ Metric.ball z (8 * A⁻¹), (F (emb z')).im = 0) ∧
    ‖f (emb z) - (wline t₀ : ℂ)‖ ≤ δ * A ∧
    ‖f' (emb z) - (wline t₀ : ℂ)‖ ≤ δ * A ∧
    (∀ z' ∈ Metric.closedBall z (2 * A⁻¹),
      ‖f (emb z') - f' (emb z')‖ ≤ δ * A) ∧
    ∀ t ∈ I ∩ Set.Icc (t₀ - A⁻¹ / (100 * q)) (t₀ + A⁻¹ / (100 * q)),
      ‖(wline t : ℂ) - f (emb (zline t))‖ ≤ δ * A

/-- The analytic construction at the single scale `A = N^a`. -/
def ScaleKernel (Cs : ℕ) : Prop :=
  ∃ (J : ℕ) (CR CK CB A₀ : ℝ), 0 < CR ∧ 0 < CK ∧
  ∀ A δ q : ℝ, A₀ ≤ A → 0 < δ → δ ≤ 1 → 1 ≤ q →
  ∀ (P P' : Test) (z₀ α : R3) (σ : ℂ) (zline : ℝ → R3)
    (wline : ℝ → ℝ) (t₀ : ℝ) (I : Set ℝ),
  ScaleTest A δ P → ScaleTest A δ P' → ‖z₀‖ ≤ 1 / 8 →
  t₀ ∈ I → zline t₀ = z₀ → (∀ t ∈ I, ‖zline t - z₀‖ ≤ q * |t - t₀|) →
  ScalePair A δ q P P' z₀ zline wline t₀ I →
  α ∈ Metric.closedBall (0 : R3) (1 / 8) →
  σ ∈ Metric.closedBall (1 / 2 : ℂ) (1 / 4) →
  SafeFor (A ^ (-(Cs : ℝ))) (disc P) (disc P') z₀ α σ →
  ∃ β ∈ bins J (δ * A ^ CB) P α, ∃ β' ∈ bins J (δ * A ^ CB) P' α,
    (∀ i, |β i - β' i| ≤ 1) ∧
    ∀ R : Test, ScaleTest A δ R →
    A ^ (-(Cs : ℝ)) ≤ |MvPolynomial.eval (fun i => α i) (disc R)| →
    β ∈ bins J (δ * A ^ CB) R α → ∀ t ∈ I, |t - t₀| ≤ A ^ (-CR) / q →
    |MvPolynomial.eval (Fin.snoc (fun i => zline t i) (wline t)) R| ≤ δ * A ^ CK ∧
    |MvPolynomial.eval (Fin.snoc (fun i => zline t i) (wline t))
      (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ A ^ CK

theorem analyticKernel_of_scale (h : ∀ Cs : ℕ, 0 < Cs → ScaleKernel Cs) : AnalyticKernel := by
  intro Cs hCs
  obtain ⟨J, CR, CK, CB, A₀, hCR, hCK, hmain⟩ := h Cs hCs
  refine ⟨binDim J, CR, CK, (fun N a δ P α => bins J (δ * (N ^ a) ^ CB) P α),
    hCR, hCK, (fun N a δ P α => card_bins J _ P α), ?_⟩
  intro a ha M
  have hlarge : ∀ᶠ N : ℝ in Filter.atTop, 1 ≤ N ∧ A₀ ≤ N ^ a :=
    (Filter.eventually_ge_atTop 1).and ((tendsto_rpow_atTop ha).eventually_ge_atTop A₀)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨N₀, ?_⟩
  intro N δ q hN hδ hδ1 hq P P' z₀ α σ zline wline t₀ I hP hP' hz ht hzline hlip
    hpair hα hσ hsafe
  have hN1 : 1 ≤ N := (hN₀ N hN).1
  have hN0 : 0 < N := by linarith
  have hneg : N ^ (-a) = (N ^ a)⁻¹ := Real.rpow_neg hN0.le a
  have hSP : ScaleTest (N ^ a) δ P := ⟨hP.1, hP.2.2.1, hP.2.2.2⟩
  have hSP' : ScaleTest (N ^ a) δ P' := ⟨hP'.1, hP'.2.2.1, hP'.2.2.2⟩
  have hpair' : ScalePair (N ^ a) δ q P P' z₀ zline wline t₀ I := by
    simpa only [ScalePair, localPair, hneg] using hpair
  obtain ⟨β, hβ, β', hβ', hnear, hrep⟩ := hmain (N ^ a) δ q (hN₀ N hN).2 hδ hδ1 hq
    P P' z₀ α σ zline wline t₀ I hSP hSP' hz ht hzline hlip hpair' hα hσ hsafe
  refine ⟨β, hβ, β', hβ', hnear, ?_⟩
  intro R hR hdisc hbin t ht htime
  have hSR : ScaleTest (N ^ a) δ R := ⟨hR.1, hR.2.2.1, hR.2.2.2⟩
  have hpR : (N ^ a) ^ (-CR) = N ^ (-(CR * a)) := by
    rw [← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hpK : (N ^ a) ^ CK = N ^ (CK * a) := by
    rw [← Real.rpow_mul hN0.le]
    congr 1
    ring
  simpa only [hpK] using hrep R hSR hdisc hbin t ht (by simpa only [hpR] using htime)

end
end Submission.Obl.k4_pair_anchor_jet_bins
