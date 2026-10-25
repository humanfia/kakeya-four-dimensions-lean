import Submission.Obl.k4_coarsened_outer_horizon_composition.Lists
import Submission.Obl.k4_coarsened_outer_horizon_composition.FormatBudget
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set

noncomputable def prunedExponent (M Mb : ℕ) (r : ℝ) : ℕ :=
  (M + 1) + (M + Mb + ⌈r⌉₊ + 2) + 12

/-- Install short lists in an entire chart system at one sample. The assignments,
time blocks and geometric data stay fixed; only the selected incidences are pruned. -/
theorem pruned_chart_system {N κ θ r : ℝ} {W C T M D Mb : ℕ}
    (hN : 2 ≤ N) (hκ : 1 ≤ κ) (hκθ : κ ≤ θ)
    (B : Fin W → ℝ) (hB : ∀ w, 0 < B w) (hBmax : ∀ w, B w ≤ N ^ Mb)
    (E : Fin W → Set Inc) (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T)) (a u : Fin C → E2)
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → MvPolynomial (Fin 4) ℝ)
    (A : Fin C → Set Line) (F : Fin C → Set Inc) (ex : Fin C → Prop)
    (hC : (C : ℝ) ≤ N ^ M)
    (hc : ∀ b, chart N M D κ T ((j b : ℕ) : ℝ) r (B (γ b)) (E (γ b))
      (a b) (u b) (Q b) (R b) (A b) (F b) (ex b)) :
    let Cr := fun b => crossing κ (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) (δ N r / B (γ b)) (B (γ b))
      (a b) (u b) (Q b) (R b)
    ∃ (F' : Fin C → Set Inc) (lst : Fin W → Obs → Finset (Fin C)),
      (∀ b, F' b ⊆ F b) ∧ (∀ w o, ((lst w o).card : ℝ) ≤ θ) ∧
      (∀ b, chart N (prunedExponent M Mb r) (max D 4) θ T ((j b : ℕ) : ℝ) r
        (B (γ b)) (E (γ b)) (a b) (u b) (Q b) (R b) (A b) (F' b)
        (∀ p ∈ F' b, b ∈ lst (γ b) (obs (B (γ b)) (δ N r) p))) ∧
      (∀ b, F b ⊆ F' b ∪ (F b ∩ {p | ENNReal.ofReal θ <
        crossCount (Finset.univ.filter (fun b' => γ b' = γ b)) Cr
          (obs (B (γ b)) (δ N r) p)})) := by
  dsimp only
  let Cr := fun b => crossing κ (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T)
    ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) (δ N r / B (γ b)) (B (γ b))
    (a b) (u b) (Q b) (R b)
  let bins := polynomialBins N (M + Mb + ⌈r⌉₊ + 2)
  let F' := fun b => F b ∩ envelopeGood γ Cr θ bins (γ b) (B (γ b)) (δ N r)
  let lst := shortEnvelopeList γ Cr θ
  have hN1 : 1 ≤ N := by linarith
  have hκ0 : 0 < κ := by linarith
  have hθ : 0 ≤ θ := by linarith
  have hδ : 0 < δ N r := by unfold δ; positivity
  have hCr : ∀ b, MeasurableSet (Cr b) := fun b => measurableSet_crossing ..
  have hbin (b) (p) (hp : p ∈ F b) : (obs (B (γ b)) (δ N r) p).2 ∈ bins := by
    rcases hc b with ⟨_, _, _, _, _, _, _, _, _, hwhole, hsel, _⟩
    have hpA := (hsel p hp).2.1
    have ht : p.2 ∈ Icc (0 : ℝ) 1 := (hE _ (hsel p hp).1).2
    exact native_bin_mem_polynomialBins hN (hB _) (hBmax _) p.1 p.2 ht
      (hwhole p.1 hpA).2.1
  have hcross (b) (p) (hp : p ∈ F b) : obs (B (γ b)) (δ N r) p ∈ Cr b := by
    rcases hc b with ⟨_, _, _, _, hR, _, _, _, _, hwhole, hsel, _⟩
    obtain ⟨_, hpA, ht, hd⟩ := hsel p hp
    obtain ⟨hs, hv, hd', hc'⟩ := (hwhole p.1 hpA).2.2 p.2 ht
    exact obs_mem_crossing hκ0 hδ (hB _) (a b) (u b) (Q b) (R b) hR p ht hs hv hd' hc' hd
  have hCrfmt (b) (n : ℤ) :
      fmt 3 9 2 {z : Fin 3 → ℝ | (WithLp.toLp 2 z, n) ∈ Cr b} := by
    rcases hc b with ⟨_, _, _, _, hR, _⟩
    exact format_crossing_bin hκ0.le (div_pos hδ (hB _)).le _ _ _ (a b) (u b) (Q b) (R b) hR n
  refine ⟨F', lst, fun _ => inter_subset_left, shortEnvelopeList_card γ Cr hθ, ?_, ?_⟩
  · intro b
    have hlarge : chart N (prunedExponent M Mb r) (max D 4) θ T ((j b : ℕ) : ℝ) r
        (B (γ b)) (E (γ b)) (a b) (u b) (Q b) (R b) (A b) (F b) True :=
      Submission.Obl.k4_quadratic_atlas_normalization.chart_mono hN1
        (by unfold prunedExponent; omega) (le_max_left _ _) hκ0 hκθ (hB _).le
        (hc b) (fun _ => trivial)
    have hFfmt (i : ℕ) : fmt 7 (N ^ prunedExponent M Mb r) (max D 4)
        {z : Fin 7 → ℝ | ((i, fun e => z e.castSucc), z 6) ∈ F' b} := by
      rcases hc b with ⟨_, _, _, _, _, _, _, _, hfmt, _⟩
      have hcut := fmt_native_envelope_cut γ Cr 9 hCrfmt (γ b) θ bins (B (γ b)) (δ N r)
      have hinter := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter (hfmt i).2 hcut
      have heq : {z : Fin 7 → ℝ | ((i, fun e => z e.castSucc), z 6) ∈ F' b} =
          {z : Fin 7 → ℝ | ((i, fun e => z e.castSucc), z 6) ∈ F b} ∩
          {z : Fin 7 → ℝ | (incidentObs (B (γ b)) (δ N r) z).2 ∈ bins ∧
            ((envelopeList γ Cr (γ b) (incidentObs (B (γ b)) (δ N r) z)).card : ℝ) ≤ θ} := by
        ext z
        rfl
      rw [heq]
      exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono hinter
        (native_cut_format_budget hN M Mb ⌈r⌉₊ hC) le_rfl
    rcases hlarge with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7,
      h8.inter (measurableSet_envelopeGood γ Cr hCr hθ bins (γ b) (B (γ b)) (δ N r)),
      (fun i => ⟨(h9 i).1, hFfmt i⟩), h10, (fun p hp => h11 p hp.1), ?_⟩
    intro p hp
    exact mem_shortEnvelopeList γ Cr hp.2.2 (hcross b p hp.1)
  · intro b p hp
    by_cases hcount : ((envelopeList γ Cr (γ b) (obs (B (γ b)) (δ N r) p)).card : ℝ) ≤ θ
    · exact Or.inl ⟨hp, hbin b p hp, hcount⟩
    · refine Or.inr ⟨hp, ?_⟩
      change ENNReal.ofReal θ < crossCount (Finset.univ.filter (fun b' => γ b' = γ b)) Cr
        (obs (B (γ b)) (δ N r) p)
      exact lt_of_not_ge (fun h => hcount ((envelope_card_le_iff γ Cr _ _ hθ).mpr h))

end Submission.Obl.k4_coarsened_outer_horizon_composition
