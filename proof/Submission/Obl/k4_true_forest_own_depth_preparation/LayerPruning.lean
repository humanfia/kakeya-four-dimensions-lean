import Submission.Obl.k4_true_forest_own_depth_preparation.Model
import Submission.Obl.k4_coarsened_outer_horizon_composition.PrunedSystem
import Submission.Obl.k4_coarsened_outer_horizon_composition.SamplePruning

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- The accepted one-layer preparation works for any finite label type.  It also
records the actual mass lost from each original selected incidence set. -/
theorem prune_finite_layer {α : Type*} [Fintype α]
    {N κ θ r fL τ c₀ : ℝ} {W T M D Mb : ℕ}
    (hN : 2 ≤ N) (hκ : 1 ≤ κ) (hκθ : κ ≤ θ)
    (ω : Fin W → ℝ) (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (ν : Fin W → Measure Line) (hν : ∀ w, IsProbabilityMeasure (ν w))
    (E : Fin W → Set Inc) (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (B : Fin W → ℝ) (hB : ∀ w, 0 < B w) (hBmax : ∀ w, B w ≤ N ^ Mb)
    (g : Fin W → Obs → ENNReal) (hg : ∀ w, Measurable (g w))
    (hlaw : ∀ w, (selected (ν w) (E w)).map (obs (B w) (δ N r)) =
      (volume.prod Measure.count).withDensity (g w))
    (γ : α → Fin W) (j : α → Fin (2 ^ T)) (a u : α → E2)
    (Q : α → Matrix (Fin 2) (Fin 2) ℝ) (R : α → MvPolynomial (Fin 4) ℝ)
    (A : α → Set Line) (F : α → Set Inc)
    (hC : (Fintype.card α : ℝ) ≤ N ^ M)
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hc : ∀ b, chart N M D κ T ((j b : ℕ) : ℝ) r (B (γ b)) (E (γ b))
      (a b) (u b) (Q b) (R b) (A b) (F b)
      (ENNReal.ofReal (N ^ (-fL) * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
        ((ν (γ b)).prod volume) (F b)))
    (htyp : ∑ w, ENNReal.ofReal (ω w) * selected (ν w) (E w)
      {p | ENNReal.ofReal (N ^ (-fL + τ)) < g w (obs (B w) (δ N r) p)} ≤
      ENNReal.ofReal (N ^ (-c₀))) :
    ∃ (F' : α → Set Inc) (lst : Fin W → Obs → Finset α),
      (∀ b, F' b ⊆ F b) ∧ (∀ w o, ((lst w o).card : ℝ) ≤ θ) ∧
      (∀ b, chart N (prunedExponent M Mb r) (max D 4) θ T ((j b : ℕ) : ℝ) r
        (B (γ b)) (E (γ b)) (a b) (u b) (Q b) (R b) (A b) (F' b)
        (∀ p ∈ F' b, b ∈ lst (γ b) (obs (B (γ b)) (δ N r) p))) ∧
      (∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b \ F' b)) ≤
        ENNReal.ofReal (2 * N ^ (-c₀) + 1024 * κ ^ 5 * N ^ τ / θ) := by
  classical
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hd : ∀ b b' : Fin (Fintype.card α), b ≠ b' → γ (e b) = γ (e b') →
      j (e b) = j (e b') → Disjoint (A (e b)) (A (e b')) := by
    intro b b' hne
    exact hdisj _ _ (fun he => hne (e.injective he))
  obtain ⟨F₁, lst₁, hsub, hlist, hchart, hcover⟩ :=
    pruned_chart_system hN hκ hκθ B hB hBmax E hE (γ ∘ e) (j ∘ e)
      (a ∘ e) (u ∘ e) (Q ∘ e) (R ∘ e) (A ∘ e) (F ∘ e)
      (fun b => ENNReal.ofReal (N ^ (-fL) * |(Q (e b)).det| /
        ((2 : ℝ) ^ T * κ)) ≤ ((ν (γ (e b))).prod volume) (F (e b))) hC
      (fun b => hc (e b))
  let F' : α → Set Inc := fun b => F₁ (e.symm b)
  let lst : Fin W → Obs → Finset α := fun w o => (lst₁ w o).map e.toEmbedding
  refine ⟨F', lst, ?_, ?_, ?_, ?_⟩
  · intro b
    simpa only [F', Equiv.apply_symm_apply, Function.comp_apply] using hsub (e.symm b)
  · intro w o
    simpa only [lst, Finset.card_map] using hlist w o
  · intro b
    have h := hchart (e.symm b)
    dsimp only [Function.comp_apply] at h
    simp only [Equiv.apply_symm_apply] at h
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hx⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
    intro p hp
    exact Finset.mem_map.mpr ⟨e.symm b, hx p hp, e.apply_symm_apply b⟩
  · have hθ : 0 < θ := lt_of_lt_of_le (by linarith : 0 < κ) hκθ
    have hdel := sample_pruning_loss hN hκ hθ ω hω0 hω1 ν hν E hE B hB g hg hlaw
      (γ ∘ e) (j ∘ e) (a ∘ e) (u ∘ e) (Q ∘ e) (R ∘ e) (A ∘ e) (F ∘ e)
      hd (fun b => hc (e b)) htyp
    rw [← e.sum_comp (fun b => ENNReal.ofReal (ω (γ b)) *
      ((ν (γ b)).prod volume) (F b \ F' b))]
    apply le_trans (Finset.sum_le_sum fun b _ => ?_) hdel
    apply mul_le_mul le_rfl (measure_mono ?_) zero_le zero_le
    intro p hp
    rcases hcover b hp.1 with hkeep | hremove
    · exact False.elim (hp.2 (by simpa only [F', Equiv.symm_apply_apply] using hkeep))
    · exact hremove

end Submission.Obl.k4_true_forest_own_depth_preparation
