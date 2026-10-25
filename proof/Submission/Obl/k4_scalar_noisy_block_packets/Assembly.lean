import Submission.Obl.k4_scalar_noisy_block_packets.PreparedPackets
import Submission.Obl.k4_scalar_noisy_block_packets.ProfileOptimizer
import Submission.Obl.k4_scalar_conditional_crop_worlds
import Submission.Obl.k4_scalar_crop_profile_transport

namespace Submission.Obl.k4_scalar_noisy_block_packets

open MeasureTheory Set Filter

lemma homogeneous_subsequence {N : ℕ → ℝ} {s V : ℝ}
    {μ : ℕ → Measure Inc} {F : ℝ → ℝ → ℝ}
    (h : Homogeneous N s V μ F) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    Homogeneous (N ∘ ψ) s V (μ ∘ ψ) F := by
  rcases h with ⟨g, G, hg, hG, ht, hT⟩
  refine ⟨(fun k => g (ψ k)), (fun k => G (ψ k)),
    (fun k r hr hrs => hg (ψ k) r hr hrs),
    (fun k r u hr hrs hu huV => hG (ψ k) r u hr hrs hu huV), ?_, ?_⟩
  · intro r τ hr hrs hτ
    obtain ⟨a, ha, he⟩ := ht r τ hr hrs hτ
    exact ⟨a, ha, hψ.tendsto_atTop.eventually he⟩
  · intro r u τ hr hrs hu huV hτ
    obtain ⟨a, ha, he⟩ := hT r u τ hr hrs hu huV hτ
    exact ⟨a, ha, hψ.tendsto_atTop.eventually he⟩

/-- The analytic split is used only to prepare the exact theorem's input. -/
theorem assembly (hselect : ProfileSelection) (hworlds : CropSelection)
    (htransport : CropTypicality) :
    ExactAngularPackets → ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) →
      Tendsto N atTop atTop → Subpower N K →
      ∀ d s m C S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C →
      0 < S → 0 < U → U < m →
      ∀ (c : ℕ → ℝ) (angular : Bool) (C₀ : ℝ) (F : ℝ → ℝ → ℝ)
        (M : ℕ) (H J : ℕ → ℕ)
        (b₀ : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
        (w : (k : ℕ) → Fin (H k) → ℝ)
        (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool),
        (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) →
        (∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) →
        ProfileShape d s m S U C₀ angular F →
        (∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
          N k ^ (C₀ - τ) ≤ c k ∧ c k ≤ N k ^ (C₀ + τ)) →
        Homogeneous N s (4 * (m + s + 1))
          (fun k => MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k)) F →
        ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
          NoisyOutput (N k) d s m (c k) ε angular
            (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k)) := by
  intro hexact N K hN hNt hK d s m C S U hd hd1 hs hsm hC hS hU hUm
    c angular C₀ F M H J b₀ w mark hcB htables hshape hc hhom ε hε
  let η := ε / 100
  have hη : 0 < η := div_pos hε (by norm_num)
  obtain ⟨L, u₀, d', S', U', he⟩ :=
    hselect d s m S U C₀ angular F hd hd1 hs hsm hS hU hUm hshape η hη
  obtain ⟨ψ, K', α, W, ω, ν, E, p, z, ρ, hψ, hK', hcrop, hfmt⟩ :=
    hworlds N K hN hNt hK m u₀ M H J b₀ w mark (hs.trans hsm)
      he.2.2.1 htables
  have hn' : ∀ k, 2 ≤ (N ∘ ψ) k := fun k => hN (ψ k)
  have hnt' : Tendsto (N ∘ ψ) atTop atTop := hNt.comp hψ.tendsto_atTop
  have hhom' : Homogeneous (N ∘ ψ) s (4 * (m + s + 1))
      (fun k => selected
        (MarkedPrior (N (ψ k) ^ (-m)) (H (ψ k)) (b₀ (ψ k)) (w (ψ k)))
        (MarkedEvent (H (ψ k)) (J (ψ k)) (mark (ψ k)))) F :=
    homogeneous_subsequence hhom hψ
  have htyp := htransport (N ∘ ψ) K' hn' hnt' hK'
    (fun k => MarkedPrior (N (ψ k) ^ (-m)) (H (ψ k)) (b₀ (ψ k)) (w (ψ k)))
    (fun k => MarkedEvent (H (ψ k)) (J (ψ k)) (mark (ψ k)))
    d s m S U C₀ η L u₀ d' S' U' α angular F hd hd1 hs hsm hη hshape he hhom'
    W ω ν E p z ρ hcrop hfmt
  have hout := lift_prepared hexact (N ∘ ψ) K' hn' hnt' hK'
    (fun k => MarkedPrior (N (ψ k) ^ (-m)) (H (ψ k)) (b₀ (ψ k)) (w (ψ k)))
    (fun k => MarkedEvent (H (ψ k)) (J (ψ k)) (mark (ψ k)))
    d s m C₀ η L u₀ d' S' U' α angular F (c ∘ ψ) hd hd1 hs hsm hη he
    (fun τ hτ => hψ.tendsto_atTop.eventually (hc τ hτ))
    W ω ν E p z ρ hcrop htyp ε hε (by dsimp [η]; linarith)
  rw [Filter.frequently_atTop] at hout ⊢
  intro n
  obtain ⟨k, hnk, hk⟩ := hout n
  refine ⟨ψ k, hnk.trans (hψ.id_le k), ?_⟩
  exact hk

/-- The frozen children specialize definitionally to the readable predicates above. -/
theorem from_children :
    ∀ (_h : ExactAngularPackets),
    ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop → Subpower N K →
      ∀ d s m C S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C →
      0 < S → 0 < U → U < m →
      ∀ (c : ℕ → ℝ) (angular : Bool) (C₀ : ℝ) (F : ℝ → ℝ → ℝ)
        (M : ℕ) (H J : ℕ → ℕ)
        (b₀ : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
        (w : (k : ℕ) → Fin (H k) → ℝ)
        (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool),
        (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) →
        (∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) →
        ProfileShape d s m S U C₀ angular F →
        (∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
          N k ^ (C₀ - τ) ≤ c k ∧ c k ≤ N k ^ (C₀ + τ)) →
        Homogeneous N s (4 * (m + s + 1))
          (fun k => MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k)) F →
        ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
          NoisyOutput (N k) d s m (c k) ε angular
            (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k)) := by
  exact assembly scalar_profile_selection
    Submission.k4_scalar_conditional_crop_worlds Submission.k4_scalar_crop_profile_transport

end Submission.Obl.k4_scalar_noisy_block_packets
