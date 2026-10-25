import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.SingleDepthInterface
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FiniteLayerSequence
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.CommonLayerFloors
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.SimultaneousNumerics

set_option maxHeartbeats 2000000

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

open MeasureTheory Set Filter
open scoped ENNReal

/-- Universality over prepared inputs permits finite sequential depth requests.
Only a vanishing loss is used when a retained law becomes the next input. -/
theorem engineAtCount_of_single (d κ ℓ S U e₀ u sMax : ℝ)
    (hsingle : EngineAt1 d κ ℓ S U e₀ u sMax) :
    ∀ m : ℕ, EngineAtCount d κ ℓ S U e₀ u sMax m := by
  classical
  intro m
  induction m with
  | zero =>
    intro N K hN hNt hK α _ ν μ ρ π b P T n j A B c F h1 h2 h3 h4 s hs ε hε
    filter_upwards [hK.2 ε hε] with k hk
    have hNp : 0 < N k := by linarith [hN k]
    have hi : (N k ^ ε)⁻¹ ≤ (K k)⁻¹ :=
      inv_anti₀ (by linarith [hK.1 k]) hk
    have hmass : ENNReal.ofReal (N k ^ (-ε)) ≤ ρ k univ := by
      obtain ⟨-, -, -, -, -, -, hm, -⟩ := h1 k
      rw [Real.rpow_neg hNp.le]
      exact (ENNReal.ofReal_le_ofReal hi).trans hm
    refine ⟨⟨ρ k, (fun _ => 0), (fun _ i => i.elim0),
      (fun _ i => i.elim0), (fun _ i => i.elim0)⟩, le_rfl, hmass, ?_⟩
    intro r
    exact r.elim0
  | succ m ih =>
    intro N K hN hNt hK α _ ν μ ρ π b P T n j A B c F h1 h2 h3 h4 s hs ε hε
    let δ₀ := ε / 10
    have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
    have hδ₀ε : δ₀ ≤ ε := by dsimp [δ₀]; linarith
    have hN1 : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
    have hNp : ∀ k, 0 < N k := fun k => by linarith [hN k]
    let tail : Fin m → ℝ := fun r => s r.succ
    have htail : ∀ r, 0 < tail r ∧ tail r < sMax := fun r => hs r.succ
    have hprevious : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
        ∃ W : LayerWitness α m, W.Valid N d e₀ u ρ π b tail k δ :=
      ih N K hN hNt hK α ν μ ρ π b P T n j A B c F h1 h2 h3 h4 tail htail
    obtain ⟨δ, W, hδ, hδlim, -, hW⟩ :=
      layer_sequence_of_fixed_request hN1 tail hprevious
    obtain ⟨H, ρ', hH, hKH, hρ', hbasic', hequal⟩ :=
      prepare_layer_residual hN1 hK hδ hδlim h1 tail W hW
    have hcaps' : Hyp2 N H d S μ π b P := h2.monoK (fun k => (hNp k).le) hKH
    have htrue' : Hyp3 N H d κ ℓ U e₀ ν μ π b P T n j A B c F :=
      h3.monoK hNp (fun k => by linarith [hK.1 k]) hKH
    have hnew : LayersAt1 N d e₀ u sMax ρ' π b :=
      hsingle N H hN hNt hH α ν μ ρ' π b P T n j A B c F hbasic' hcaps' htrue' h4
    have hδsmall : ∀ᶠ k in atTop, δ k < δ₀ :=
      hδlim.eventually (gt_mem_nhds hδ₀)
    have hreserve := hNt.eventually
      (eventually_common_layer_reserve (ε := ε) (m + 1) hδ₀ (by dsimp [δ₀]; linarith))
    filter_upwards [hW, hequal, hδsmall, hK.2 δ₀ hδ₀, hreserve,
      hnew (s 0) (hs 0).1 (hs 0).2 δ₀ hδ₀] with k hWk heq hδk hKk hnum hk
    obtain ⟨σ, hσ, hσmass, n₀, A₀, q₀, g₀, hnewLayer⟩ := hk
    let source : Fin (m + 1) → Measure (α × ℝ) :=
      Fin.cases σ (fun _ => (W k).law)
    let loss : Fin (m + 1) → ℝ := Fin.cases δ₀ (fun _ => δ k)
    let D : Fin (m + 1) → ℝ := fun r => N k ^ (-u * s r)
    let a : Fin (m + 1) → ℝ := fun r => N k ^ (-s r)
    let nn : Fin (m + 1) → ℕ := Fin.cases n₀ (W k).n
    let AA : (r : Fin (m + 1)) → Fin (nn r) → Set α :=
      fun r => Fin.cases (motive := fun r => Fin (nn r) → Set α) A₀ (W k).A r
    let qq : (r : Fin (m + 1)) → Fin (nn r) → Fin 3 → ℤ :=
      fun r => Fin.cases (motive := fun r => Fin (nn r) → Fin 3 → ℤ) q₀ (W k).q r
    let gg : (r : Fin (m + 1)) → Fin (nn r) → Fin 6 → ℝ :=
      fun r => Fin.cases (motive := fun r => Fin (nn r) → Fin 6 → ℝ) g₀ (W k).h r
    have hsource : ∀ r, LayerAt N d e₀ π b k (loss r) (source r) (D r) (a r)
        (nn r) (AA r) (qq r) (gg r) := by
      intro r
      refine Fin.cases ?_ (fun r => ?_) r
      · exact hnewLayer
      · exact hWk.2.2 r
    have hσsource : ∀ r, σ ≤ source r := by
      intro r
      refine Fin.cases le_rfl (fun _ => ?_) r
      exact hσ.trans_eq heq
    have hsourceDom : ∀ r, source r ≤ ρ k := by
      intro r
      refine Fin.cases ?_ (fun _ => hWk.1) r
      exact hσ.trans (hρ' k)
    have hmassSource : ∀ r, source r univ ≤ ENNReal.ofReal (K k) :=
      fun r => (hsourceDom r _).trans (h1.current_mass_le k)
    have hloss : ∀ r, loss r ≤ δ₀ := by
      intro r
      exact Fin.cases le_rfl (fun _ => hδk.le) r
    have hcost := common_layer_floor_budget (ε := ε) (δ₀ := δ₀) (B := K k)
      source loss D a nn AA qq gg (hN1 k) hloss hKk hmassSource hsource
    have hσorig : σ ≤ ρ k := hσ.trans (hρ' k)
    have htime : σ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
      obtain ⟨-, -, -, -, hρμ, htimeμ, -⟩ := h1 k
      exact le_antisymm (((hσorig.trans hρμ) _).trans_eq htimeμ) bot_le
    have hbudget : ENNReal.ofReal (N k ^ (-ε)) +
        (∑ r, ∑ i, ENNReal.ofReal ((D r) ^ 2 * (a r) ^ d / N k ^ ε) *
          π k (Ico ((qq r i 0 : ℝ) * N k ^ (-e₀))
            (((qq r i 0 : ℝ) + 1) * N k ^ (-e₀)))) < σ univ := by
      calc
        _ ≤ ENNReal.ofReal (N k ^ (-ε)) +
            ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * N k ^ (2 * δ₀ - ε)) :=
          add_le_add le_rfl hcost
        _ = ENNReal.ofReal (N k ^ (-ε) +
            ((m + 1 : ℕ) : ℝ) * N k ^ (2 * δ₀ - ε)) :=
          (ENNReal.ofReal_add (Real.rpow_nonneg (hNp k).le _)
            (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hNp k).le _))).symm
        _ < ENNReal.ofReal (N k ^ (-δ₀)) :=
          (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (hNp k) _)).mpr hnum.2
        _ ≤ σ univ := hσmass
    obtain ⟨σ', n', A', q', g', hσ', hmass', hlayers⟩ :=
      restore_common_layers σ source loss D a nn AA qq gg (hN1 k)
        (fun r => Real.rpow_nonneg (hNp k).le _) (fun r => (hloss r).trans hδ₀ε)
        hσsource htime hsource hbudget
    exact ⟨⟨σ', n', A', q', g'⟩, hσ'.trans hσorig, hmass', hlayers⟩

/-- A universal one-depth engine supplies all finite simultaneous depth requests,
with every floor evaluated in the same final current law. -/
theorem engineAt_of_single (d κ ℓ S U e₀ u sMax : ℝ)
    (hsingle : EngineAt1 d κ ℓ S U e₀ u sMax) :
    EngineAt d κ ℓ S U e₀ u sMax := by
  intro N K hN hNt hK α _ ν μ ρ π b P T n j A B c F h1 h2 h3 h4 m s hs ε hε
  filter_upwards [(engineAtCount_of_single d κ ℓ S U e₀ u sMax hsingle m)
    N K hN hNt hK α ν μ ρ π b P T n j A B c F h1 h2 h3 h4 s hs ε hε] with k hk
  obtain ⟨W, hW⟩ := hk
  exact ⟨W.law, hW.1, hW.2.1, W.n, W.A, W.q, W.h, hW.2.2⟩

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
