import Submission.Obl.k4_scalar_mesh_block_reduction.ChildTypes
import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity
import Submission.Obl.k4_scalar_marked_coefficient_smoothing
import Submission.Obl.k4_scalar_marked_profile_selection
import Submission.Obl.k4_scalar_noisy_block_packets
import Submission.Obl.k4_scalar_marked_packet_recovery

open Filter MeasureTheory
open scoped Topology

namespace Submission.Obl.k4_scalar_mesh_block_reduction

private theorem smoothing : marked_smoothing_type :=
  Submission.k4_scalar_marked_coefficient_smoothing

private theorem noisy_packets : noisy_packets_type :=
  Submission.k4_scalar_noisy_block_packets

private theorem profile_selection : profile_selection_type :=
  Submission.k4_scalar_marked_profile_selection

private theorem recovery : original_recovery_type :=
  Submission.k4_scalar_marked_packet_recovery

private theorem coupling_of_subtable {N K K' s m : ℝ} {α : Type}
    [MeasurableSpace α] {ν : Measure α} {μ : Measure (α × ℝ)}
    {b : α → Fin 5 → ℝ} {H J : ℕ} {tag : α → Fin H}
    {b₀ : Fin H → Fin 5 → ℝ} {w : Fin H → ℝ}
    {mark mark' : Fin H → Fin J → Bool}
    (h : Coupling N K s m α ν μ b H J tag b₀ w mark)
    (hK : 0 < K) (hKK' : K ≤ K') (hw : ∀ j, 0 ≤ w j)
    (hJ : 1 ≤ J) (hsub : ∀ j z, mark' j z = true → mark j z = true) :
    Coupling N K' s m α ν μ b H J tag b₀ w mark' := by
  rcases h with ⟨htag, hweights, hround, hmark⟩
  refine ⟨htag, hweights, hround, ?_⟩
  intro j z hz
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hmark j z (hsub j z hz))
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  exact div_le_div_of_nonneg_left (hw j) (mul_pos hJpos hK)
    (mul_le_mul_of_nonneg_left hKK' (Nat.cast_nonneg J))

/-- The underlying measurable space is part of a model, and may vary along a
failure sequence. This preserves the quantifier over arbitrary trajectory priors. -/
structure Model where
  α : Type
  [space : MeasurableSpace α]
  ν : Measure α
  μ : Measure (α × ℝ)
  b : α → Fin 5 → ℝ
  c : ℝ
  angular : Bool

attribute [local instance] Model.space

private def Admissible (d s m C S U η N : ℝ) (Q : Model) : Prop :=
  (N ^ (-C) ≤ Q.c ∧ Q.c ≤ N ^ C) ∧
  MeshInput N (N ^ η) d s m S U Q.α Q.ν Q.μ Q.b Q.c Q.angular

private def Result (d s m ε _η N : ℝ) (Q : Model) : Prop :=
  BlockOutput N d s m Q.c ε Q.angular Q.α Q.μ Q.b

/-- All analytic work is in the four children. A successful sample of every
vanishing-loss sequence supplies uniform finite parameters. -/
theorem uniform_block_packets (hExact : ExactAngularPackets)
    (d s m C S U ε : ℝ) (hd : 0 ≤ d) (hd1 : d < 1)
    (hs : 0 < s) (hsm : s < m) (hC : 0 < C) (hS : 0 < S)
    (hU : 0 < U) (hUm : U < m) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ Q : Model,
        Admissible d s m C S U η N Q → Result d s m ε η N Q := by
  apply uniformity_of_sequence (Model := fun _ _ => Model)
    (Admissible d s m C S U) (Result d s m ε)
  intro η N hη hηlim hN hNlim Q hQ
  have hK : Subpower N (fun k => N k ^ η k) :=
    subpower_of_vanishing_exponent N η (fun k => le_trans (by norm_num) (hN k))
      (fun k => (hη k).le) hηlim
  have hc k : N k ^ (-C) ≤ (Q k).c ∧ (Q k).c ≤ N k ^ C := (hQ k).1
  have hinput k : MeshInput (N k) (N k ^ η k) d s m S U
      (Q k).α (Q k).ν (Q k).μ (Q k).b (Q k).c (Q k).angular := (hQ k).2
  obtain ⟨K', hK', M, H, J, b₀, w, mark, tag, htables, hcoupling, hraw⟩ :=
    smoothing N (fun k => N k ^ η k) hN hNlim hK
      d s m C S U hd hd1 hs hsm hC hS hU hUm
      (fun k => (Q k).α) (fun k => (Q k).ν) (fun k => (Q k).μ)
      (fun k => (Q k).b) (fun k => (Q k).c) (fun k => (Q k).angular) hc hinput
  obtain ⟨ψ, hψ, K'', hK'', hKK'', mark', angular₀, hflag, C₀, F,
      hshape, hcwindow, hselected, hsub, hhom⟩ :=
    profile_selection N K' hN hNlim hK'
      d s m C S U hd hd1 hs hsm hC hS hU hUm
      (fun k => (Q k).c) (fun k => (Q k).angular) M H J b₀ w mark
      hc htables hraw
  have hNs k : 2 ≤ (N ∘ ψ) k := hN (ψ k)
  have hNslim : Tendsto (N ∘ ψ) atTop atTop := hNlim.comp hψ.tendsto_atTop
  have hnoisy := noisy_packets hExact (N ∘ ψ) K'' hNs hNslim hK''
    d s m C S U hd hd1 hs hsm hC hS hU hUm
    (fun k => (Q (ψ k)).c) angular₀ C₀ F M (H ∘ ψ) (J ∘ ψ)
    (fun k => b₀ (ψ k)) (fun k => w (ψ k)) mark'
    (fun k => hc (ψ k)) hselected hshape hcwindow hhom
  have hcoupling' k : Coupling (N (ψ k)) (K'' k) s m
      (Q (ψ k)).α (Q (ψ k)).ν (Q (ψ k)).μ (Q (ψ k)).b
      (H (ψ k)) (J (ψ k)) (tag (ψ k)) (b₀ (ψ k)) (w (ψ k)) (mark' k) := by
    rcases htables (ψ k) with ⟨hJ, _, _, _, _, hw, _, _, _⟩
    exact coupling_of_subtable (hcoupling (ψ k))
      (lt_of_lt_of_le (by norm_num) (hK'.1 (ψ k))) (hKK'' k) hw hJ (hsub k)
  have hnoisy' (δ : ℝ) (hδ : 0 < δ) : ∃ᶠ k in atTop,
      NoisyOutput (N (ψ k)) d s m (Q (ψ k)).c δ (Q (ψ k)).angular
        (MarkedLaw (N (ψ k) ^ (-m)) (H (ψ k)) (J (ψ k))
          (b₀ (ψ k)) (w (ψ k)) (mark' k)) := by
    exact (hnoisy δ hδ).mono fun k hk => by
      simpa only [Function.comp_apply, hflag k] using hk
  have horiginal := recovery (N ∘ ψ) K'' hNs hNslim hK'' d s m hd hd1 hs hsm
    (fun k => (Q (ψ k)).α) (fun k => (Q (ψ k)).ν) (fun k => (Q (ψ k)).μ)
    (fun k => (Q (ψ k)).b) (fun k => (Q (ψ k)).c) (fun k => (Q (ψ k)).angular)
    M (H ∘ ψ) (J ∘ ψ) (fun k => b₀ (ψ k)) (fun k => w (ψ k)) mark'
    (fun k => tag (ψ k)) hselected hcoupling' hnoisy' ε hε
  obtain ⟨k, hk⟩ := horiginal.exists
  exact ⟨ψ k, hk⟩

/-- Repackage the uniform result in exactly the parent's model quantifiers. -/
theorem meshBlock_of_exact (hExact : ExactAngularPackets) : MeshBlockPackets := by
  intro d s m C S U ε hd hd1 hs hsm hC hS hU hUm hε
  obtain ⟨η, hη, N₀, hN₀, huniform⟩ :=
    uniform_block_packets hExact d s m C S U ε hd hd1 hs hsm hC hS hU hUm hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α inst ν μ b c angular hb hν hμ hsupp hmass hcoeff hc₀ hc₁ hcap hfinite hangular
  have hmass' : ENNReal.ofReal ((N ^ η)⁻¹) ≤ μ Set.univ := by
    simpa only [Real.rpow_neg (le_trans (by norm_num) (hN₀.trans hN))] using hmass
  exact huniform N hN
    { α := α, space := inst, ν := ν, μ := μ, b := b, c := c, angular := angular }
    ⟨⟨hc₀, hc₁⟩, hb, hν, hμ, hsupp, hmass', hcoeff, hcap, hfinite, hangular⟩

end Submission.Obl.k4_scalar_mesh_block_reduction
