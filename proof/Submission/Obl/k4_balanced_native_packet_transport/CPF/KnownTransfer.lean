/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/KnownTransfer.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/KnownTransfer.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.PrunedAtlas
import Submission.Obl.k4_balanced_native_packet_transport.CPF.CrossingBounds
import Submission.Obl.k4_balanced_native_packet_transport.CPF.PruningNumerics
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! True systems at an intermediate depth give known atlases in fixed format.
This is the label-knowledge part of the supplied paper's Lemma `a01:saturation`.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set MeasureTheory Filter
open scoped ENNReal

theorem knownAtlas_of_true_at_depth {p : Data} (hp : p.Valid) {r h : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (ht : ∃ M D : ℕ, ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
      ∃ a : Atlas p k, 1 ≤ a.κ ∧ a.κ ≤ p.N k ^ σ ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M D r) :
    KnownAtlas p r h := by
  obtain ⟨M, D, htrue⟩ := ht
  obtain ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, ⟨Mb, Db, htemp⟩,
    hg, hG, hprofile, htyp, hcap, hang⟩ := hp
  let R : ℕ := ⌈r⌉₊
  let J : ℕ := Mb + Mb + R + 2
  let M' : ℕ := M + (J + 3) + 10
  refine ⟨M', max D 4, ?_⟩
  intro ε hε
  let τ := ε / 100
  let u := ε / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨c, hc, htyp⟩ := htyp r τ hr hrL hτ
  let σ := min 1 (min (ε / 100) (c / 10))
  have hσ : 0 < σ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hσε : σ ≤ ε / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hσc : σ ≤ c / 10 := (min_le_right _ _).trans (min_le_right _ _)
  have hbadLarge := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -c < -σ by linarith) 4
  have hcostLarge := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show 5 * σ + τ - u < -σ by dsimp [τ, u]; linarith) (160 * Real.pi)
  have hslackLarge := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show σ < ε by linarith) 2
  have hlarge : ∀ᶠ k in atTop,
      4 * p.N k ^ (-c) ≤ p.N k ^ (-σ) ∧
      160 * Real.pi * p.N k ^ (5 * σ + τ - u) ≤ p.N k ^ (-σ) ∧
      2 * p.N k ^ σ ≤ p.N k ^ ε := by
    filter_upwards [hbadLarge, hcostLarge, hslackLarge] with k hb hc hs
    exact ⟨hb.le, hc.le, hs.le⟩
  apply ((htrue σ hσ).and_eventually (htyp.and hlarge)).mono
  intro k hk
  obtain ⟨a, hκ, hκσ, hT, ha⟩ := hk.1
  have hN0 : 0 < p.N k := by linarith [hN k]
  have hN1 : 1 ≤ p.N k := by linarith [hN k]
  have hκN : a.κ ≤ p.N k := hκσ.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hσ1)
  let bins : Fin (p.W k) → Finset ℤ := fun _ => boundedHiddenBins (p.N k) J
  let m := ⌈4 * a.κ ^ 2⌉₊
  have hsample := crossing_sample_count_bound (hN k) hκ hκN
  have hworld := (htemp k).2.2.2.1
  have hB (γ : Fin (p.W k)) : 0 < p.B k γ := (hworld γ).2.1
  have hprob (γ : Fin (p.W k)) : IsProbabilityMeasure (p.ν k γ) := (hworld γ).1
  have hE (γ : Fin (p.W k)) : p.E k γ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, hE, _⟩ := hworld γ
    exact hE
  have hmass : a.mass ≤ 1 := a.mass_le_one ha.2.1 _ ha.2.2.1 hprob
    (htemp k).2.1 (htemp k).2.2.1 hE
  have hceiling : (∑ γ, ENNReal.ofReal (p.ω k γ) *
      (((p.ν k γ).prod volume).restrict (p.E k γ))
        {q | ENNReal.ofReal (p.N k ^ (-p.f r + τ)) <
          p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}) ≤ ENNReal.ofReal (p.N k ^ (-c)) := by
    apply le_trans _ hk.2.1
    apply Finset.sum_le_sum
    intro γ _
    apply mul_le_mul le_rfl _ zero_le zero_le
    exact measure_mono (fun q hq => Or.inr hq)
  have hlost : a.crossingLostMass r bins m (p.N k ^ u) ≤ ENNReal.ofReal (2 * a.κ)⁻¹ := by
    apply (a.crossingLostMass_le_power ha hN0 hκ hκσ hB bins m hmass
      (fun γ => (hg k γ r hr hrL).1) (fun γ => (hg k γ r hr hrL).2) hceiling).trans
    apply ENNReal.ofReal_le_ofReal
    exact pruning_loss_small hN0 hκ hκσ hk.2.2.1 hk.2.2.2.1
  have hbin (b : Fin a.C) (q : Incidence) (hq : q ∈ a.F b) :
      (obs (p.B k (a.γ b)) (δ (p.N k) r) q).2 ∈ bins (a.γ b) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := ha.2.2.1 b
    have hqE := (hsel q hq).1
    obtain ⟨_, _, hBN, _, _, _, _, _, _, hcoeff, _⟩ := hworld (a.γ b)
    apply mem_boundedHiddenBins
    exact hidden_signal_bound (hN k) (hB _).le hBN (Nat.le_ceil r) q.1 q.2
      (hE _ hqE).2 (hcoeff q hqE).2
  have hformat (b : Fin a.C) : p.N k ^ M + (a.C : ℝ) *
      ((bins (a.γ b)).card * (5 + 4 * m)) ≤ p.N k ^ M' :=
    crossing_format_bound (hN k) ha.1 (boundedHiddenBins_card (hN k) J) hsample.2
  have hκout : 2 * a.κ ≤ p.N k ^ ε :=
    (mul_le_mul_of_nonneg_left hκσ (by norm_num)).trans hk.2.2.2.2
  apply knownAt_of_crossing_loss a ha hN1 hrL (by dsimp [M']; omega)
    (le_max_left _ _) (le_max_right _ _) hκ hκout le_rfl hB _ bins m hsample.1
    (Real.rpow_pos_of_pos hN0 u).le _ hformat hbin hlost
  · exact hT.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  · exact Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [u]; linarith)

end Submission.Obl.k4_balanced_native_packet_transport.CPF
