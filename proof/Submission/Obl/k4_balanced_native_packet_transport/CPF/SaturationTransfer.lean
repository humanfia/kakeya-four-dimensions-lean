/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/SaturationTransfer.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/SaturationTransfer.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SaturatedSample
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SaturationNumerics
import Submission.Obl.k4_balanced_native_packet_transport.CPF.KnownTransfer

/-! Full native saturation at a fixed depth.  The format bounds are fixed before
the tolerance; the original assigned priors and world weights are retained. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set MeasureTheory Filter
open scoped ENNReal

theorem uniform_saturation_at_depth {p : Data} (hp : p.Valid) {r : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) (M D : ℕ) :
    ∃ M' D' : ℕ, M ≤ M' ∧ D ≤ D' ∧ ∀ ε : ℝ, 0 < ε →
      ∃ σ : ℝ, 0 < σ ∧ σ ≤ ε ∧ ∀ᶠ k in atTop, ∀ a : Atlas p k,
        1 ≤ a.κ → a.κ ≤ p.N k ^ σ → a.TrueAt M D r →
        ∃ a' : Atlas p k, 1 ≤ a'.κ ∧ p.K k ≤ a'.κ ∧ a'.κ = p.N k ^ ε ∧
          a'.T = a.T ∧ a'.SaturatedAt M' D' r := by
  have hvalid : p.Valid := hp
  obtain ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, ⟨Mb, Db, htemp⟩,
    hg, hG, hprofile, htyp, hcap, hang⟩ := hp
  let R : ℕ := ⌈r⌉₊
  let J : ℕ := Mb + Mb + R + 2
  let M' : ℕ := M + (J + 3) + 10
  refine ⟨M', max D 4, by dsimp [M']; omega, le_max_left _ _, ?_⟩
  intro ε hε
  let τ := ε / 100
  let u := ε / 2
  let v := ε / 10
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨c, hc, htyp⟩ := htyp r τ hr hrL hτ
  let σ := min 1 (min (ε / 100) (c / 10))
  have hσ : 0 < σ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hσε : σ ≤ ε / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hσc : σ ≤ c / 10 := (min_le_right _ _).trans (min_le_right _ _)
  have hbLarge := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -c < -σ by linarith) 24
  have hcLarge := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show 5 * σ + τ - u < -σ by dsimp [τ, u]; linarith) (480 * Real.pi)
  have hlLarge := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -v < -σ by dsimp [v]; linarith) 6
  have hsLarge := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show σ < ε by linarith) 2
  have hpLarge := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show v + τ + 4 * σ < ε by dsimp [v, τ]; linarith) (80 * Real.pi)
  have hlarge : ∀ᶠ k in atTop,
      24 * p.N k ^ (-c) ≤ p.N k ^ (-σ) ∧
      480 * Real.pi * p.N k ^ (5 * σ + τ - u) ≤ p.N k ^ (-σ) ∧
      6 * p.N k ^ (-v) ≤ p.N k ^ (-σ) ∧
      2 * p.N k ^ σ ≤ p.N k ^ ε ∧
      80 * Real.pi * p.N k ^ (v + τ + 4 * σ) ≤ p.N k ^ ε ∧ p.K k ≤ p.N k ^ ε := by
    filter_upwards [hbLarge, hcLarge, hlLarge, hsLarge, hpLarge, hK.2 ε hε]
      with k hb hc hl hs hp hK
    exact ⟨hb.le, hc.le, hl.le, hs.le, hp.le, hK⟩
  refine ⟨σ, hσ, by linarith, ?_⟩
  filter_upwards [htyp, hlarge] with k htypk hlargek
  intro a hκ hκσ ha
  obtain ⟨hb, hcost, hlight, hslack, hprior, hKn⟩ := hlargek
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
    apply le_trans _ htypk
    apply Finset.sum_le_sum
    intro γ _
    apply mul_le_mul' le_rfl
    exact measure_mono (fun q hq => Or.inr hq)
  have hcross := a.crossingLostMass_le_power (u := u) ha hN0 hκ hκσ hB bins m hmass
    (fun γ => (hg k γ r hr hrL).1) (fun γ => (hg k γ r hr hrL).2) hceiling
  have hlabels := a.saturated_label_loss_le hvalid ha hκ (Real.rpow_pos_of_pos hN0 v)
    (Real.rpow_pos_of_pos hN0 (-p.f r + τ)).le hB m hsample.1
    (fun γ => (hg k γ r hr hrL).1) (fun γ => (hg k γ r hr hrL).2)
  have htwo (x : ℝ) : (2 : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hlost : 2 * a.crossingLostMass r bins m (p.N k ^ u) +
      a.deletedMass (a.saturatedLabels (p.N k ^ v) (p.N k ^ (-p.f r + τ))) ≤
        ENNReal.ofReal (2 * a.κ)⁻¹ := by
    calc
      _ ≤ 2 * ENNReal.ofReal (p.N k ^ (-c) + 40 * Real.pi * p.N k ^ (5 * σ + τ - u)) +
          (ENNReal.ofReal ((p.N k ^ v)⁻¹) + 2 * ENNReal.ofReal (p.N k ^ (-c))) :=
        add_le_add (mul_le_mul' le_rfl hcross) (hlabels.trans (add_le_add le_rfl
          (mul_le_mul' le_rfl hceiling)))
      _ = ENNReal.ofReal (4 * p.N k ^ (-c) +
          80 * Real.pi * p.N k ^ (5 * σ + τ - u) + p.N k ^ (-v)) := by
        rw [← Real.rpow_neg hN0.le, htwo, htwo,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (saturation_loss_small hN0 hκ hκσ hb hcost hlight)
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
    (mul_le_mul_of_nonneg_left hκσ (by norm_num)).trans hslack
  obtain ⟨a', hTT, hκout', hsat⟩ := saturated_atlas_of_crossing_loss hvalid
    (M' := M') (D' := max D 4) (κ' := p.N k ^ ε) a ha
    (by dsimp [M']; omega) (le_max_left _ _) (le_max_right _ _) hκ hκout bins m hsample.1
    (Real.rpow_pos_of_pos hN0 u).le
    (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [u]; linarith))
    (Real.rpow_pos_of_pos hN0 v).le hformat hbin hlost
    ((saturated_prior_factor_bound hN0 hκ hκσ).trans
      (mul_le_mul_of_nonneg_right hprior (by positivity)))
  refine ⟨a', ?_, ?_, hκout', hTT, hsat⟩
  · rw [hκout']
    linarith
  · simpa only [hκout'] using hKn

theorem saturated_atlases_of_true_at_depth {p : Data} (hp : p.Valid) {r h : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (ht : ∃ M D : ℕ, ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
      ∃ a : Atlas p k, 1 ≤ a.κ ∧ a.κ ≤ p.N k ^ σ ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M D r) :
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.SaturatedAt M D r := by
  obtain ⟨M, D, htrue⟩ := ht
  obtain ⟨M', D', _, _, hprep⟩ := uniform_saturation_at_depth hp hr hrL M D
  refine ⟨M', D', ?_⟩
  intro ε hε
  obtain ⟨σ, hσ, _, hs⟩ := hprep ε hε
  apply ((htrue σ hσ).and_eventually hs).mono
  intro k hk
  obtain ⟨a, hκ, hκN, hT, ha⟩ := hk.1
  obtain ⟨a', hκ', hK', hκN', hT', ha'⟩ := hk.2 a hκ hκN ha
  exact ⟨a', hκ', hK', hκN'.le, by simpa only [hT'] using hT, ha'⟩

end Submission.Obl.k4_balanced_native_packet_transport.CPF
