import Submission.Obl.k4_raw_localized_native_systems.C.FixedTimeBad

/-
Adapted from this LOT tree, o178, session x0596, `FixedTimeTotal.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The fixed-time transverse bound of one world

The charts of one world whose block contains a fixed time have disjoint
assignments, so their selected prior masses add up to at most the block length.
With the chart floors, their determinants add up to at most `κ N^{f(r)}`, and the
transverse incidences at any fixed first time have the same bound as the
time-averaged bad pairs.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

open Classical in
/-- The selected prior masses of the charts of one world and one block. -/
theorem block_prior_sum_le (a : Atlas p k) {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop}
    (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (γ : Fin (p.W k)) [IsProbabilityMeasure (p.ν k γ)] (t₀ : ℝ) :
    ∑ b ∈ Finset.univ.filter (fun b => t₀ ∈ q2tblk a γ b), priorMass p k (a.γ b) (a.F b) ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := by
  set s := Finset.univ.filter (fun b => t₀ ∈ q2tblk a γ b) with hs
  have h2T : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  have h1 : ∀ b ∈ s, priorMass p k (a.γ b) (a.F b) ≤
      p.ν k γ (a.A b) * ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := by
    intro b hb
    have hγ : a.γ b = γ := (Finset.mem_filter.1 hb).2.1
    have hsub : a.F b ⊆ a.A b ×ˢ Set.Icc (((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T)
        ((((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T) := by
      intro z hz
      have := hc.selected b hz
      exact ⟨this.2.1, this.2.2⟩
    unfold priorMass
    rw [hγ]
    calc ((p.ν k γ).prod volume) (a.F b)
        ≤ ((p.ν k γ).prod volume) (a.A b ×ˢ Set.Icc (((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T)
            ((((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T)) := measure_mono hsub
      _ = p.ν k γ (a.A b) * ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := by
        rw [Measure.prod_prod, Real.volume_Icc]
        congr 2
        ring
  have hdis : Set.PairwiseDisjoint (↑s) a.A := by
    intro b hb b' hb' hne
    have hb1 := (Finset.mem_filter.1 hb).2
    have hb2 := (Finset.mem_filter.1 hb').2
    have hj : a.j b = a.j b' := by
      apply Fin.ext
      have := hb1.2.symm.trans hb2.2
      exact_mod_cast this
    exact hdisj b b' hne (hb1.1.trans hb2.1.symm) hj
  have h2 : ∑ b ∈ s, p.ν k γ (a.A b) ≤ 1 := by
    rw [← measure_biUnion_finset hdis (fun b _ => hc.measA b)]
    exact prob_le_one
  calc ∑ b ∈ s, priorMass p k (a.γ b) (a.F b)
      ≤ ∑ b ∈ s, p.ν k γ (a.A b) * ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) :=
        Finset.sum_le_sum h1
    _ = (∑ b ∈ s, p.ν k γ (a.A b)) * ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := by gcongr
    _ = ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := one_mul _

open Classical in
/-- **Fixed-time transverse bound of one world.** -/
theorem q2_world_fixed_total_le (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k))
    {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
    (κL : ℕ) (hcard : ∀ o, (a.lst γ o).card ≤ κL)
    (hmeas : ∀ b, MeasurableSet {o | b ∈ a.lst γ o})
    (hfloor : ∀ b, ENNReal.ofReal (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * κ)) ≤
      priorMass p k (a.γ b) (a.F b))
    (hκ : 0 < κ)
    (hC : 0 < a.C) {u τ κ' lam ρ Kc g H : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hκ' : 1 ≤ κ') (hκκ' : κ ≤ κ')
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
    (hKc : κ' + ρ ≤ Kc)
    (hg : 0 < g) (hH : 0 < H) (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u) (t₀ : ℝ) :
    ((p.ν k γ).prod volume)
        {q | (q.1, t₀) ∈ goodPath a γ u τ κ' lam ∧ q ∈ goodPath a γ u τ κ' lam ∧
          g * H < min ‖q2normal a (tagOf a γ hC (q.1, t₀)) - q2normal a (tagOf a γ hC q)‖
            ‖q2normal a (tagOf a γ hC (q.1, t₀)) + q2normal a (tagOf a γ hC q)‖} ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
        (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
          ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r))) := by
  have hN : 0 < p.N k := hp.scale_pos k
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have : IsProbabilityMeasure (p.ν k γ) := ((hfmt k).2.2.2.1 γ).1
  set s := Finset.univ.filter (fun b => t₀ ∈ q2tblk a γ b) with hs
  set cS := ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) with hcS
  set C0 := ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) with hC0
  set Y := ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r)) with hY
  have hmain := q2_world_bad_fixed_le hp a γ hc hdisj hknown κL hcard hmeas hC (τ := τ) hu huη
    hκ' hκκ' hρ hKc hg hH hpin t₀
  refine hmain.trans ?_
  rw [← hs, ← Finset.mul_sum]
  simp_rw [← hcS, ← hC0]
  rw [← Finset.mul_sum]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  have hterm : ∀ b ∈ s, ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|) ≤
      ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r) * (2 : ℝ) ^ a.T) *
        priorMass p k (a.γ b) (a.F b) := by
    intro b _
    have hdet : |(stripScale a.T • a.Q b).det| = stripScale a.T ^ 2 * |(a.Q b).det| := by
      rw [Matrix.det_smul, abs_mul, Fintype.card_fin, abs_pow, abs_of_pos (stripScale_pos a.T)]
    have hval : 256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det| =
        (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r) * (2 : ℝ) ^ a.T) *
          (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * κ)) := by
      rw [hdet, Real.rpow_neg hN.le, sub_zero, mul_one]
      have : p.N k ^ p.f r ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
      field_simp
    rw [hval, ENNReal.ofReal_mul (by
      have : 0 ≤ p.N k ^ p.f r := Real.rpow_nonneg hN.le _
      positivity)]
    gcongr
    exact hfloor b
  have hsum : ∑ b ∈ s, ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|) ≤
      Y := by
    calc ∑ b ∈ s, ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|)
        ≤ ∑ b ∈ s, ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r) *
            (2 : ℝ) ^ a.T) * priorMass p k (a.γ b) (a.F b) := Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r) *
            (2 : ℝ) ^ a.T) * ∑ b ∈ s, priorMass p k (a.γ b) (a.F b) := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r) *
            (2 : ℝ) ^ a.T) * ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := by
          gcongr
          exact block_prior_sum_le a hc hdisj γ t₀
      _ = Y := by
          rw [← ENNReal.ofReal_mul (by
            have : 0 ≤ p.N k ^ p.f r := Real.rpow_nonneg hN.le _
            positivity)]
          congr 1
          field_simp
  calc cS * ((9 * κL : ℕ) : ENNReal) * (C0 * ∑ b ∈ s,
        ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|))
      ≤ cS * ((9 * κL : ℕ) : ENNReal) * (C0 * Y) := by gcongr

end

end Submission.Obl.k4_raw_localized_native_systems.C
