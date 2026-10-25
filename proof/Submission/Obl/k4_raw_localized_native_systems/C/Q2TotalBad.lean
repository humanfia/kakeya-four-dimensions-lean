import Submission.Obl.k4_raw_localized_native_systems.C.Q2BadPair
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

/-
Adapted from this LOT tree, o178, session x0596, `Q2TotalBad.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The weighted bad-pair mass over all worlds

Summing the one-world bounds with the original world weights, each chart is
charged once, with its block length.  The true floor at depth `r` converts the
determinant into prior mass, and the original assignment budget (accepted o115)
bounds the total:

  `Σ_γ ω_γ · pair_γ(bad) ≤ N^(-S u + 2τ) · 9κ_L · N^(-f 0 + τ) · 256 κ'^4 s² κ N^(f r)`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

theorem volume_q2blk (a : Atlas p k) (γ : Fin (p.W k)) (b : Fin a.C) :
    volume (q2blk a γ b) = if a.γ b = γ then ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) else 0 := by
  classical
  unfold q2blk
  split_ifs
  · rw [Real.volume_Icc]
    congr 1
    ring
  · simp

/-- The weighted sum of block lengths against a chart quantity. -/
theorem sum_worlds_blocks (a : Atlas p k) (X : Fin a.C → ENNReal) :
    ∑ γ, ENNReal.ofReal (p.ω k γ) * ∑ b, volume (q2blk a γ b) * X b =
      ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * (ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) * X b) := by
  classical
  simp_rw [volume_q2blk, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp_rw [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- **Total weighted bad-pair mass of a later chart system.** -/
theorem q2_total_bad_pair_le (hp : Valid p) (a : Atlas p k)
    {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
    (κL : ℕ) (hcard : ∀ γ o, (a.lst γ o).card ≤ κL)
    (hmeas : ∀ γ b, MeasurableSet {o | b ∈ a.lst γ o})
    (hfloor : ∀ b, ENNReal.ofReal (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * κ)) ≤
      priorMass p k (a.γ b) (a.F b))
    (hκ : 0 < κ)
    (hC : 0 < a.C) {u τ κ' lam ρ Kc g H : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hκ' : 1 ≤ κ') (hκκ' : κ ≤ κ')
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ) (hKc : κ' + ρ ≤ Kc)
    (hg : 0 < g) (hH : 0 < H) (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u) :
    ∑ γ, ENNReal.ofReal (p.ω k γ) * ((p.ν k γ).prod (volume.prod volume))
        {z | (z.1, z.2.1) ∈ goodPath a γ u τ κ' lam ∧ (z.1, z.2.2) ∈ goodPath a γ u τ κ' lam ∧
          g * H < min ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) -
              q2normal a (tagOf a γ hC (z.1, z.2.2))‖
            ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) + q2normal a (tagOf a γ hC (z.1, z.2.2))‖} ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
        (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
          ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r))) := by
  classical
  have hN : 0 < p.N k := hp.scale_pos k
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hprob : ∀ γ, IsProbabilityMeasure (p.ν k γ) := fun γ => ((hfmt k).2.2.2.1 γ).1
  have hω0 : ∀ γ, 0 ≤ p.ω k γ := (hfmt k).2.1
  have hω1 : ∑ γ, p.ω k γ = 1 := (hfmt k).2.2.1
  set cS := ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) with hcS
  set C0 := ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) with hC0
  set X : Fin a.C → ENNReal := fun b => cS * ((9 * κL : ℕ) : ENNReal) *
    (C0 * ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|)) with hX
  -- one world at a time
  have hworld : ∀ γ, ((p.ν k γ).prod (volume.prod volume))
        {z | (z.1, z.2.1) ∈ goodPath a γ u τ κ' lam ∧ (z.1, z.2.2) ∈ goodPath a γ u τ κ' lam ∧
          g * H < min ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) -
              q2normal a (tagOf a γ hC (z.1, z.2.2))‖
            ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) + q2normal a (tagOf a γ hC (z.1, z.2.2))‖} ≤
        ∑ b, volume (q2blk a γ b) * X b := fun γ =>
    q2_world_bad_pair_le hp a γ hc hdisj hknown κL (hcard γ) (hmeas γ) hC hu huη hκ' hκκ'
      hρ hKc hg hH hpin
  calc _ ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) * ∑ b, volume (q2blk a γ b) * X b := by
        gcongr with γ; exact hworld γ
    _ = ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * (ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) * X b) :=
        sum_worlds_blocks a X
    _ ≤ ∑ b, cS * ((9 * κL : ℕ) : ENNReal) * (C0 *
          ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r))) *
          (ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b)) := by
        apply Finset.sum_le_sum
        intro b _
        -- the floor converts the determinant into prior mass
        have hdet : |(stripScale a.T • a.Q b).det| = stripScale a.T ^ 2 * |(a.Q b).det| := by
          rw [Matrix.det_smul, abs_mul, Fintype.card_fin, abs_pow,
            abs_of_pos (stripScale_pos a.T)]
        have h2 : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
        have hfl := hfloor b
        have hkey : ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) *
            ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|) ≤
            ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r)) *
              priorMass p k (a.γ b) (a.F b) := by
          have hval : (1 / (2 : ℝ) ^ a.T) * (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|) =
              (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r)) *
                (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * κ)) := by
            rw [hdet, Real.rpow_neg hN.le, sub_zero, mul_one]
            have : p.N k ^ p.f r ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
            field_simp
          rw [← ENNReal.ofReal_mul (by positivity), hval,
            ENNReal.ofReal_mul (by
              have : 0 ≤ p.N k ^ p.f r := Real.rpow_nonneg hN.le _
              positivity)]
          gcongr
        calc ENNReal.ofReal (p.ω k (a.γ b)) * (ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) * X b)
            = cS * ((9 * κL : ℕ) : ENNReal) * C0 * (ENNReal.ofReal (p.ω k (a.γ b)) *
                (ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) *
                  ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|))) := by
              simp only [hX]; ring
          _ ≤ cS * ((9 * κL : ℕ) : ENNReal) * C0 * (ENNReal.ofReal (p.ω k (a.γ b)) *
                (ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r)) *
                  priorMass p k (a.γ b) (a.F b))) := by gcongr
          _ = _ := by ring
    _ = cS * ((9 * κL : ℕ) : ENNReal) * (C0 *
          ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r))) *
          ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b) := by
        rw [Finset.mul_sum]
    _ ≤ cS * ((9 * κL : ℕ) : ENNReal) * (C0 *
          ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r))) * 1 := by
        gcongr
        have hbud := Submission.Obl.k4_quadratic_atlas_normalization.weighted_incidence_mass_le_section_bound
          (p.ν k) (p.ω k) a.γ a.j a.A a.F (ENNReal.ofReal (1 / (2 : ℝ) ^ a.T)) hprob hω0 hω1
          hc.measA hc.measF hdisj
          (fun b z hz => ((hc b).2.2.2.2.2.2.2.2.2.2.1 z hz).2.1)
          (fun b l hl => by
            calc volume {t : ℝ | (l, t) ∈ a.F b}
                ≤ volume (Set.Icc (((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T)
                    ((((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T)) := by
                  apply measure_mono
                  intro t ht
                  exact ((hc b).2.2.2.2.2.2.2.2.2.2.1 (l, t) ht).2.2.1
              _ = ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := by
                  rw [Real.volume_Icc]; congr 1; ring)
        refine hbud.trans (le_of_eq ?_)
        rw [Fintype.card_fin, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        push_cast
        rw [div_mul_cancel₀ _ (by positivity), ENNReal.ofReal_one]
    _ = _ := by rw [mul_one]

end

end Submission.Obl.k4_raw_localized_native_systems.C
