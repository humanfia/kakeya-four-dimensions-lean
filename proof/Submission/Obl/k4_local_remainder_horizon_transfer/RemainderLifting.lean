import Submission.Obl.k4_local_remainder_horizon_transfer.RemainderData
import Submission.Obl.k4_local_remainder_horizon_transfer.Horizon

/-! Genuine terminal systems lift from the concrete normalized remaining problem. -/

namespace Submission.Obl.k4_local_remainder_horizon_transfer

open MeasureTheory Filter

/-- Repack a finite normalization system as an atlas of the original problem. -/
def Atlas.ofSystem (p : Data) (k T : ℕ) (κ : ℝ)
    (a : Normalization.ChartSystem (p.W k) T) : Atlas p k :=
  ⟨κ, T, a.count, a.world, a.block, a.center, a.speed, a.frame, a.test,
    a.assignment, a.event⟩

/-- All format bounds are chosen before the terminal slack tolerance. -/
theorem NormalizedRemainder.lift_terminal {p : Data} (hp : p.Valid)
    {M D : ℕ} {r h cap : ℝ} {s : KnownSequence p M D r h}
    (q : NormalizedRemainder s cap) (hr : 0 ≤ r)
    {b ζ : ℝ} (hb : Terminal q.data b) (hζ : 0 < ζ) : Terminal p (h + b + ζ) := by
  classical
  obtain ⟨Mₚ, Dₚ, hsample⟩ := hp.sampleProblem
  obtain ⟨M', D', hterminal⟩ := hb
  let M₀ := M + Mₚ + Nat.ceil (h + 1)
  let D₀ := max D Dₚ
  refine ⟨4 * M₀ + M' + 11, max D₀ D', fun ε hε => ?_⟩
  let a : ℝ := ε / 8
  have ha : 0 < a := by dsimp [a]; positivity
  have hNseq : Tendsto (fun k => p.N (s.index k)) atTop atTop :=
    hp.2.1.comp s.strictMono.tendsto_atTop
  have hconst : ∀ᶠ k in atTop, 4 ≤ p.N (s.index k) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hNseq).eventually_ge_atTop 4
  have hevent : ∀ᶠ k in atTop,
      (s.atlas k).κ ≤ p.N (s.index k) ^ a ∧
      ((s.atlas k).system.normZ (p.ω (s.index k)) (p.ν (s.index k)))⁻¹ ≤
        p.N (s.index k) ^ a ∧
      (∀ c, p.N (s.index k) ^ (-p.f p.L) * |((s.atlas k).Q c).det| ≤
        p.N (s.index k) ^ a *
          (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal *
          p.N (s.index k) ^ (-q.f (p.L - r))) ∧
      (2 : ℝ) ^ (s.atlas k).T ≤ p.N (s.index k) ^ (h + ζ) ∧
      (2 : ℝ) ^ (s.atlas k).T ≤ p.N (s.index k) ^ (h + 1) ∧
      4 ≤ p.N (s.index k) ^ (ε / 2) :=
    (s.slack_subpower a ha).and ((q.normalizer_subpower a ha).and
      ((q.terminal_comparison a ha).and ((s.time_upper ζ hζ).and
        ((s.time_upper 1 (by norm_num)).and hconst))))
  apply s.strictMono.tendsto_atTop.frequently
  apply ((hterminal a ha).and_eventually hevent).mono
  rintro k ⟨⟨child, hc1, hcK, hca, hct, hcvalid⟩,
    hpa, hZa, hcompare, hpt, hpoly, hfour⟩
  let parent := s.atlas k
  let N := p.N (s.index k)
  let Z := parent.system.normZ (p.ω (s.index k)) (p.ν (s.index k))
  let κ₁ := N ^ a
  let κ := 4 * parent.κ * child.κ * κ₁ / Z
  let δr := δ N r
  let δ' := δ N (p.L - r)
  let δL := δ N p.L
  have hN : 2 ≤ N := hp.1 _
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hpar1 : 1 ≤ parent.κ := s.slack_one k
  have hpar0 : 0 < parent.κ := by linarith
  have hchild0 : 0 < child.κ := by linarith
  have hκ₁ : 1 ≤ κ₁ := Real.one_le_rpow hN1 ha.le
  have hκ₁0 : 0 < κ₁ := by linarith
  have hδr : 0 < δr := by dsimp [δr, δ]; positivity
  have hδr1 : δr ≤ 1 :=
    Submission.Obl.k4_quadratic_atlas_normalization.delta_le_one hN1 hr
  have hδL : 0 < δL := by dsimp [δL, δ]; positivity
  have hδprod := delta_product_compare hN0 r (p.L - r)
  rw [show r + (p.L - r) = p.L by ring] at hδprod
  have hω := (hsample (s.index k)).weight_nonneg
  have hωsum := (hsample (s.index k)).weight_sum
  have hB : ∀ γ, 0 ≤ p.B (s.index k) γ := fun γ => ((hsample (s.index k)).scale_pos γ).le
  letI : ∀ γ, IsProbabilityMeasure (p.ν (s.index k) γ) := (hsample (s.index k)).prob
  obtain ⟨lst, hC, hsep, hlist, hcharts, hmass⟩ := s.valid k
  have hA : ∀ c, MeasurableSet (parent.A c) := by
    intro c
    exact (hcharts c).2.2.2.2.2.2.1
  have hZ : 0 < Z := parent.system.normZ_pos (p.ω (s.index k)) (p.ν (s.index k)) hω
    (q.prior_positive k) hpar0 hmass
  have hZ1 : Z ≤ 1 := parent.system.normZ_le_one (p.ω (s.index k)) (p.ν (s.index k))
    hω hωsum hA hsep
  have hbase : child.κ ≤ 4 * parent.κ * child.κ * κ₁ := by
    calc child.κ = 1 * 1 * child.κ * 1 := by ring
      _ ≤ 4 * parent.κ * child.κ * κ₁ := by gcongr <;> linarith
  have hbasep : parent.κ ≤ 4 * parent.κ * child.κ * κ₁ := by
    calc parent.κ = 1 * parent.κ * 1 * 1 := by ring
      _ ≤ 4 * parent.κ * child.κ * κ₁ := by gcongr <;> linarith
  have hκbase : 4 * parent.κ * child.κ * κ₁ ≤ κ := by
    dsimp [κ]
    rw [le_div_iff₀ hZ]
    exact mul_le_of_le_one_right (by positivity) hZ1
  have hκZ : child.κ ≤ κ * Z := by
    dsimp [κ]
    rw [div_mul_cancel₀ _ hZ.ne']
    exact hbase
  have hκone : 1 ≤ κ := hc1.trans (hbase.trans hκbase)
  have hκK : p.K (s.index k) ≤ κ := (s.slack_ambient k).trans (hbasep.trans hκbase)
  have hκsmall : κ ≤ N ^ ε := by
    calc κ = 4 * parent.κ * child.κ * (N ^ a) * Z⁻¹ := by rfl
      _ ≤ 4 * (N ^ a) * (N ^ a) * (N ^ a) * (N ^ a) := by
        gcongr
        exact hca
      _ = 4 * N ^ (ε / 2) := by
        rw [show ε / 2 = a + a + a + a by dsimp [a]; ring,
          Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0]
        ring
      _ ≤ N ^ (ε / 2) * N ^ (ε / 2) := mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = N ^ ε := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hgeo : parent.system.Geometry N parent.κ M₀ D₀ :=
    ((s.valid k).mono_format hN1 hpar0 hB (by dsimp [M₀]; omega)
      (by dsimp [D₀]; omega)).geometry
  have hT₀ : (2 : ℝ) ^ parent.T ≤ N ^ M₀ := by
    refine hpoly.trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hceil : h + 1 ≤ (Nat.ceil (h + 1) : ℝ) := Nat.le_ceil _
    have hle : (Nat.ceil (h + 1) : ℝ) ≤ M₀ := by exact_mod_cast (show Nat.ceil (h + 1) ≤ M₀ by dsimp [M₀]; omega)
    linarith
  have hEm := (hsample (s.index k)).event_meas
  have hEf : ∀ γ i, Normalization.PolynomialFormat N M₀ D₀
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ p.E (s.index k) γ} := by
    intro γ i
    exact Normalization.Fmt.mono ((hsample (s.index k)).event_fmt γ i)
      (pow_le_pow_right₀ hN1 (by dsimp [M₀]; omega)) (by dsimp [D₀]; omega)
  have hchild : child.system.Valid N child.κ (q.f (p.L - r)) δ' M' D'
      (q.data.ω k) (q.data.ν k) (q.data.E k) (q.data.B k) :=
    (child.trueAt_iff_valid M' D' q.data.L).mp hcvalid
  have hν' : ∀ c, q.data.ν k c =
      (p.ν (s.index k) (parent.system.world c) (parent.system.assignment c))⁻¹ •
      Measure.map (parent.system.frameOf c).normTraj
        ((p.ν (s.index k) (parent.system.world c)).restrict (parent.system.assignment c)) :=
    fun _ => rfl
  have hE' : ∀ c l t, l ∈ parent.system.assignment c →
      ((parent.system.frameOf c).normTraj l,
        (t - (parent.system.frameOf c).t₀) / (parent.system.frameOf c).q) ∈ q.data.E k c →
      (l, t) ∈ p.E (s.index k) (parent.system.world c) := by
    intro c l t _ ht
    have hdet : IsUnit (parent.system.frame c).det := isUnit_iff_ne_zero.mpr (hcharts c).1
    have hm := (parent.system.frameOf c).mem_of_mem_normEvent
      (parent.system.frameOf_q_pos c).ne' hdet (parent.system.assignment c)
        (parent.system.event c) l t (q.event_subset k c ht)
    exact ((hcharts c).2.2.2.2.2.2.2.2.2.2.1 _ hm).1
  have hB' : ∀ c, δr * q.data.B k c = p.B (s.index k) (parent.system.world c) := by
    intro c
    change δr * (p.B (s.index k) (parent.system.world c) / δr) = _
    field_simp
  have hω' : ∀ c, q.data.ω k c * Z = p.ω (s.index k) (parent.system.world c) *
      ((p.ν (s.index k) (parent.system.world c) (parent.system.assignment c)).toReal /
        (2 : ℝ) ^ parent.T) := by
    intro c
    change (_ / Z) * Z = _
    exact div_mul_cancel₀ _ hZ.ne'
  have hlift := Normalization.ChartSystem.lift_valid
    (M := 4 * M₀ + M' + 11) (D := max D₀ D')
    (p.ω (s.index k)) (p.ν (s.index k)) (p.E (s.index k)) (p.B (s.index k))
    parent.system hgeo hEm hEf (q.data.ω k) (q.data.ν k) (q.data.E k) (q.data.B k)
    hν' hE' hB' hω' child.system hchild hN hT₀ hδr hδr1
    (by norm_num : (1 : ℝ) ≤ 4) hδL hδprod.1 hδprod.2 hZ hκZ hcompare
    hpar1 hc1 hκ₁ hκbase (by omega) (by omega) hω hB
  let result : Atlas p (s.index k) := Atlas.ofSystem p (s.index k) (parent.T + child.T) κ
    (parent.system.lift (p.E (s.index k)) δr child.system)
  refine ⟨result, hκone, hκK, hκsmall, ?_, ?_⟩
  · change (2 : ℝ) ^ (parent.T + child.T) ≤ N ^ (h + b + ζ)
    rw [pow_add]
    calc (2 : ℝ) ^ parent.T * (2 : ℝ) ^ child.T ≤ N ^ (h + ζ) * N ^ b := by
          exact mul_le_mul hpt hct (by positivity) (by positivity)
      _ = N ^ (h + b + ζ) := by rw [← Real.rpow_add hN0]; congr 1; ring
  · exact (result.trueAt_iff_valid _ _ p.L).mpr hlift

/-- Genuine child horizons compose additively through the normalized family. -/
theorem NormalizedRemainder.horizon_bound (hi : InitialHorizon) {p : Data} (hp : p.Valid)
    {M D : ℕ} {r h cap : ℝ} {s : KnownSequence p M D r h}
    (q : NormalizedRemainder s cap) (hr : 0 ≤ r) :
    horizon p ≤ h + horizon q.data :=
  horizon_composition hi hp q.valid fun _ hb _ hε => q.lift_terminal hp hr hb hε

end Submission.Obl.k4_local_remainder_horizon_transfer
