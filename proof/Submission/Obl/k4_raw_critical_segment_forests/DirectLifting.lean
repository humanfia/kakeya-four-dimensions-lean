import Submission.Obl.k4_raw_critical_segment_forests.PureModels
import Submission.Obl.k4_raw_critical_segment_forests.NestedTransfer
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalizer
import Submission.Obl.k4_remainder_pure_profile_normalization.RemainderData
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.SampleNormalize

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_remainder_pure_profile_normalization
  (KnownSequence NormalizedRemainder)

noncomputable section

/-- A finite system, with its full geometry retained in the forest atlas record. -/
def pureSystemAtlas (p : PureData) (k T : ℕ)
    (a : k4_remainder_pure_profile_normalization.Normalization.ChartSystem (p.W k) T) :
    Atlas (fromPure p) k :=
  ⟨T, a.count, a.world, a.block, a.center, a.speed, a.frame, a.test,
    a.assignment, a.event, fun _ _ => ∅⟩

/-- Direct finite lifting from the accepted normalized remainder. The estimates
follow o147's RemainderLifting, but this conclusion retains every geometric field,
parent map, time identity and exact Jacobian product required by the forest. -/
theorem atlasLift_of_normalized_remainder {p : PureData} (hp : p.Valid)
    {M D : ℕ} {r h cap : ℝ} {s : KnownSequence p M D r h}
    (q : NormalizedRemainder s cap) (hr : 0 ≤ r) :
    AtlasLift (fromPure p) (fromPure q.data) s.index
      (fun n => atlasFromPure (s.atlas n)) := by
  classical
  obtain ⟨Mp, Dp, hs⟩ := hp.sampleProblem
  let M₀ := M + Mp + Nat.ceil (h + 1)
  let D₀ := max D Dp
  intro M' D'
  refine ⟨4 * M₀ + M' + 11, max D₀ D', fun e he => ?_⟩
  let a : ℝ := e / 8
  have ha : 0 < a := by dsimp [a]; positivity
  have hNt : Tendsto (fun n => p.N (s.index n)) atTop atTop :=
    hp.2.1.comp s.strictMono.tendsto_atTop
  have hfour : ∀ᶠ n in atTop, 4 ≤ p.N (s.index n) ^ (e / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < e / 2)).comp hNt).eventually_ge_atTop 4
  refine ⟨a, ha, ?_⟩
  filter_upwards [s.slack_subpower a ha, q.normalizer_subpower a ha,
    q.terminal_comparison a ha, s.time_upper 1 (by norm_num), hfour] with n hpa hZa hcal hpoly hfour
  intro κ' child hc1 hcK hca hc
  let parent := s.atlas n
  let N := p.N (s.index n)
  let Z := parent.system.normZ (p.ω (s.index n)) (p.ν (s.index n))
  let κ₁ := N ^ a
  let κ := 4 * parent.κ * κ' * κ₁ / Z
  let δr := k4_remainder_pure_profile_normalization.δ N r
  let δ' := k4_remainder_pure_profile_normalization.δ N (p.L - r)
  let δL := k4_remainder_pure_profile_normalization.δ N p.L
  have hN : 2 ≤ N := hp.1 _
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hpar1 : 1 ≤ parent.κ := s.slack_one n
  have hpar0 : 0 < parent.κ := by linarith
  have hchild0 : 0 < κ' := by linarith
  have hκ₁ : 1 ≤ κ₁ := Real.one_le_rpow hN1 ha.le
  have hκ₁0 : 0 < κ₁ := by linarith
  have hδr : 0 < δr := by dsimp [δr, k4_remainder_pure_profile_normalization.δ]; positivity
  have hδr1 : δr ≤ 1 :=
    k4_quadratic_atlas_normalization.delta_le_one hN1 hr
  have hδL : 0 < δL := by dsimp [δL, k4_remainder_pure_profile_normalization.δ]; positivity
  have hδprod := k4_remainder_pure_profile_normalization.delta_product_compare hN0 r (p.L - r)
  rw [show r + (p.L - r) = p.L by ring] at hδprod
  have hω := (hs (s.index n)).weight_nonneg
  have hωsum := (hs (s.index n)).weight_sum
  have hB : ∀ γ, 0 ≤ p.B (s.index n) γ := fun γ => ((hs (s.index n)).scale_pos γ).le
  letI : ∀ γ, IsProbabilityMeasure (p.ν (s.index n) γ) := (hs (s.index n)).prob
  obtain ⟨lst, hC, hsep, hlist, hcharts, hmass⟩ := s.valid n
  have hA : ∀ c, MeasurableSet (parent.A c) := fun c => (hcharts c).2.2.2.2.2.2.1
  have hZ : 0 < Z := parent.system.normZ_pos (p.ω (s.index n)) (p.ν (s.index n)) hω
    (q.prior_positive n) hpar0 hmass
  have hZ1 : Z ≤ 1 := parent.system.normZ_le_one (p.ω (s.index n)) (p.ν (s.index n))
    hω hωsum hA hsep
  have hbase : κ' ≤ 4 * parent.κ * κ' * κ₁ := by
    calc κ' = 1 * 1 * κ' * 1 := by ring
      _ ≤ 4 * parent.κ * κ' * κ₁ := by gcongr <;> linarith
  have hbasep : parent.κ ≤ 4 * parent.κ * κ' * κ₁ := by
    calc parent.κ = 1 * parent.κ * 1 * 1 := by ring
      _ ≤ 4 * parent.κ * κ' * κ₁ := by gcongr <;> linarith
  have hκbase : 4 * parent.κ * κ' * κ₁ ≤ κ := by
    dsimp [κ]
    rw [le_div_iff₀ hZ]
    exact mul_le_of_le_one_right (by positivity) hZ1
  have hκZ : κ' ≤ κ * Z := by
    dsimp [κ]
    rw [div_mul_cancel₀ _ hZ.ne']
    exact hbase
  have hκone : 1 ≤ κ := hc1.trans (hbase.trans hκbase)
  have hκK : p.K (s.index n) ≤ κ := (s.slack_ambient n).trans (hbasep.trans hκbase)
  have hκsmall : κ ≤ N ^ e := by
    calc κ = 4 * parent.κ * κ' * (N ^ a) * Z⁻¹ := by rfl
      _ ≤ 4 * (N ^ a) * (N ^ a) * (N ^ a) * (N ^ a) := by
        gcongr
        exact hca
      _ = 4 * N ^ (e / 2) := by
        rw [show e / 2 = a + a + a + a by dsimp [a]; ring,
          Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0]
        ring
      _ ≤ N ^ (e / 2) * N ^ (e / 2) := mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = N ^ e := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hgeo : parent.system.Geometry N parent.κ M₀ D₀ :=
    ((s.valid n).mono_format hN1 hpar0 hB (by dsimp [M₀]; omega)
      (by dsimp [D₀]; omega)).geometry
  have hT₀ : (2 : ℝ) ^ parent.T ≤ N ^ M₀ := by
    refine hpoly.trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hceil : h + 1 ≤ (Nat.ceil (h + 1) : ℝ) := Nat.le_ceil _
    have hle : (Nat.ceil (h + 1) : ℝ) ≤ M₀ := by exact_mod_cast
      (show Nat.ceil (h + 1) ≤ M₀ by dsimp [M₀]; omega)
    linarith
  have hEm := (hs (s.index n)).event_meas
  have hEf : ∀ γ i, k4_remainder_pure_profile_normalization.Normalization.PolynomialFormat N M₀ D₀
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ p.E (s.index n) γ} := by
    intro γ i
    exact k4_remainder_pure_profile_normalization.Normalization.Fmt.mono
      ((hs (s.index n)).event_fmt γ i)
      (pow_le_pow_right₀ hN1 (by dsimp [M₀]; omega)) (by dsimp [D₀]; omega)
  let cs : k4_remainder_pure_profile_normalization.Normalization.ChartSystem parent.C child.T :=
    ⟨child.C, child.γ, child.j, child.c, child.u, child.Q, child.R, child.A, child.F⟩
  have hchild : cs.Valid N κ' (q.f (p.L - r)) δ' M' D'
      (q.data.ω n) (q.data.ν n) (q.data.E n) (q.data.B n) := hc
  have hν' : ∀ c, q.data.ν n c =
      (p.ν (s.index n) (parent.system.world c) (parent.system.assignment c))⁻¹ •
      Measure.map (parent.system.frameOf c).normTraj
        ((p.ν (s.index n) (parent.system.world c)).restrict (parent.system.assignment c)) :=
    fun _ => rfl
  have hF' : ∀ c l t, l ∈ parent.system.assignment c →
      ((parent.system.frameOf c).normTraj l,
        (t - (parent.system.frameOf c).t₀) / (parent.system.frameOf c).q) ∈ q.data.E n c →
      (l, t) ∈ parent.F c := by
    intro c l t _ ht
    have hdet : IsUnit (parent.system.frame c).det := isUnit_iff_ne_zero.mpr (hcharts c).1
    exact (parent.system.frameOf c).mem_of_mem_normEvent
      (parent.system.frameOf_q_pos c).ne' hdet (parent.system.assignment c)
        (parent.system.event c) l t (q.event_subset n c ht)
  have hE' : ∀ c l t, l ∈ parent.system.assignment c →
      ((parent.system.frameOf c).normTraj l,
        (t - (parent.system.frameOf c).t₀) / (parent.system.frameOf c).q) ∈ q.data.E n c →
      (l, t) ∈ p.E (s.index n) (parent.system.world c) := by
    intro c l t hl ht
    exact ((hcharts c).2.2.2.2.2.2.2.2.2.2.1 _ (hF' c l t hl ht)).1
  have hB' : ∀ c, δr * q.data.B n c = p.B (s.index n) (parent.system.world c) := by
    intro c
    change δr * (p.B (s.index n) (parent.system.world c) / δr) = _
    field_simp
  have hω' : ∀ c, q.data.ω n c * Z = p.ω (s.index n) (parent.system.world c) *
      ((p.ν (s.index n) (parent.system.world c) (parent.system.assignment c)).toReal /
        (2 : ℝ) ^ parent.T) := by
    intro c
    change (_ / Z) * Z = _
    exact div_mul_cancel₀ _ hZ.ne'
  have hlift := k4_remainder_pure_profile_normalization.Normalization.ChartSystem.lift_valid
    (M := 4 * M₀ + M' + 11) (D := max D₀ D')
    (p.ω (s.index n)) (p.ν (s.index n)) (p.E (s.index n)) (p.B (s.index n))
    parent.system hgeo hEm hEf (q.data.ω n) (q.data.ν n) (q.data.E n) (q.data.B n)
    hν' hE' hB' hω' cs hchild hN hT₀ hδr hδr1
    (by norm_num : (1 : ℝ) ≤ 4) hδL hδprod.1 hδprod.2 hZ hκZ hcal
    hpar1 hc1 hκ₁ hκbase (by omega) (by omega) hω hB
  let ls := parent.system.lift (p.E (s.index n)) δr cs
  let result : Atlas (fromPure p) (s.index n) :=
    pureSystemAtlas p (s.index n) (parent.T + child.T) ls
  refine ⟨κ, result, child.γ, fun b => b, hκone, hκK, hκsmall, rfl, hlift, ?_, ?_⟩
  · intro b
    refine ⟨rfl, Set.inter_subset_left, ?_, ?_, ?_⟩
    · intro z hz
      change z ∈ ls.event b at hz
      exact hF' (child.γ b) z.1 z.2 hz.2.1
        (((hchild.2.2.1 b).2.2.2.2.2.2.2.2.2.2.1 _ hz.2.2).1)
    · change ((parent.j (child.γ b) : ℕ) : ℝ) / (2 : ℝ) ^ parent.T ≤
        ((k4_native_finite_terminal_atlas_lift.compositeBlock
          (parent.j (child.γ b)) (child.j b) : ℕ) : ℝ) / (2 : ℝ) ^ (parent.T + child.T)
      rw [k4_native_finite_terminal_atlas_lift.compositeBlock_lower]
      have : (0 : ℝ) ≤ ((child.j b : ℕ) : ℝ) / (2 : ℝ) ^ child.T /
          (2 : ℝ) ^ parent.T := by positivity
      linarith
    · change (((k4_native_finite_terminal_atlas_lift.compositeBlock
          (parent.j (child.γ b)) (child.j b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (parent.T + child.T) ≤
        (((parent.j (child.γ b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ parent.T
      rw [k4_native_finite_terminal_atlas_lift.compositeBlock_upper]
      have hj : ((child.j b : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ child.T := by exact_mod_cast (child.j b).isLt
      have h1 : (((child.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ child.T ≤ 1 :=
        (div_le_one (by positivity)).mpr hj
      have h2 := div_le_div_of_nonneg_right h1 (show (0 : ℝ) ≤ (2 : ℝ) ^ parent.T by positivity)
      rw [add_div (((parent.j (child.γ b) : ℕ) : ℝ)) 1]
      linarith
  · intro b
    change |Matrix.det (parent.Q (child.γ b) * child.Q b)| * (4 : ℝ) ^ (parent.T + child.T) =
      (|Matrix.det (parent.Q (child.γ b))| * (4 : ℝ) ^ parent.T) *
        (|Matrix.det (child.Q b)| * (4 : ℝ) ^ child.T)
    rw [Matrix.det_mul, abs_mul, pow_add]
    ring

end
end Submission.Obl.k4_raw_critical_segment_forests
