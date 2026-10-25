import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic
import Submission.Obl.k4_scalar_angular_pair_agreement.Extrapolation
import Submission.Obl.k4_scalar_angular_pair_agreement.ThreeLines
import Submission.Obl.k4_scalar_angular_pair_agreement.VelocityBins
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open Set MeasureTheory
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The closed dyadic interval written with its left endpoint and length. -/
theorem I_eq_time_block (T : ℕ) (j : Fin (2 ^ T)) :
    I T j = Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j : ℕ) : ℝ) / (2 : ℝ) ^ T) + ((2 : ℝ) ^ T)⁻¹) := by
  simpa only [one_div, Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block, I] using
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_eq T j

/-- Membership in a dyadic block is a midpoint distance bound. -/
theorem mem_I_iff_mid (T : ℕ) (j : Fin (2 ^ T)) (t : ℝ) :
    t ∈ I T j ↔ |t - mid T j| ≤ ((2 : ℝ) ^ T)⁻¹ / 2 := by
  simp only [I, mid, Set.mem_Icc, abs_le, div_eq_mul_inv]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith

section Charts

variable {p : Code} {B k T n : ℕ} {r b₀ h θ : ℝ} {flag : Bool}
  {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
  {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
  {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
  {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
  {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}

/-- Both chart residuals extend from their assigned fine block to its coarse block. -/
theorem chart_extended_residual
    (hdata : ChartData p B r b₀ h θ flag k T n γ j A C u v J P Λ)
    {T₁ : ℕ} (hT : T₁ ≤ T) (b : Fin (2 ^ T₁)) (i : Fin n)
    (hsub : I T (j i) ⊆ I T₁ b) (l : ℕ × (Fin 5 → ℝ)) (hl : l ∈ A i)
    (t : ℝ) (ht : t ∈ I T₁ b) :
    |y l t - u i - t * v i| ≤
      (1 + 2 * (2 : ℝ) ^ (T - T₁)) * (N p k ^ θ * J i) ∧
    |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤
      48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * (N p k ^ θ * N p k ^ (-r)) := by
  obtain ⟨_, _, _, _, _, hP, _, _, _, _, hfit, _⟩ := hdata.2.2.2.2.2.1 i
  have hsub' := hsub
  rw [I_eq_time_block, I_eq_time_block] at hsub'
  have ht' := ht
  rw [I_eq_time_block] at ht'
  have hratio : ((2 : ℝ) ^ T₁)⁻¹ / ((2 : ℝ) ^ T)⁻¹ = (2 : ℝ) ^ (T - T₁) := by
    rw [div_inv_eq_mul, two_pow_split hT]
    field_simp
  have hyfit : ∀ s ∈ Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j i : ℕ) : ℝ) / (2 : ℝ) ^ T) + ((2 : ℝ) ^ T)⁻¹),
      |y l s - u i - s * v i| ≤ N p k ^ θ * J i := by
    simpa only [← I_eq_time_block] using (fun s hs => (hfit l hl s hs).1)
  have hxfit : ∀ s ∈ Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j i : ℕ) : ℝ) / (2 : ℝ) ^ T) + ((2 : ℝ) ^ T)⁻¹),
      |x l s - MvPolynomial.eval ![s, y l s] (P i)| ≤ N p k ^ θ * N p k ^ (-r) := by
    simpa only [← I_eq_time_block] using (fun s hs => (hfit l hl s hs).2)
  constructor
  · have hh := trajectory_affine_extrapolation l (u i) (v i)
      (show 0 < ((2 : ℝ) ^ T)⁻¹ by positivity) hsub' hyfit t ht'
    simpa only [mul_div_assoc, hratio] using hh
  · have hh := trajectory_predictor_extrapolation l (P i) hP
      (show 0 < ((2 : ℝ) ^ T)⁻¹ by positivity) hsub' hxfit t ht'
    simpa only [hratio] using hh

/-- A common trajectory is in a subpower spatial strip at the coarse midpoint. -/
theorem chart_midpoint_strip
    (hdata : ChartData p B r b₀ h θ flag k T n γ j A C u v J P Λ)
    {T₁ : ℕ} (hT : T₁ ≤ T) (b : Fin (2 ^ T₁)) (i : Fin n)
    (hsub : I T (j i) ⊆ I T₁ b) (l : ℕ × (Fin 5 → ℝ)) (hl : l ∈ A i)
    (hN : 1 ≤ N p k) (_hθ : 0 ≤ θ) :
    |l.2 0 + l.2 1 * mid T₁ b - (u i + mid T₁ b * v i)| ≤
      (4 * (N p k ^ θ) ^ 2) * ((2 : ℝ) ^ T₁)⁻¹ := by
  have hm : mid T₁ b ∈ I T₁ b := (mem_I_iff_mid _ _ _).mpr (by simp; positivity)
  have hres := (chart_extended_residual hdata hT b i hsub l hl _ hm).1
  have hJ := (hdata.2.2.2.2.2.1 i).2.2.2.1
  have hJpos := (hdata.2.2.2.2.2.1 i).2.1
  have hR : 1 ≤ (2 : ℝ) ^ (T - T₁) := one_le_pow₀ (by norm_num)
  have hpow : 0 ≤ N p k ^ θ := Real.rpow_nonneg (by linarith) _
  have hratio : (2 : ℝ) ^ (T - T₁) * ((2 : ℝ) ^ T)⁻¹ = ((2 : ℝ) ^ T₁)⁻¹ := by
    rw [two_pow_split hT]
    field_simp
  calc
    _ = |y l (mid T₁ b) - u i - mid T₁ b * v i| := by congr 1; dsimp [y]; ring
    _ ≤ (1 + 2 * (2 : ℝ) ^ (T - T₁)) * (N p k ^ θ * J i) := hres
    _ ≤ (3 * (2 : ℝ) ^ (T - T₁)) *
        (N p k ^ θ * (N p k ^ θ / (2 : ℝ) ^ T)) := by gcongr; linarith
    _ = (3 * (N p k ^ θ) ^ 2) * ((2 : ℝ) ^ T₁)⁻¹ := by
      rw [div_eq_mul_inv]
      calc
        _ = (3 * (N p k ^ θ) ^ 2) *
            ((2 : ℝ) ^ (T - T₁) * ((2 : ℝ) ^ T)⁻¹) := by ring
        _ = _ := by rw [hratio]
    _ ≤ (4 * (N p k ^ θ) ^ 2) * ((2 : ℝ) ^ T₁)⁻¹ := by gcongr; norm_num

/-- Every trajectory assigned to two labels sees their predictor difference uniformly
small throughout any common coarse block. -/
theorem chart_common_predictor_bound
    (hdata : ChartData p B r b₀ h θ flag k T n γ j A C u v J P Λ)
    {T₁ : ℕ} (hT : T₁ ≤ T) (b : Fin (2 ^ T₁)) (i i' : Fin n)
    (hi : I T (j i) ⊆ I T₁ b) (hi' : I T (j i') ⊆ I T₁ b)
    (l : ℕ × (Fin 5 → ℝ)) (hl : l ∈ A i) (hl' : l ∈ A i')
    (t : ℝ) (ht : t ∈ I T₁ b) :
    |MvPolynomial.eval ![t, y l t] (P i - P i')| ≤
      96 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * (N p k ^ θ * N p k ^ (-r)) := by
  have h₁ := (chart_extended_residual hdata hT b i hi l hl t ht).2
  have h₂ := (chart_extended_residual hdata hT b i' hi' l hl' t ht).2
  rw [map_sub]
  calc
    _ = |(x l t - MvPolynomial.eval ![t, y l t] (P i')) -
        (x l t - MvPolynomial.eval ![t, y l t] (P i))| := by congr 1; ring
    _ ≤ |x l t - MvPolynomial.eval ![t, y l t] (P i')| +
        |x l t - MvPolynomial.eval ![t, y l t] (P i)| := abs_sub _ _
    _ ≤ 96 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * (N p k ^ θ * N p k ^ (-r)) := by linarith

/-- A bad pair of old labels has common trajectories in at most six angular bins.
The numerical hypothesis separates local geometry from the later power bookkeeping. -/
theorem bad_chart_common_velocity_bins
    (hdata : ChartData p B (L p) b₀ h θ flag k T n γ j A C u v J P Λ)
    (hN : 1 ≤ N p k) (hθ : 0 ≤ θ)
    {T₁ : ℕ} (hT : T₁ ≤ T) (b : Fin (2 ^ T₁)) (i i' : Fin n)
    (hi : I T (j i) ⊆ I T₁ b) (hi' : I T (j i') ⊆ I T₁ b)
    {w a e : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hnumeric :
      2048000 * (96 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * (N p k ^ θ * N p k ^ (-L p))) *
        (4 * (N p k ^ θ) ^ 2) ^ 9 / w ^ 9 ≤ N p k ^ (-L p + a * e))
    (hbad : ¬ Agrees p k T₁ n u v P a e b i i') :
    ∃ F : Finset ℤ, F.card ≤ 6 ∧
      ∀ l : ℕ × (Fin 5 → ℝ), l ∈ A i → l ∈ A i' → ⌊l.2 1 / w⌋ ∈ F := by
  classical
  let Svel : Set ℝ := {s | ∃ l : ℕ × (Fin 5 → ℝ), l ∈ A i ∧ l ∈ A i' ∧ l.2 1 = s}
  obtain ⟨_, _, _, _, _, hPi, _, hAi, _, _, _, _⟩ := hdata.2.2.2.2.2.1 i
  obtain ⟨_, _, _, _, _, hPi', _, _, _, _, _, _⟩ := hdata.2.2.2.2.2.1 i'
  have hQ : (P i - P i').totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le hPi hPi')
  have hNθ : 1 ≤ N p k ^ θ := Real.one_le_rpow hN hθ
  have hH : 1 ≤ 4 * (N p k ^ θ) ^ 2 := by nlinarith
  have hnot : ∀ s₀ ∈ Svel, ∀ s₁ ∈ Svel, ∀ s₂ ∈ Svel,
      w ≤ |s₀ - s₁| → w ≤ |s₀ - s₂| → w ≤ |s₁ - s₂| → False := by
    intro s₀ hs₀ s₁ hs₁ s₂ hs₂ h01 h02 h12
    obtain ⟨l₀, hl₀, hl₀', rfl⟩ := hs₀
    obtain ⟨l₁, hl₁, hl₁', rfl⟩ := hs₁
    obtain ⟨l₂, hl₂, hl₂', rfl⟩ := hs₂
    let ls : Fin 3 → ℕ × (Fin 5 → ℝ) := ![l₀, l₁, l₂]
    have hls : ∀ q, ls q ∈ A i ∧ ls q ∈ A i' := by
      intro q
      fin_cases q
      · exact ⟨hl₀, hl₀'⟩
      · exact ⟨hl₁, hl₁'⟩
      · exact ⟨hl₂, hl₂'⟩
    apply hbad
    intro t ht z hz
    have hbound := three_lines_centered_box_bound (P i - P i') hQ
      (q := ((2 : ℝ) ^ T₁)⁻¹) (m := mid T₁ b) (c := u i + mid T₁ b * v i)
      (E := 96 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * (N p k ^ θ * N p k ^ (-L p)))
      (H := 4 * (N p k ^ θ) ^ 2)
      (by positivity) (by positivity) hH hw hw1
      (fun q => (ls q).2 0) (fun q => (ls q).2 1)
      (by
        intro q
        have hval := (hAi (ls q) (hls q).1).2 1
        nlinarith)
      (by
        intro q
        exact chart_midpoint_strip hdata hT b i hi (ls q) (hls q).1 hN hθ)
      (by
        intro q q' hqq'
        fin_cases q <;> fin_cases q' <;> try { norm_num at hqq' } <;> norm_num [ls]
        all_goals first | exact h01 | exact h02 | exact h12 |
          simpa only [abs_sub_comm] using h01 | simpa only [abs_sub_comm] using h02 |
          simpa only [abs_sub_comm] using h12)
      (by
        intro q s hs
        have hs' : s ∈ I T₁ b := (mem_I_iff_mid _ _ _).mpr hs
        simpa only [y, mul_comm] using
          chart_common_predictor_bound hdata hT b i i' hi hi' (ls q)
            (hls q).1 (hls q).2 s hs')
      t z ((mem_I_iff_mid _ _ _).mp ht) hz
    exact hbound.trans hnumeric
  obtain ⟨F, hF, hmem⟩ := no_three_separated_velocity_bins Svel hw hnot
  exact ⟨F, hF, fun l hl hl' => hmem (l.2 1) ⟨l, hl, hl', rfl⟩⟩

end Charts

end Submission.Obl.k4_scalar_angular_pair_agreement
