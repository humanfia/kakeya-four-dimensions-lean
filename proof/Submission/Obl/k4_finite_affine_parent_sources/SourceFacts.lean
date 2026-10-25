-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceInputs

/-!
# All facts of a source stage from its true inputs

`SourceData.facts_of_inputs` produces `SourceData.Facts` from the schedule inequalities, the
largeness of the sample, the problem facts and the true inputs `SourceData.Inputs`, for the
source depth map, the rotated parent frame and the model loss `K = (Nk^(uL))^θ`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W}

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **The facts of a source stage from its true inputs.** -/
theorem facts_of_inputs (D : SourceData p) {n M Mb : ℕ} {d₁ S ρ gain ε u J τ mesh : ℝ}
    {H : Fin W → Set Incidence}
    (hprof : ∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    (hνw : IsProbabilityMeasure (ν D.w₀)) (hBw : 0 < B D.w₀)
    (hBp : B D.w₀ ≤ Nk ^ Mb) (hBi : (B D.w₀)⁻¹ ≤ Nk ^ Mb)
    (hdepth : D.depth = sourceDepth m sg D.i₀ u)
    (hframe : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hK : D.K = (Nk ^ (u * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1))))
    (hn : 2 ≤ n) (hM : budgetExp L ℓ Mp Mb ≤ M) (hd₁ : 0 ≤ d₁) (hκ₁ : 0 < κ₁)
    (hκ₁' : κ₁ ≤ 1) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 4) (hε : 0 < ε) (hu : 0 < u)
    (hun : u * n ≤ 1 / 8) (hg : 0 < gain) (hg' : gain ≤ ρ * u / (1000000 * ((n : ℝ) + 1)))
    (hmesh0 : 0 ≤ mesh) (hmesh : ∀ i, i + 1 < m → sg (i + 1) - sg i ≤ mesh) (hm : 0 < m)
    (hsg1 : sg (m - 1) = 1) (hδ₀ : 0 ≤ δ₀) (hL : 0 < L)
    (herr1 : κ₁ * mesh + 2 * δ₀ ≤ u * (ρ / (1000000 * ((n : ℝ) + 1))))
    (herr2 : mesh + 2 * δ₀ ≤ u * (ρ / (1000000 * ((n : ℝ) + 1))) / 2)
    (herr3 : 6 * δ₀ + d₁ * (mesh + 2 * δ₀) + ℓ * mesh ≤
      u * (ρ / (1000000 * ((n : ℝ) + 1))) / 2)
    (hgap : 2 * δ₀ ≤ κ₁ * (u / n - mesh)) (hroom : sg D.i₀ + u + δ₀ ≤ 1 / 2)
    (hsg0 : 0 ≤ sg D.i₀)
    (hNk : 2 ≤ Nk) (h100 : 100 ≤ Nk ^ (ε / 1000000)) (hNst : (n : ℝ) + 2 ≤ Nk ^ (u * L))
    (hJ1 : 1 ≤ J) (hJ2 : J ≤ Nk ^ (ε / 1000000)) (hJκ : 18 * p.κ ≤ J) (hJτ : τ⁻¹ ≤ J)
    (hJN : J ≤ Nk) (hτ : 0 < τ) (hKτ : τ⁻¹ ≤ D.K) (hKκ : 18 * p.κ ≤ D.K)
    (hthickK : 2 * p.κ * Nk ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 2) ≤ D.K)
    (hpriorK : p.κ ^ 2 * Nk ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 2) ≤ D.K)
    (hin : D.Inputs n m d₁ ℓ S u Nk L τ ν B H) :
    D.Facts n M m d₁ κ₁ ℓ S ρ gain ε u Nk L J τ ν B H := by
  set θ := ρ / (1000000 * ((n : ℝ) + 1)) with hθ
  have hN1 : (1 : ℝ) ≤ Nk := by linarith
  have hN0 : 0 < Nk := by linarith
  have hθ0 : 0 < θ := by positivity
  have hi₀ : D.i₀ < m := hp.label_level D.parent
  have hu1 : u ≤ 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hroom' : sg D.i₀ + u ≤ sg (m - 1) := by rw [hsg1]; linarith
  -- the parent's depth
  obtain ⟨hr₀e, hr₀pos, hT₀lo, hT₀hi, -⟩ := hp.level_bounds D.i₀ hi₀
  rw [abs_le] at hr₀e
  have hr₀L : p.r D.i₀ ≤ L / 2 := by
    have h1 : sg D.i₀ + δ₀ ≤ 1 / 2 := by linarith
    have h2 : (sg D.i₀ + δ₀) * L ≤ 1 / 2 * L := mul_le_mul_of_nonneg_right h1 hL.le
    have h3 : p.r D.i₀ ≤ sg D.i₀ * L + δ₀ * L := by linarith [hr₀e.2]
    linarith
  -- depths of the labels
  have hdep : ∀ x, 0 ≤ x → x ≤ 1 →
      |p.r (D.depth x) - p.r D.i₀ - u * L * x| ≤ (mesh + 2 * δ₀) * L ∧
        p.r (D.depth x) ≤ (sg D.i₀ + u + δ₀) * L := fun x hx0 hx1 => by
    rw [hdepth]
    exact sourceDepth_actual hp hm hi₀ hu.le hmesh0 hmesh hroom' hL.le hx0 hx1
  have hninv : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → 0 ≤ s := fun s hs =>
    le_trans (inv_nonneg.mpr (Nat.cast_nonneg n)) hs
  have hKone : 1 ≤ D.K := by
    rw [hK]; exact Real.one_le_rpow (by linarith) hθ0.le
  refine
    { num := ⟨hn, ?_, hNk, hL, hd₁, hℓ, hρ, hρ', hε, hu, hun, hg, hg', h100, by linarith,
        hKone, le_of_eq hK⟩
      N_ge := hNst
      νw := hνw
      Bw := hBw
      π_prob := hin.π_prob
      frame_eq := hframe
      J_one := hJ1
      J_le := hJ2
      J_slack := hJκ
      τ_pos := hτ
      J_τ := hJτ
      K_τ := hKτ
      K_slack := hKκ
      S_meas := hin.S_meas
      S_res := hin.S_res
      S_open := hin.S_open
      S_term := hin.S_term
      S_end := hin.S_end
      prior_pos := prior_pos_of_valid hp hN0 D.parent
      parent_floor := hin.parent_floor
      depth_mono := by rw [hdepth]; exact sourceDepth_mono m sg D.i₀ hu.le
      depth_ge := fun s => by rw [hdepth]; exact sourceDepth_ge sg hi₀ hu.le s
      depth_lt := fun s => by rw [hdepth]; exact sourceDepth_lt hm sg D.i₀ u s
      depth_err := ?_
      depth_half := ?_
      size := ?_
      P_coeff := ?_
      time := ?_
      thick := ?_
      label := ?_
      vel := hin.vel
      eh2 := hin.eh2 }
  · unfold budgetExp at hM; omega
  · intro s hs1 hs2
    have h := (hdep s (hninv s hs1) hs2).1
    have hmθ : (mesh + 2 * δ₀) ≤ u * θ := by linarith
    calc _ ≤ (mesh + 2 * δ₀) * L := h
      _ ≤ (u * θ) * L := mul_le_mul_of_nonneg_right hmθ hL.le
      _ = ρ * u * L / (1000000 * ((n : ℝ) + 1)) := by rw [hθ]; ring
  · intro s hs1 hs2
    have h := (hdep s (hninv s hs1) hs2).2
    have h2 : (sg D.i₀ + u + δ₀) * L ≤ 1 / 2 * L := mul_le_mul_of_nonneg_right hroom hL.le
    linarith
  · -- size
    have hT₀ : (2 : ℝ) ^ p.T D.i₀ ≤ Nk ^ (2 * ⌈L⌉₊) := by
      refine hT₀hi.trans (rpow_le_npow hN1 ?_)
      have hLc : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
      have h1 : κ₁ * sg D.i₀ ≤ 1 / 2 := by
        have : sg D.i₀ ≤ 1 / 2 := by linarith
        calc κ₁ * sg D.i₀ ≤ 1 * sg D.i₀ := mul_le_mul_of_nonneg_right hκ₁' hsg0
          _ ≤ 1 / 2 := by linarith
      have h2 : δ₀ ≤ 1 / 2 := by linarith
      have h3 : (κ₁ * sg D.i₀ + δ₀) * L ≤ 1 * L :=
        mul_le_mul_of_nonneg_right (by linarith) hL.le
      push_cast
      linarith
    refine (source_size hp D hNk hframe hBp hBw hBi hr₀pos.le (by linarith) hL.le hℓ.le
      hu.le hu1 (by linarith) hJN hT₀).trans (pow_le_pow_right₀ hN1 hM)
  · -- P coefficients
    have hc := hp.chart D.parent
    exact (source_test_coeff hp D hNk hframe hBw hBi hr₀pos.le (by linarith) (p.test D.parent)
      hc.2.2.2.2.1 hc.2.2.2.2.2.1).trans (pow_le_pow_right₀ hN1 hM)
  · -- time
    intro s hs1 hs2
    have hs0 := hninv s hs1
    have hgs : 2 * δ₀ ≤ κ₁ * (u * s - mesh) := by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have h1 : u / n ≤ u * s := by
        rw [div_le_iff₀ hn0]
        have := mul_le_mul_of_nonneg_left ((inv_le_iff_one_le_mul₀ hn0).mp hs1) hu.le
        nlinarith
      have h2 : κ₁ * (u / n - mesh) ≤ κ₁ * (u * s - mesh) :=
        mul_le_mul_of_nonneg_left (by linarith) hκ₁.le
      linarith
    show (Nk ^ (u * L)) ^ (κ₁ * s) / D.K ≤ (2 : ℝ) ^ (p.T (D.depth s) - p.T D.i₀) ∧
      (2 : ℝ) ^ (p.T (D.depth s) - p.T D.i₀) ≤ D.K * (Nk ^ (u * L)) ^ (κ₁ * s)
    rw [hdepth]
    exact time_field hp hN1 hL.le hm hi₀ hu.le hmesh0 hmesh hroom' hκ₁.le herr1 hK hs0 hs2 hgs
  · -- thick
    intro s hs1 hs2
    rw [hdepth]
    exact thick_field hp hN1 hL.le hm hi₀ hu.le hmesh0 hmesh hroom' herr2 hK hthickK
      (hninv s hs1) hs2
  · -- label
    intro s hs1 hs2 i
    have hs0 := hninv s hs1
    have hge : D.i₀ ≤ D.depth s := by rw [hdepth]; exact sourceDepth_ge sg hi₀ hu.le s
    have hcold := hp.chart (D.old s i)
    have hw : p.world (D.old s i) = D.w₀ := (D.old_world s i).1
    have hlev : p.lev (D.old s i) = D.depth s := D.old_level s i
    -- velocity and frame budget
    have hvel : ‖p.velocity (D.old s i)‖ +
        (∑ e : Fin 2, ∑ e' : Fin 2,
          (|p.frame (D.old s i) e e'| + |(p.frame (D.old s i))⁻¹ e e'|)) ≤ Nk ^ M := by
      have h1 := hcold.2.1
      have h2 := hcold.2.2.1
      have h3 : 2 * Nk ^ Mp ≤ Nk ^ (Mp + 1) := const_mul_pow_le hNk Mp 1 (by norm_num)
      have h4 : Nk ^ (Mp + 1) ≤ Nk ^ M := by
        apply pow_le_pow_right₀ hN1; unfold budgetExp at hM; omega
      linarith [norm_nonneg (p.center (D.old s i))]
    -- test coefficients
    have hF : (∑ e ∈ ((D.stage Nk L u ν B).F s i).support,
        |((D.stage Nk L u ν B).F s i).coeff e|) ≤ Nk ^ M :=
      (source_test_coeff hp D hNk hframe hBw hBi hr₀pos.le (by linarith) (p.test (D.old s i))
        hcold.2.2.2.2.1 hcold.2.2.2.2.2.1).trans (pow_le_pow_right₀ hN1 hM)
    -- the prior
    have hsub := D.old_assigned_subset hp hin.S_open s hge i
    have hrj : p.r (D.depth s) ≤ L := by
      have h := (hdep s hs0 hs2).2
      have h2 : (sg D.i₀ + u + δ₀) * L ≤ 1 / 2 * L := mul_le_mul_of_nonneg_right hroom hL.le
      linarith
    have herr : |f (p.r (D.depth s)) - f (p.r D.i₀) - d₁ * (u * L * s)| +
        |p.nw (D.depth s) - p.nw D.i₀ - ℓ * (u * L * s)| + 2 * δ₀ * L ≤
        (6 * δ₀ + d₁ * (mesh + 2 * δ₀) + ℓ * mesh) * L := by
      rw [hdepth]
      exact prior_error hp hm hi₀ hu.le hmesh0 hmesh hroom' hL.le hd₁ hℓ.le hprof hs0 hs2
        (by linarith) (by rw [← hdepth]; exact hrj)
    have hexp : (6 * δ₀ + d₁ * (mesh + 2 * δ₀) + ℓ * mesh) * L ≤ u * θ * L / 2 :=
      le_of_le_of_eq (mul_le_mul_of_nonneg_right herr3 hL.le) (by ring)
    have hKE : p.κ ^ 2 * Nk ^ ((6 * δ₀ + d₁ * (mesh + 2 * δ₀) + ℓ * mesh) * L) ≤ D.K :=
      le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hexp)
        (sq_nonneg _)) hpriorK
    have hT' : p.T D.i₀ ≤ p.T (D.depth s) := (D.old_bin_div hp hin.S_open s hge i).1
    obtain ⟨hlo, hhi⟩ := prior_field_at hp hN1 D.parent (D.old s i) D.w₀ D.i₀ (D.depth s)
      hw rfl rfl hlev hT' hcold.2.2.2.2.2.2.1 hsub herr hKE
    obtain ⟨hc, htr⟩ := hin.track s hs1 hs2 i
    exact ⟨hin.label_floor s hs1 hs2 i, hin.det s hs1 hs2 i, hvel, hF, hlo, hhi, hc, htr⟩

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
