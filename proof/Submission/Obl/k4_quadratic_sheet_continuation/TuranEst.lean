import Mathlib
import Submission.Lib.K4PolynomialRemez
import Submission.Obl.k4_quadratic_sheet_continuation.TuranAlg

/-!
# Sums of polynomial multiples of products of square roots (estimates)

On the `ρ`-neighbourhood `tube ρ` of the unit segment, the jets at `0` of a function of the class
`radSum` control its values on the segment, with a loss polynomial in `ρ⁻¹`
(`turan_jet_bound`).  The proof is a Turán-type induction on the number of terms: dividing by the
nonvanishing factor of one term and differentiating kills that term; integrating back along the
segment loses only the ratio of that factor between the segment and the disc of radius `ρ / 2`
around `0`, which is polynomial because all radicands have their roots outside the tube.
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Polynomial Metric Set Filter Finset
open scoped Topology ContDiff

noncomputable section

/-- The open `ρ`-neighbourhood of the unit segment `[0,1] ⊆ ℂ`. -/
def tube (ρ : ℝ) : Set ℂ := thickening ρ (segment ℝ (0 : ℂ) 1)

theorem isOpen_tube (ρ : ℝ) : IsOpen (tube ρ) := isOpen_thickening

theorem convex_tube (ρ : ℝ) : Convex ℝ (tube ρ) := (convex_segment _ _).thickening ρ

theorem segment_subset_tube {ρ : ℝ} (hρ : 0 < ρ) : segment ℝ (0 : ℂ) 1 ⊆ tube ρ :=
  self_subset_thickening hρ _

theorem closedBall_subset_tube {ρ : ℝ} (hρ : 0 < ρ) :
    closedBall (0 : ℂ) (ρ / 2) ⊆ tube ρ := by
  intro u hu
  rw [tube, mem_thickening_iff]
  refine ⟨0, left_mem_segment ℝ 0 1, ?_⟩
  rw [mem_closedBall] at hu
  linarith

theorem zero_mem_tube {ρ : ℝ} (hρ : 0 < ρ) : (0 : ℂ) ∈ tube ρ :=
  segment_subset_tube hρ (left_mem_segment ℝ 0 1)

theorem norm_le_one_of_mem_segment {t : ℂ} (ht : t ∈ segment ℝ (0 : ℂ) 1) : ‖t‖ ≤ 1 := by
  rcases ht with ⟨a, b, ha, hb, hab, rfl⟩
  rw [smul_zero, zero_add, Complex.real_smul, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb]
  linarith

theorem le_norm_sub_of_not_mem_tube {ρ : ℝ} {z : ℂ} (hz : z ∉ tube ρ) {y : ℂ}
    (hy : y ∈ segment ℝ (0 : ℂ) 1) : ρ ≤ ‖z - y‖ := by
  by_contra hlt
  push Not at hlt
  exact hz (mem_thickening_iff.mpr ⟨y, hy, by rwa [dist_eq_norm]⟩)

/-- Values of a polynomial without zeros in the tube compare between the segment and the small
disc around `0`. -/
theorem poly_ratio {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ℂ[X])
    (hp : ∀ x ∈ tube ρ, p.eval x ≠ 0) {e : ℕ} (he : p.natDegree ≤ e) {t u : ℂ}
    (ht : t ∈ segment ℝ (0 : ℂ) 1) (hu : u ∈ closedBall (0 : ℂ) (ρ / 2)) :
    ‖p.eval t‖ ≤ (4 * ρ⁻¹) ^ e * ‖p.eval u‖ ∧ ‖p.eval u‖ ≤ (4 * ρ⁻¹) ^ e * ‖p.eval t‖ := by
  have hA : 1 ≤ 4 * ρ⁻¹ := by
    rw [le_mul_inv_iff₀ hρ]
    linarith
  have hA0 : 0 ≤ 4 * ρ⁻¹ := by linarith
  have hu' : ‖u‖ ≤ ρ / 2 := by simpa using hu
  have ht' := norm_le_one_of_mem_segment ht
  have hroot : ∀ z ∈ p.roots, ρ ≤ ‖z - t‖ ∧ ρ ≤ ‖z‖ := by
    intro z hz
    have hz0 : p.eval z = 0 := (mem_roots'.mp hz).2
    have hzt : z ∉ tube ρ := fun hmem => hp z hmem hz0
    refine ⟨le_norm_sub_of_not_mem_tube hzt ht, ?_⟩
    simpa using le_norm_sub_of_not_mem_tube hzt (left_mem_segment ℝ (0 : ℂ) 1)
  have htu : ‖t - u‖ ≤ 3 / 2 := by
    calc ‖t - u‖ ≤ ‖t‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ 3 / 2 := by linarith
  constructor
  · have h := Submission.Lib.K4PolynomialRemez.norm_eval_le_of_root_comparison p t u hA0 (by
      intro z hz
      obtain ⟨h1, h2⟩ := hroot z hz
      have huz : ρ / 2 ≤ ‖u - z‖ := by
        have := norm_sub_norm_le z u
        rw [norm_sub_rev] at this
        linarith
      have htz : ‖t - z‖ ≤ ‖t - u‖ + ‖u - z‖ := by
        calc ‖t - z‖ = ‖(t - u) + (u - z)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have htz' : ‖t - z‖ ≤ 3 / 2 + ‖u - z‖ := by linarith
      have hm := mul_le_mul_of_nonneg_left htz' hρ.le
      have : ρ * ‖t - z‖ ≤ 4 * ‖u - z‖ := by nlinarith
      rw [mul_comm 4 ρ⁻¹, mul_assoc, le_inv_mul_iff₀ hρ]
      linarith)
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA he) (norm_nonneg _))
  · have h := Submission.Lib.K4PolynomialRemez.norm_eval_le_of_root_comparison p u t hA0 (by
      intro z hz
      obtain ⟨h1, h2⟩ := hroot z hz
      have htz : ρ ≤ ‖t - z‖ := by rw [norm_sub_rev]; exact h1
      have huz : ‖u - z‖ ≤ ‖u - t‖ + ‖t - z‖ := by
        calc ‖u - z‖ = ‖(u - t) + (t - z)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have hut : ‖u - t‖ ≤ 3 / 2 := by rw [norm_sub_rev]; exact htu
      have huz' : ‖u - z‖ ≤ 3 / 2 + ‖t - z‖ := by linarith
      have hm := mul_le_mul_of_nonneg_left huz' hρ.le
      have : ρ * ‖u - z‖ ≤ 4 * ‖t - z‖ := by nlinarith
      rw [mul_comm 4 ρ⁻¹, mul_assoc, le_inv_mul_iff₀ hρ]
      linarith)
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA he) (norm_nonneg _))

namespace RadOn

variable {m : ℕ} {Δ : Fin m → ℂ[X]} {s : Fin m → ℂ → ℂ} {ρ : ℝ}

theorem s_ratio (h : RadOn Δ s (tube ρ)) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (i : Fin m) {t u : ℂ}
    (ht : t ∈ segment ℝ (0 : ℂ) 1) (hu : u ∈ closedBall (0 : ℂ) (ρ / 2)) :
    ‖s i t‖ ≤ 4 * ρ⁻¹ * ‖s i u‖ := by
  have hp : ∀ x ∈ tube ρ, (Δ i).eval x ≠ 0 := fun x hx => h.delta_ne i hx
  have hr := (poly_ratio hρ hρ1 (Δ i) hp (h.deg i) ht hu).1
  have htt := segment_subset_tube hρ ht
  have huu := closedBall_subset_tube hρ hu
  rw [← h.sq i t htt, ← h.sq i u huu, norm_pow, norm_pow] at hr
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow]
  exact hr

theorem nu_ratio (h : RadOn Δ s (tube ρ)) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (T : Finset (Fin m))
    (K : ℕ) {t u : ℂ} (ht : t ∈ segment ℝ (0 : ℂ) 1) (hu : u ∈ closedBall (0 : ℂ) (ρ / 2)) :
    ‖radProd s T t / (radDen Δ).eval t ^ K‖ ≤
      (4 * ρ⁻¹) ^ (m + 2 * m * K) * ‖radProd s T u / (radDen Δ).eval u ^ K‖ := by
  have hA : 1 ≤ 4 * ρ⁻¹ := by
    rw [le_mul_inv_iff₀ hρ]
    linarith
  have htt := segment_subset_tube hρ ht
  have huu := closedBall_subset_tube hρ hu
  have he : ‖radProd s T t‖ ≤ (4 * ρ⁻¹) ^ m * ‖radProd s T u‖ := by
    rw [radProd, radProd, norm_prod, norm_prod]
    calc ∏ i ∈ T, ‖s i t‖ ≤ ∏ i ∈ T, (4 * ρ⁻¹ * ‖s i u‖) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg (s i t)) (fun i _ => h.s_ratio hρ hρ1 i ht hu)
      _ = (4 * ρ⁻¹) ^ T.card * ∏ i ∈ T, ‖s i u‖ := by rw [prod_mul_distrib, prod_const]
      _ ≤ (4 * ρ⁻¹) ^ m * ∏ i ∈ T, ‖s i u‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA (by simpa using card_le_univ T))
            (prod_nonneg (fun i _ => norm_nonneg _))
  have hE : ‖(radDen Δ).eval u‖ ≤ (4 * ρ⁻¹) ^ (2 * m) * ‖(radDen Δ).eval t‖ :=
    (poly_ratio hρ hρ1 (radDen Δ) (fun x hx => h.den_ne hx) (natDegree_radDen_le h.deg)
      ht hu).2
  have hEt : 0 < ‖(radDen Δ).eval t‖ := norm_pos_iff.mpr (h.den_ne htt)
  have hEu : 0 < ‖(radDen Δ).eval u‖ := norm_pos_iff.mpr (h.den_ne huu)
  have hEK : ‖(radDen Δ).eval u‖ ^ K ≤ (4 * ρ⁻¹) ^ (2 * m * K) * ‖(radDen Δ).eval t‖ ^ K := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hE K
  rw [norm_div, norm_div, norm_pow, norm_pow, div_le_iff₀ (pow_pos hEt K)]
  calc ‖radProd s T t‖ ≤ (4 * ρ⁻¹) ^ m * ‖radProd s T u‖ := he
    _ = (4 * ρ⁻¹) ^ m * (‖radProd s T u‖ / ‖(radDen Δ).eval u‖ ^ K) *
          ‖(radDen Δ).eval u‖ ^ K := by
        field_simp
    _ ≤ (4 * ρ⁻¹) ^ m * (‖radProd s T u‖ / ‖(radDen Δ).eval u‖ ^ K) *
          ((4 * ρ⁻¹) ^ (2 * m * K) * ‖(radDen Δ).eval t‖ ^ K) := by
        gcongr
    _ = (4 * ρ⁻¹) ^ (m + 2 * m * K) * (‖radProd s T u‖ / ‖(radDen Δ).eval u‖ ^ K) *
          ‖(radDen Δ).eval t‖ ^ K := by
        rw [pow_add]
        ring

end RadOn

/-- Leibniz rule and Cauchy estimates: jets at `0` of a product with a function bounded on the
disc of radius `ρ / 2`. -/
theorem jet_mul_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {G w : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (tube ρ)) (hw : DifferentiableOn ℂ w (tube ρ)) {M V : ℝ}
    (hM : ∀ u ∈ closedBall (0 : ℂ) (ρ / 2), ‖w u‖ ≤ M) (q : ℕ)
    (hV : ∀ j ≤ q, ‖iteratedDeriv j G 0‖ ≤ V) :
    ∀ j ≤ q, ‖iteratedDeriv j (fun x => G x * w x) 0‖ ≤
      2 ^ q * q.factorial * (2 * ρ⁻¹) ^ q * M * V := by
  intro j hj
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0 (Nat.zero_le _))
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self hρ2.le))
  have hB : 1 ≤ 2 * ρ⁻¹ := by
    rw [le_mul_inv_iff₀ hρ]
    linarith
  have h0 : (0 : ℂ) ∈ tube ρ := zero_mem_tube hρ
  have hcauchy : ∀ i ≤ q, ‖iteratedDeriv i w 0‖ ≤ q.factorial * (2 * ρ⁻¹) ^ q * M := by
    intro i hi
    have hdc : DiffContOnCl ℂ w (ball (0 : ℂ) (ρ / 2)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hρ2.ne']
      exact hw.mono (closedBall_subset_tube hρ)
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hρ2 hdc
      (fun z hz => hM z (sphere_subset_closedBall hz))
    calc ‖iteratedDeriv i w 0‖ ≤ i.factorial * M / (ρ / 2) ^ i := hc
      _ = i.factorial * (2 * ρ⁻¹) ^ i * M := by
          rw [div_eq_mul_inv, ← inv_pow, inv_div, div_eq_mul_inv]
          ring
      _ ≤ q.factorial * (2 * ρ⁻¹) ^ q * M := by
          gcongr
  have hleib : ‖iteratedDeriv j (fun x => G x * w x) 0‖ ≤
      ∑ i ∈ range (j + 1), (j.choose i : ℝ) * ‖iteratedDeriv i G 0‖ *
        ‖iteratedDeriv (j - i) w 0‖ := by
    have := norm_iteratedFDerivWithin_mul_le (hG.contDiffOn (n := (j : ℕ∞ω)) (isOpen_tube ρ))
      (hw.contDiffOn (n := (j : ℕ∞ω)) (isOpen_tube ρ)) (isOpen_tube ρ).uniqueDiffOn h0
      (n := j) le_rfl
    simp only [iteratedFDerivWithin_of_isOpen _ (isOpen_tube ρ) h0,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] at this
    exact this
  calc ‖iteratedDeriv j (fun x => G x * w x) 0‖
      ≤ ∑ i ∈ range (j + 1), (j.choose i : ℝ) * ‖iteratedDeriv i G 0‖ *
        ‖iteratedDeriv (j - i) w 0‖ := hleib
    _ ≤ ∑ i ∈ range (j + 1), (j.choose i : ℝ) * V * (q.factorial * (2 * ρ⁻¹) ^ q * M) := by
        apply sum_le_sum
        intro i hi
        have hi' : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
        gcongr
        · exact hV i (hi'.trans hj)
        · exact hcauchy (j - i) (by omega)
    _ = 2 ^ j * (V * (q.factorial * (2 * ρ⁻¹) ^ q * M)) := by
        rw [← sum_mul, ← sum_mul]
        have hc : (∑ i ∈ range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hc]
        ring
    _ ≤ 2 ^ q * (V * (q.factorial * (2 * ρ⁻¹) ^ q * M)) := by
        gcongr
        norm_num
    _ = 2 ^ q * q.factorial * (2 * ρ⁻¹) ^ q * M * V := by ring

/-- Iterated mean value inequality along the unit segment. -/
theorem norm_le_of_iteratedDeriv_bound {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f (tube ρ) → ∀ {B W : ℝ},
      (∀ x ∈ segment ℝ (0 : ℂ) 1, ‖iteratedDeriv k f x‖ ≤ B) →
      (∀ j < k, ‖iteratedDeriv j f 0‖ ≤ W) →
      ∀ x ∈ segment ℝ (0 : ℂ) 1, ‖f x‖ ≤ k * W + B := by
  induction k with
  | zero =>
    intro f hf B W hB hW x hx
    simpa using hB x hx
  | succ k ih =>
    intro f hf B W hB hW x hx
    have hf' : DifferentiableOn ℂ (deriv f) (tube ρ) := hf.deriv (isOpen_tube ρ)
    have hd := ih hf' (B := B) (W := W)
      (fun y hy => by rw [← iteratedDeriv_succ']; exact hB y hy)
      (fun j hj => by rw [← iteratedDeriv_succ']; exact hW (j + 1) (by omega))
    have hdiff : ∀ y ∈ segment ℝ (0 : ℂ) 1, DifferentiableAt ℂ f y := fun y hy =>
      hf.differentiableAt ((isOpen_tube ρ).mem_nhds (segment_subset_tube hρ hy))
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hd (convex_segment 0 1)
      (left_mem_segment ℝ 0 1) hx
    have hx1 := norm_le_one_of_mem_segment hx
    have h0 : ‖f 0‖ ≤ W := by simpa using hW 0 (by omega)
    have hC : 0 ≤ k * W + B := (norm_nonneg _).trans (hd 0 (left_mem_segment ℝ 0 1))
    calc ‖f x‖ = ‖f 0 + (f x - f 0)‖ := by ring_nf
      _ ≤ ‖f 0‖ + ‖f x - f 0‖ := norm_add_le _ _
      _ ≤ W + (k * W + B) * ‖x - 0‖ := by gcongr
      _ ≤ W + (k * W + B) * 1 := by
          gcongr
          simpa using hx1
      _ = ((k + 1 : ℕ) : ℝ) * W + B := by push_cast; ring

/-- **Turán-type jet bound.**  For a function of the class `radSum` on the tube, jets at `0` up to
a fixed order control its values on the unit segment, with a loss `C ρ⁻ᵏ`. -/
theorem turan_jet_bound (m : ℕ) (n : ℕ) : ∀ K d : ℕ, ∃ q k : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ (Δ : Fin m → ℂ[X]) (s : Fin m → ℂ → ℂ), RadOn Δ s (tube ρ) →
    ∀ {ι : Type} (L : Finset ι) (τ : ι → Finset (Fin m)) (N : ι → ℂ[X]),
    L.card ≤ n → (∀ ℓ ∈ L, (N ℓ).natDegree ≤ d) → ∀ G : ℂ → ℂ,
    (∀ t ∈ tube ρ, G t = radSum Δ s L τ 0 N K t) → ∀ V : ℝ,
    (∀ j ≤ q, ‖iteratedDeriv j G 0‖ ≤ V) →
    ∀ t ∈ segment ℝ (0 : ℂ) 1, ‖G t‖ ≤ C * ρ⁻¹ ^ k * V := by
  induction n with
  | zero =>
    intro K d
    refine ⟨0, 0, 1, one_pos, ?_⟩
    intro ρ hρ hρ1 Δ s hRad ι L τ N hcard hdeg G hG V hV t ht
    have hL : L = ∅ := card_eq_zero.mp (Nat.le_zero.mp hcard)
    have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0 le_rfl)
    have hGt : G t = 0 := by
      rw [hG t (segment_subset_tube hρ ht), radSum, hL]
      simp
    rw [hGt, norm_zero]
    simpa using hV0
  | succ n ih =>
    intro K d
    obtain ⟨q₁, k₁, C₁, hC₁, hIH⟩ := ih (1 + (d + 1)) (d + 4 * m + (d + 1) * (2 * m))
    refine ⟨q₁ + d + 1, k₁ + (q₁ + d + 1) + (m + 2 * m * K),
      ((d : ℝ) + 1 + C₁) * 2 ^ (q₁ + d + 1) * (q₁ + d + 1).factorial * 2 ^ (q₁ + d + 1) *
        4 ^ (m + 2 * m * K), by positivity, ?_⟩
    intro ρ hρ hρ1 Δ s hRad ι L τ N hcard hdeg G hG V hV t ht
    classical
    set q := q₁ + d + 1 with hq
    set r := m + 2 * m * K with hr
    have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0 (Nat.zero_le _))
    have hΩ := isOpen_tube ρ
    have htt := segment_subset_tube hρ ht
    have hρinv : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ |>.mpr hρ1
    rcases L.eq_empty_or_nonempty with hL | ⟨ℓ₀, hℓ₀⟩
    · have hGt : G t = 0 := by
        rw [hG t htt, radSum, hL]
        simp
      rw [hGt, norm_zero]
      positivity
    -- the factor of the term `ℓ₀` and its inverse
    let w : ℂ → ℂ := fun x => (radDen Δ).eval x ^ K / radProd s (τ ℓ₀) x
    let ν : ℂ → ℂ := fun x => radProd s (τ ℓ₀) x / (radDen Δ).eval x ^ K
    let Ψ : ℂ → ℂ := fun x => G x * w x
    let τ' : ι → Finset (Fin m) := fun ℓ => symmDiff (τ ℓ) (τ ℓ₀)
    let M : ι → ℂ[X] := fun ℓ => N ℓ * (∏ i ∈ τ ℓ ∩ τ ℓ₀, Δ i) * ∏ i ∈ (τ ℓ₀)ᶜ, Δ i
    have hΨ : ∀ x ∈ tube ρ, Ψ x = radSum Δ s (L.erase ℓ₀) τ' (N ℓ₀) M 1 x := by
      intro x hx
      change G x * ((radDen Δ).eval x ^ K / radProd s (τ ℓ₀) x) = _
      rw [hG x hx, ← mul_div_assoc]
      exact hRad.radSum_div_eq L τ N K hℓ₀ hx
    let G₁ : ℂ → ℂ := iteratedDeriv (d + 1) Ψ
    have hG₁ : ∀ x ∈ tube ρ,
        G₁ x = radSum Δ s (L.erase ℓ₀) τ' 0 (radIter Δ τ' 1 (d + 1) M) (1 + (d + 1)) x := by
      intro x hx
      change iteratedDeriv (d + 1) Ψ x = _
      rw [hRad.iteratedDeriv_eq_radSum hΩ (L.erase ℓ₀) τ' (N ℓ₀) M 1 hΨ (d + 1) x hx,
        iterate_derivative_eq_zero (Nat.lt_succ_of_le (hdeg ℓ₀ hℓ₀))]
    have hcard' : (L.erase ℓ₀).card ≤ n := by
      rw [card_erase_of_mem hℓ₀]
      omega
    have hdeg' : ∀ ℓ ∈ L.erase ℓ₀,
        (radIter Δ τ' 1 (d + 1) M ℓ).natDegree ≤ d + 4 * m + (d + 1) * (2 * m) := by
      intro ℓ hℓ
      have h1 := natDegree_radIter_le hRad.deg τ' 1 M ℓ (d + 1)
      have h2 := natDegree_kill_le hRad.deg (N ℓ) (τ ℓ ∩ τ ℓ₀) (τ ℓ₀)ᶜ
      have h3 := hdeg ℓ (mem_of_mem_erase hℓ)
      have h4 : (M ℓ).natDegree ≤ d + 4 * m := by
        change (N ℓ * (∏ i ∈ τ ℓ ∩ τ ℓ₀, Δ i) * ∏ i ∈ (τ ℓ₀)ᶜ, Δ i).natDegree ≤ _
        omega
      omega
    -- differentiability on the tube
    have hGd : DifferentiableOn ℂ G (tube ρ) := by
      intro x hx
      have hev : G =ᶠ[𝓝 x] radSum Δ s L τ 0 N K := by
        filter_upwards [hΩ.mem_nhds hx] with y hy
        exact hG y hy
      exact ((hRad.hasDerivAt_radSum hΩ L τ 0 N K hx).differentiableAt.congr_of_eventuallyEq
        hev).differentiableWithinAt
    have hwd : DifferentiableOn ℂ w (tube ρ) := by
      intro x hx
      have hE : DifferentiableAt ℂ (fun y => (radDen Δ).eval y ^ K) x :=
        ((Polynomial.differentiable _) x).pow K
      have he : DifferentiableAt ℂ (radProd s (τ ℓ₀)) x :=
        (hRad.hasDerivAt_radProd hΩ (τ ℓ₀) hx).differentiableAt
      exact (hE.div he (hRad.radProd_ne (τ ℓ₀) hx)).differentiableWithinAt
    -- the ratio bound fixes the size of `w` near `0` relative to `ν t`
    have hνt : ν t ≠ 0 := div_ne_zero (hRad.radProd_ne (τ ℓ₀) htt) (pow_ne_zero K (hRad.den_ne htt))
    have hνt' : 0 < ‖ν t‖ := norm_pos_iff.mpr hνt
    set R := (4 * ρ⁻¹) ^ r with hR
    have hwM : ∀ u ∈ closedBall (0 : ℂ) (ρ / 2), ‖w u‖ ≤ R / ‖ν t‖ := by
      intro u hu
      have huu := closedBall_subset_tube hρ hu
      have hrat := hRad.nu_ratio hρ hρ1 (τ ℓ₀) K ht hu
      have hνu : ν u ≠ 0 :=
        div_ne_zero (hRad.radProd_ne (τ ℓ₀) huu) (pow_ne_zero K (hRad.den_ne huu))
      have hwu : w u = (ν u)⁻¹ := by
        change (radDen Δ).eval u ^ K / radProd s (τ ℓ₀) u =
          (radProd s (τ ℓ₀) u / (radDen Δ).eval u ^ K)⁻¹
        rw [inv_div]
      rw [hwu, norm_inv, le_div_iff₀ hνt']
      calc ‖ν u‖⁻¹ * ‖ν t‖ ≤ ‖ν u‖⁻¹ * (R * ‖ν u‖) := by
            gcongr
        _ = R := by
            field_simp [norm_pos_iff.mpr hνu]
    set B := 2 ^ q * q.factorial * (2 * ρ⁻¹) ^ q * (R / ‖ν t‖) * V with hB
    have hΨjet := jet_mul_le hρ hρ1 hGd hwd hwM q hV
    have hG₁jet : ∀ j ≤ q₁, ‖iteratedDeriv j G₁ 0‖ ≤ B := by
      intro j hj
      have hit : iteratedDeriv j G₁ = iteratedDeriv (j + (d + 1)) Ψ := by
        change iteratedDeriv j (iteratedDeriv (d + 1) Ψ) = _
        rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate]
        exact (Function.iterate_add_apply deriv j (d + 1) Ψ).symm
      rw [hit]
      exact hΨjet _ (by omega)
    have hG₁bd := hIH ρ hρ hρ1 Δ s hRad (L.erase ℓ₀) τ' (radIter Δ τ' 1 (d + 1) M) hcard'
      hdeg' G₁ hG₁ B hG₁jet
    have hΨd : DifferentiableOn ℂ Ψ (tube ρ) := hGd.mul hwd
    have hΨt := norm_le_of_iteratedDeriv_bound hρ (d + 1) hΨd (B := C₁ * ρ⁻¹ ^ k₁ * B)
      (W := B) hG₁bd (fun j hj => hΨjet j (by omega)) t ht
    have hGt : G t = Ψ t * ν t := by
      change G t = G t * ((radDen Δ).eval t ^ K / radProd s (τ ℓ₀) t) *
        (radProd s (τ ℓ₀) t / (radDen Δ).eval t ^ K)
      have h1 := hRad.radProd_ne (τ ℓ₀) htt
      have h2 := pow_ne_zero K (hRad.den_ne htt)
      field_simp
    have hB0 : 0 ≤ B := by positivity
    have hk1 : 1 ≤ ρ⁻¹ ^ k₁ := one_le_pow₀ hρinv
    calc ‖G t‖ = ‖Ψ t‖ * ‖ν t‖ := by rw [hGt, norm_mul]
      _ ≤ (((d + 1 : ℕ) : ℝ) * B + C₁ * ρ⁻¹ ^ k₁ * B) * ‖ν t‖ := by gcongr
      _ = (((d + 1 : ℕ) : ℝ) + C₁ * ρ⁻¹ ^ k₁) * 2 ^ q * q.factorial * (2 * ρ⁻¹) ^ q * R * V := by
          rw [hB]
          field_simp
      _ ≤ (((d : ℝ) + 1) * ρ⁻¹ ^ k₁ + C₁ * ρ⁻¹ ^ k₁) * 2 ^ q * q.factorial * (2 * ρ⁻¹) ^ q *
            R * V := by
          gcongr
          push_cast
          nlinarith
      _ = ((d : ℝ) + 1 + C₁) * 2 ^ q * q.factorial * 2 ^ q * 4 ^ r *
            ρ⁻¹ ^ (k₁ + q + r) * V := by
          rw [hR, mul_pow, mul_pow, pow_add, pow_add]
          ring

end

end Submission.Obl.k4_quadratic_sheet_continuation
