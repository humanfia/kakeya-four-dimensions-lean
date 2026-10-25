-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.IndexedInsertion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.CoverScaleSelection

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (convexExpansionLoss)

theorem insert_indexed_covers {J k q : ℕ} {d θ ζ ε C ω g gap g' gap' : ℝ}
    (H : HierarchyCertificate d θ g gap J) (hk : k < J)
    {Y : Fin (H.tree.layer (k + 1)).card → Set Space}
    (D : IndexedCovers H.tree k d θ ζ C ω (d ^ (θ + 2 * ζ)) (d ^ (-ζ)) Y)
    (hd : 0 < d) (hd1 : d < 1) (hθ : 0 ≤ θ) (hθζ : θ ≤ ζ) (hζ : 0 < ζ)
    (hε : 100 * ζ ≤ ε) (hgg : g' ≤ g) (hgap : gap' ≤ gap) (hgap' : 0 ≤ gap')
    (hω : 0 ≤ ω / 100) (hω1 : ω / 100 ≤ 1) (hC : 1 ≤ C)
    (hlarge : (H.tree.layer (k + 1)).radius / (H.tree.layer k).radius ≤ d ^ g')
    (hq : 0 < q) (hn : ((H.tree.layer J).card : ℝ) < (d ^ (-ζ)) ^ q)
    (hspan : d ^ (-2 : ℝ) < (d ^ (-ζ)) ^ q)
    (hqsmall : (q : ℝ) ^ (J + 2) * d ^ ζ ≤ 1) (hsmall : (10 ^ 15 : ℝ) * d ^ ζ ≤ 1)
    (hCsmall : C ^ 2 * d ≤ 1)
    (hmesh : 1024 * C * d ^ g' ≤ d ^ ((1 - ω / 100) * g))
    (htop : 65536 * C * d ^ (ω / 100 * g') ≤ d ^ gap') :
    ∃ r : ℝ, 0 < r ∧ d ^ g' * (H.tree.layer k).radius ≤ r ∧
      d ^ g' * r ≤ (H.tree.layer (k + 1)).radius ∧
    ∃ H' : HierarchyCertificate d ε g gap' (J + 1),
      (∀ j, (H'.tree.layer j).radius =
        if j ≤ k then (H.tree.layer j).radius else if j = k + 1 then r else (H.tree.layer (j - 1)).radius) ∧
      (H'.tree.layer (J + 1)).card ≤ (H.tree.layer J).card ∧
      (⋃ i, H'.shading i) ⊆ (⋃ i, H.shading i) ∧
      ENNReal.ofReal (d ^ ε) * (∑ i, volume (H.shading i)) ≤ ∑ i, volume (H'.shading i) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqsmall' : (q : ℝ) * d ^ ζ ≤ 1 := by
    have hh : (q : ℝ) ≤ q ^ (J + 2) := by
      simpa only [pow_one] using pow_le_pow_right₀ hq1 (show 1 ≤ J + 2 by omega)
    exact (mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hd.le _)).trans hqsmall
  obtain ⟨P, hP, r, hr, hparents, hr64, hsr, hlo₁, hlo₂, hhi₁, hhi₂, hρ⟩ :=
    D.select_scales H.control hk hd hd1 hζ hω hω1 hC hgap' hlarge hq hspan hqsmall' hCsmall hmesh htop
  let G := Classical.choice (D.exists_grouping P)
  let K : ℝ := (10 ^ 15 : ℝ) * d ^ (-(3 * ζ))
  let L : ℝ := 2000000 * d ^ (-(2 * θ + 3 * ζ))
  have hK : K ≤ d ^ (-ε) := inverse_power_error_bound hd
    (power_coefficient_bound hd hd1.le (by norm_num) le_rfl (by linarith : ζ ≤ ε - 3 * ζ) hsmall)
  have hslab : L * d ^ (-(5 * θ + 6 * ζ)) ≤ d ^ (-ε) := by
    have he : L * d ^ (-(5 * θ + 6 * ζ)) = 2000000 * d ^ (-(7 * θ + 9 * ζ)) := by
      dsimp [L]
      rw [mul_assoc, ← Real.rpow_add hd]
      congr 2
      ring
    rw [he]
    exact inverse_power_error_bound hd
      (power_coefficient_bound hd hd1.le (by norm_num) (by norm_num)
        (by linarith : ζ ≤ ε - (7 * θ + 9 * ζ)) hsmall)
  have hmass : 56 * d ^ ε ≤ d ^ (3 * θ + 4 * ζ) := by
    have hh := density_power_bound hd (by norm_num : (0 : ℝ) < 56)
      (power_coefficient_bound hd hd1.le (by norm_num) (by norm_num)
        (by linarith : ζ ≤ ε - (3 * θ + 4 * ζ)) hsmall)
    nlinarith only [hh]
  have hratio (t) (ht : t ∈ P) : r / (D.cover t).radius ≤ 1024 * d ^ (-ζ) :=
    (div_le_iff₀ (D.cover t).radius_pos).mpr (hρ t ht).2.2.2
  have hratio0 (t) : 0 ≤ r / (D.cover t).radius := (div_pos hr (D.cover t).radius_pos).le
  have hsquare (t) (ht : t ∈ P) : (r / (D.cover t).radius) ^ 2 * d ^ (-ζ) ≤
      1024 ^ 2 * d ^ (-(3 * ζ)) := by
    calc
      _ ≤ (1024 * d ^ (-ζ)) ^ 2 * d ^ (-ζ) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (hratio0 t) (hratio t ht) 2) (Real.rpow_nonneg hd.le _)
      _ = _ := by
        rw [mul_pow, pow_two (d ^ (-ζ)), mul_assoc, ← Real.rpow_add hd, ← Real.rpow_add hd]
        congr 2
        ring
  have hcount (t) (ht : t ∈ P) :
      (r / (D.cover t).radius) ^ 2 * d ^ (-ζ) * convexExpansionLoss 6 ≤ K := by
    calc
      _ ≤ (1024 ^ 2 * d ^ (-(3 * ζ))) * convexExpansionLoss 6 :=
        mul_le_mul_of_nonneg_right (hsquare t ht) (by norm_num [convexExpansionLoss])
      _ ≤ K := by
        dsimp [K]
        have hh : (1024 : ℝ) ^ 2 * convexExpansionLoss 6 ≤ 10 ^ 15 := by norm_num [convexExpansionLoss]
        nlinarith only [mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hd.le (-(3 * ζ)))]
  have hfine (t) (ht : t ∈ P) : 262144 * (r / (D.cover t).radius) ^ 2 * d ^ (-ζ) ≤ K := by
    calc
      _ = 262144 * ((r / (D.cover t).radius) ^ 2 * d ^ (-ζ)) := by ring
      _ ≤ 262144 * (1024 ^ 2 * d ^ (-(3 * ζ))) := mul_le_mul_of_nonneg_left (hsquare t ht) (by norm_num)
      _ ≤ K := by
        dsimp [K]
        have hh : (262144 : ℝ) * 1024 ^ 2 ≤ 10 ^ 15 := by norm_num
        nlinarith only [mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hd.le (-(3 * ζ)))]
  have hcoarse : 2000000 * (d ^ (-ζ) * d ^ (-θ) / d ^ (θ + 2 * ζ)) ≤ L := by
    dsimp [L]
    apply le_of_eq
    rw [← Real.rpow_add hd, ← Real.rpow_sub hd]
    congr 2
    ring
  have hr1 : r ≤ 1 := by have hh := (H.control.radius_bounds hk.le).2; linarith
  have Q := G.geometry H.alignment hk hd.le (H.control.positive k hk.le)
    (H.control.positive (k + 1) (by omega)) (H.control.radius_bounds (by omega : k + 1 ≤ J)).1
    (Real.rpow_pos_of_pos hd _) (Real.rpow_nonneg hd.le _) hr1
    (fun t ht => (hρ t ht).1) (fun t ht => (hρ t ht).2.1) (fun t ht => (hρ t ht).2.2.1)
    hcount hcoarse hfine
  have hg : d ^ g ≤ d ^ g' := Real.rpow_le_rpow_of_exponent_ge hd hd1.le hgg
  obtain ⟨H', hrad, hcard, hunion, hret⟩ := insert_grouped_certificate H hk G.selection Q
    hd hd1 hθ hζ (by linarith) hgap q hq hn hqsmall
    (by simpa only [G.parents] using hparents) hr hr64 hsr
    ((mul_le_mul_of_nonneg_right hg (H.control.positive k hk.le).le).trans hlo₁)
    ((mul_le_mul_of_nonneg_right hg hr.le).trans hlo₂) hhi₁ hhi₂ hK hK
    (by dsimp [L]; positivity) hslab hmass
  exact ⟨r, hr, hlo₁, hlo₂, H', hrad, hcard, hunion, hret⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
