-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RootCensusAt, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The census of one active root at the explicit choices (session x1088, for x1082's sample).

`root_census_at` is `Source.RootCensusPackage.root_census_package` with every free census
parameter chosen (`Source.CensusChoices`) and every side condition discharged, for the core
family of ALL levels `i, i+1, …, i+nfam-1` (`depth j = i + j`). What remains as hypotheses:
* the grid (`s l = (l+1)/m`, `4 δ₀ m ≤ κ₁ ≤ 1`), the window (`i + nfam ≤ stop + 1`,
  `stop + 2 ≤ m`), the broad residual's radius `N^(-ub L)` and fraction `> 0`;
* ONE geometric bound `Kgeom ≤ N^(γ L)` and the pre-sample margin
  `γ deepPowerOf + ub + 2δ₀ ≤ κ₁ (s stop - s (i + nfam - 1))` (the family ends early enough);
* the two list lengths fit in the family (`hnnA`, `hnnB`);
* the cap constants at the child level (`hres`, `hKbase`, `hKband`, `censusKAt ≤ Kpk`).
The census charge is bounded by `nfam (4/K² + 1728 K^(3R+32) fraction)` times the root's
reference; the MK4 occupancy is at `(fineMeshA, censusKAt, d₁)`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.CensusChoices
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootCensusPackage
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.FixedSourcePowers

set_option autoImplicit false
set_option maxRecDepth 32768
set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- The census constant at the sample. -/
def censusKAt (K κ N δ₀ L ub : ℝ) (m R : ℕ) : ℝ :=
  censusKOf (geomOf K N δ₀ L) R FixedSourcePowers.jet
    (stripExpOf (geomOf K N δ₀ L) κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf R)
    (gapExpOf (geomOf K N δ₀ L) N δ₀ L m)

/-- The list target `2 Kgeom^(gp+10)/fine`. -/
def listTargetAt (K κ N δ₀ L ub fine : ℝ) (R : ℕ) : ℝ :=
  2 * geomOf K N δ₀ L ^ (censusGp R FixedSourcePowers.jet
    (stripExpOf (geomOf K N δ₀ L) κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf R) + 10) / fine

/-- The child's census shape is below `2 N^(4 δ₀ L)`. -/
theorem child_shape_le {N L κ₁ δ₀ si sl ri rl : ℝ} {Ti Tl : ℕ} (hN : 1 < N) (hL : 0 ≤ L)
    (hκ1 : κ₁ ≤ 1) (hri : |ri - si * L| ≤ δ₀ * L) (hrl : |rl - sl * L| ≤ δ₀ * L) (hsil : si ≤ sl)
    (hTi : N ^ ((κ₁ * si - δ₀) * L) ≤ (2 : ℝ) ^ Ti)
    (hTl : (2 : ℝ) ^ Tl ≤ N ^ ((κ₁ * sl + δ₀) * L)) :
    (O204.Split.δ N rl / O204.Split.δ N ri) / ((2 : ℝ) ^ Ti / (2 : ℝ) ^ Tl) ≤
      2 * N ^ (4 * δ₀ * L) := by
  have hNp : 0 < N := by linarith
  have hδi : 0 < O204.Split.δ N ri := O204.Tangent.δ_pos _ _
  have hratio : O204.Split.δ N rl / O204.Split.δ N ri ≤ 2 * N ^ (ri - rl) := by
    rw [div_le_iff₀ hδi]; exact delta_le_two_rpow_mul hNp
  have hclock : ((2 : ℝ) ^ Ti / (2 : ℝ) ^ Tl)⁻¹ ≤ N ^ ((κ₁ * (sl - si) + 2 * δ₀) * L) := by
    rw [inv_div, div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ Tl ≤ N ^ ((κ₁ * sl + δ₀) * L) := hTl
      _ = N ^ ((κ₁ * (sl - si) + 2 * δ₀) * L) * N ^ ((κ₁ * si - δ₀) * L) := by
          rw [← Real.rpow_add hNp]; ring_nf
      _ ≤ N ^ ((κ₁ * (sl - si) + 2 * δ₀) * L) * (2 : ℝ) ^ Ti := by gcongr
  have h1 := (abs_le.mp hri).2
  have h2 := (abs_le.mp hrl).1
  rw [div_eq_mul_inv]
  calc O204.Split.δ N rl / O204.Split.δ N ri * ((2 : ℝ) ^ Ti / (2 : ℝ) ^ Tl)⁻¹
      ≤ 2 * N ^ (ri - rl) * N ^ ((κ₁ * (sl - si) + 2 * δ₀) * L) :=
        mul_le_mul hratio hclock (by positivity) (by positivity)
    _ = 2 * N ^ (ri - rl + (κ₁ * (sl - si) + 2 * δ₀) * L) := by
        rw [mul_assoc, ← Real.rpow_add hNp]
    _ ≤ 2 * N ^ (4 * δ₀ * L) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.rpow_le_rpow_of_exponent_le hN.le
        have : κ₁ * (sl - si) * L ≤ (sl - si) * L := by
          have := mul_le_mul_of_nonneg_right hκ1 (mul_nonneg (by linarith : (0:ℝ) ≤ sl - si) hL)
          nlinarith
        nlinarith

/-- **The census charge** at the chosen `θrow`, `δref`. -/
theorem census_cost_le {K Kgeom κ fraction : ℝ} {R n : ℕ} (hK : 1 ≤ K) (hκ : 0 ≤ κ)
    (hκK : κ ≤ K) (hKK : K ≤ Kgeom) (hfr : 0 ≤ fraction) :
    (n : ENNReal) * (ENNReal.ofReal (4 * K ^ (3 * R + 28) * κ ^ 2) *
      (ENNReal.ofReal ((Kgeom ^ rowExpOf R)⁻¹ * (K ^ R)⁻¹) +
        27 * (ENNReal.ofReal (16 * fraction) * ENNReal.ofReal (κ ^ 2)))) ≤
      ENNReal.ofReal (n * (4 / K ^ 2 + 1728 * K ^ (3 * R + 32) * fraction)) := by
  have hK0 : 0 < K := by linarith
  have hKg0 : 0 < Kgeom := by linarith
  have h16 : (0 : ℝ) ≤ 16 * fraction := mul_nonneg (by norm_num) hfr
  have e1 : ENNReal.ofReal (16 * fraction) * ENNReal.ofReal (κ ^ 2) =
      ENNReal.ofReal (16 * fraction * κ ^ 2) := (ENNReal.ofReal_mul h16).symm
  have e2 : (27 : ENNReal) * ENNReal.ofReal (16 * fraction * κ ^ 2) =
      ENNReal.ofReal (27 * (16 * fraction * κ ^ 2)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27), ENNReal.ofReal_ofNat]
  have e3 : ENNReal.ofReal ((Kgeom ^ rowExpOf R)⁻¹ * (K ^ R)⁻¹) +
      ENNReal.ofReal (27 * (16 * fraction * κ ^ 2)) =
      ENNReal.ofReal ((Kgeom ^ rowExpOf R)⁻¹ * (K ^ R)⁻¹ + 27 * (16 * fraction * κ ^ 2)) :=
    (ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by norm_num) (mul_nonneg h16 (sq_nonneg κ)))).symm
  have e4 : ENNReal.ofReal (4 * K ^ (3 * R + 28) * κ ^ 2) *
      ENNReal.ofReal ((Kgeom ^ rowExpOf R)⁻¹ * (K ^ R)⁻¹ + 27 * (16 * fraction * κ ^ 2)) =
      ENNReal.ofReal (4 * K ^ (3 * R + 28) * κ ^ 2 *
        ((Kgeom ^ rowExpOf R)⁻¹ * (K ^ R)⁻¹ + 27 * (16 * fraction * κ ^ 2))) :=
    (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hK0.le _))
      (sq_nonneg κ))).symm
  rw [e1, e2, e3, e4, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold rowExpOf
  have hκ2 : κ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hκ hκK 2
  have hpowK : K ^ (2 * R + 32) ≤ Kgeom ^ (2 * R + 32) := pow_le_pow_left₀ hK0.le hKK _
  have hA : 4 * K ^ (3 * R + 28) * κ ^ 2 * ((Kgeom ^ (2 * R + 32))⁻¹ * (K ^ R)⁻¹) ≤ 4 / K ^ 2 := by
    have hB : (Kgeom ^ (2 * R + 32))⁻¹ ≤ (K ^ (2 * R + 32))⁻¹ :=
      inv_anti₀ (by positivity) hpowK
    calc 4 * K ^ (3 * R + 28) * κ ^ 2 * ((Kgeom ^ (2 * R + 32))⁻¹ * (K ^ R)⁻¹)
        ≤ 4 * K ^ (3 * R + 28) * K ^ 2 * ((K ^ (2 * R + 32))⁻¹ * (K ^ R)⁻¹) := by
          gcongr
      _ = 4 / K ^ 2 := by
          field_simp
          ring
  have hC : 4 * K ^ (3 * R + 28) * κ ^ 2 * (27 * (16 * fraction * κ ^ 2)) ≤
      1728 * K ^ (3 * R + 32) * fraction := by
    have hκ4 : κ ^ 2 * κ ^ 2 ≤ K ^ 2 * K ^ 2 := mul_le_mul hκ2 hκ2 (by positivity) (by positivity)
    have e : K ^ (3 * R + 32) = K ^ (3 * R + 28) * (K ^ 2 * K ^ 2) := by ring
    rw [e]
    have h0 : 0 ≤ K ^ (3 * R + 28) * fraction := by positivity
    nlinarith
  calc 4 * K ^ (3 * R + 28) * κ ^ 2 * ((Kgeom ^ (2 * R + 32))⁻¹ * (K ^ R)⁻¹ +
        27 * (16 * fraction * κ ^ 2))
      = 4 * K ^ (3 * R + 28) * κ ^ 2 * ((Kgeom ^ (2 * R + 32))⁻¹ * (K ^ R)⁻¹) +
        4 * K ^ (3 * R + 28) * κ ^ 2 * (27 * (16 * fraction * κ ^ 2)) := by ring
    _ ≤ 4 / K ^ 2 + 1728 * K ^ (3 * R + 32) * fraction := add_le_add hA hC

/-- Depths below the last level are at most `L`. -/
theorem r_le_L_of_grid {L δ₀ rl : ℝ} {m l : ℕ} {s : ℕ → ℝ} (hL : 0 < L) (hm : 0 < m)
    (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ 1) (hl : l + 2 ≤ m)
    (hr : |rl - s l * L| ≤ δ₀ * L) : rl ≤ L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := (abs_le.mp hr).2
  have hsl : s l * m = (l : ℝ) + 1 := by rw [hs l]; field_simp
  have hl2 : (l : ℝ) + 2 ≤ m := by exact_mod_cast hl
  have h1 : rl * m ≤ (s l * L + δ₀ * L) * m :=
    mul_le_mul_of_nonneg_right (by linarith only [h]) hmR.le
  have h2 : (s l * L + δ₀ * L) * m = ((l : ℝ) + 1) * L + (δ₀ * m) * L := by
    rw [← hsl]; ring
  have h3 : ((l : ℝ) + 1) * L + (δ₀ * m) * L ≤ (m : ℝ) * L := by
    have h4 : (δ₀ * m) * L ≤ L := by
      have : δ₀ * m ≤ 1 := by linarith only [hδm]
      calc (δ₀ * m) * L ≤ 1 * L := mul_le_mul_of_nonneg_right this hL.le
        _ = L := one_mul L
    have h5 : ((l : ℝ) + 1) * L ≤ ((m : ℝ) - 1) * L :=
      mul_le_mul_of_nonneg_right (by linarith only [hl2]) hL.le
    linarith only [h4, h5]
  have : rl * m ≤ L * m := by linarith only [h1, h2, h3]
  exact le_of_mul_le_mul_right this hmR

/-- The grid is increasing. -/
theorem s_le_of_le {m : ℕ} {s : ℕ → ℝ} (hm : 0 < m) (hs : ∀ i, s i = ((i : ℝ) + 1) / m)
    {a b : ℕ} (hab : a ≤ b) : s a ≤ s b := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [hs, hs]
  apply div_le_div_of_nonneg_right _ hmR.le
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  linarith only [this]

/-- **The deep margin of the family** (`hdeep` of the census). -/
theorem family_deep {K Kgeom κ N L δ₀ ub γ κ₁ : ℝ} {R J w : ℕ} {m i nfam stop : ℕ}
    {s : ℕ → ℝ} {T : ℕ → ℕ}
    (hN : 1 < N) (hL : 0 < L) (hm : 0 < m) (hs : ∀ i, s i = ((i : ℝ) + 1) / m)
    (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁) (hκ₁0 : 0 < κ₁)
    (hTb : ∀ l, l < m → N ^ ((κ₁ * s l - δ₀) * L) ≤ (2 : ℝ) ^ T l ∧
      (2 : ℝ) ^ T l ≤ N ^ ((κ₁ * s l + δ₀) * L))
    (hκ : 1 ≤ κ) (hκK : κ ≤ K) (hKK : K ≤ Kgeom)
    (hNK : N ^ (2 * δ₀ * L) ≤ Kgeom) (h24 : 24 ≤ Kgeom) (hγ : Kgeom ≤ N ^ (γ * L))
    (hδ : 0 ≤ δ₀) (hub : 0 ≤ ub)
    (hw : Kgeom ^ w ≤ Kgeom * (6 * κ ^ 3 * N ^ (2 * δ₀ * L) / N ^ (-(ub * L))))
    (hstop : i + nfam ≤ stop + 1) (hstopm : stop + 2 ≤ m) {j : ℕ} (hj : j < nfam)
    (hmargin : γ * (deepPowerOf R J : ℝ) + ub + 2 * δ₀ ≤ κ₁ * (s stop - s (i + nfam - 1))) :
    6 * K ^ R * ((1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ) *
      ((2 : ℝ) ^ T (i + j) / (2 : ℝ) ^ T stop)) ≤
      renewalCellMesh (Kgeom ^ (3 * R + 66)) J (layerQOf w R) := by
  apply deep_margin hN hL hκ hκK hKK hNK h24 hγ hδ hub hw _ hmargin
  have hlast : i + nfam - 1 ≤ stop := by omega
  have hTj : T (i + j) ≤ T (i + nfam - 1) :=
    T_le_of_grid hN hL hm hs hδm hκ₁0 hTb (by omega) (by omega)
  have hTl : T (i + nfam - 1) ≤ T stop := T_le_of_grid hN hL hm hs hδm hκ₁0 hTb hlast (by omega)
  have hcr := clock_ratio_le hN hTl (hTb _ (by omega)).2 (hTb stop (by omega)).1
  have hrel : ((2 : ℝ) ^ (T stop - T (i + nfam - 1)))⁻¹ =
      (2 : ℝ) ^ T (i + nfam - 1) / (2 : ℝ) ^ T stop := by
    rw [pow_sub₀ (2 : ℝ) (by norm_num) hTl]; field_simp
  rw [hrel] at hcr
  calc (2 : ℝ) ^ T (i + j) / (2 : ℝ) ^ T stop
      ≤ (2 : ℝ) ^ T (i + nfam - 1) / (2 : ℝ) ^ T stop := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hTj
    _ ≤ _ := hcr

/-- **The last list depth** of a census list of length `listLenOf … (2 G/fine)`. -/
theorem census_list_last {N L δ₀ G fine : ℝ} {m a : ℕ} {s r : ℕ → ℝ} (hN : 1 < N) (hL : 0 < L)
    (hm : 0 < m) (hG : 0 < G) (hfine : 0 < fine) (hs : ∀ i, s i = ((i : ℝ) + 1) / m)
    (hr : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L)
    (hann : a + listLenOf m δ₀ L N (2 * G / fine) < m) :
    G * (O204.Split.δ N (r (a + listLenOf m δ₀ L N (2 * G / fine))) / O204.Split.δ N (r a)) ≤
      fine := by
  have hX : 0 < 2 * G / fine := by positivity
  have h := list_last_le hN hL hm hX hs hr hann (Nat.le_ceil _)
  calc G * (O204.Split.δ N (r (a + listLenOf m δ₀ L N (2 * G / fine))) / O204.Split.δ N (r a))
      ≤ G * (2 / (2 * G / fine)) := mul_le_mul_of_nonneg_left h hG.le
    _ = fine := by field_simp

/-- **Consecutive census steps** at the gap power. -/
theorem census_step {N L δ₀ Kgeom ρ : ℝ} {m gap l : ℕ} {s r : ℕ → ℝ} (hN : 1 < N)
    (hm : 0 < m) (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hr : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L)
    (hgap : 2 * N ^ ((1 / (m : ℝ) + 2 * δ₀) * L) ≤ Kgeom ^ gap) (hρ : 0 < ρ) (hl : l + 1 < m) :
    O204.Split.δ N (r l) / ρ ≤ Kgeom ^ gap * (O204.Split.δ N (r (l + 1)) / ρ) := by
  have h := delta_step_le hN hm hs hr hl
  have h0 := O204.Tangent.δ_pos N (r (l + 1))
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hρ]
  exact h.trans (mul_le_mul_of_nonneg_right hgap h0.le)

/-- **The profile comparison** of two depths. -/
theorem profile_pair {f : ℝ → ℝ} {L δ₀ d₁ r r' : ℝ}
    (hprof : ∀ x, 0 ≤ x → x ≤ L → |f x - f 0 - d₁ * x| ≤ δ₀ * L)
    (hr : 0 ≤ r) (hrL : r ≤ L) (hr' : 0 ≤ r') (hr'L : r' ≤ L) :
    f r' - f r ≤ d₁ * (r' - r) + 2 * δ₀ * L := by
  have h1 := (abs_le.mp (hprof r' hr' hr'L)).2
  have h2 := (abs_le.mp (hprof r hr hrL)).1
  linarith only [h1, h2]

/-- **The child's census shape** is below the census constant. -/
theorem census_shape {N L κ₁ δ₀ si sl ri rl Kgeom Kc : ℝ} {Ti Tl : ℕ} (hN : 1 < N) (hL : 0 ≤ L)
    (hκ1 : κ₁ ≤ 1) (hri : |ri - si * L| ≤ δ₀ * L) (hrl : |rl - sl * L| ≤ δ₀ * L) (hsil : si ≤ sl)
    (hTi : N ^ ((κ₁ * si - δ₀) * L) ≤ (2 : ℝ) ^ Ti)
    (hTl : (2 : ℝ) ^ Tl ≤ N ^ ((κ₁ * sl + δ₀) * L))
    (hNK : N ^ (2 * δ₀ * L) ≤ Kgeom) (h2 : 2 ≤ Kgeom) (hKc : Kgeom ^ 3 ≤ Kc) :
    (O204.Split.δ N rl / O204.Split.δ N ri) / ((2 : ℝ) ^ Ti / (2 : ℝ) ^ Tl) ≤ Kc := by
  have hNp : 0 < N := by linarith
  have h := child_shape_le hN hL hκ1 hri hrl hsil hTi hTl
  have hsq : N ^ (4 * δ₀ * L) = N ^ (2 * δ₀ * L) * N ^ (2 * δ₀ * L) := by
    rw [← Real.rpow_add hNp]; ring_nf
  have h0 : 0 ≤ N ^ (2 * δ₀ * L) := (Real.rpow_pos_of_pos hNp _).le
  have h4 : 2 * N ^ (4 * δ₀ * L) ≤ Kgeom ^ 3 := by
    rw [hsq]
    have := mul_le_mul hNK hNK h0 (by linarith)
    have e : Kgeom ^ 3 = Kgeom * (Kgeom * Kgeom) := by ring
    rw [e]
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **The census of one active root** at the explicit choices. -/
theorem root_census_at
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {m nfam : ℕ} {K : ℝ} {e R : ℕ}
    {H₀ original : Fin (d.W k) → Set ParentSource.Event} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H₀ u τ) (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {i stop : ℕ}
    (C : BroadMultiscaleCoreSource d k p original nfam (fun j => i + (j : ℕ)) K e R)
    (hHE : ∀ w, original w⊆d.E k w) (hHbase : ∀ w, original w⊆Q.base w)
    (hHterminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    {aF AF ub fraction : ℝ} {θF : ENNReal}
    {F : PaletteFamily Q i stop aF AF θF}
    (broad : BroadResidual F (d.N k ^ (-(ub * d.L))) fraction)
    (hHbroad : ∀ w, original w⊆broad.residual w)
    (root : Fin p.C) (hroot : p.lev root = i) (hactive : F.active root)
    -- the grid and the window
    (hm : 0 < m) (hs : ∀ l, s l = ((l : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁)
    (hκ₁0 : 0 < κ₁) (hκ₁ : κ₁ ≤ 1) (hub : 0 ≤ ub) (hfr : 0 < fraction)
    (hstop : i + nfam ≤ stop + 1) (hstopm : stop + 2 ≤ m)
    -- the geometric bound and the pre-sample margin of the family
    {γ : ℝ} (hgeom : geomOf K (d.N k) δ₀ d.L ≤ d.N k ^ (γ * d.L))
    (hmargin : γ * (deepPowerOf R FixedSourcePowers.jet : ℝ) + ub + 2 * δ₀ ≤
      κ₁ * (s stop - s (i + nfam - 1)))
    (source : Set ParentSource.Event) (hsource : MeasurableSet source)
    (hsub : source⊆C.current (p.γ root)∩p.F root)
    {d₁ : ℝ} (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1)
    (hprof : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    -- the root's MK4 census
    (fineMeshA : ℝ) (hFineA : 0 < fineMeshA)
    (hnnA : listLenOf m δ₀ d.L (d.N k) (listTargetAt K p.κ (d.N k) δ₀ d.L ub fineMeshA R) < nfam)
    -- the children's census at level `i + c`
    (c : ℕ) {Kpk εpk : ℝ} (hε : 0 < εpk)
    (hnnB : c + listLenOf m δ₀ d.L (d.N k) (listTargetAt K p.κ (d.N k) δ₀ d.L ub εpk R) < nfam)
    (hres : d.N k ^ (-(d.L - p.r (i + c))) ≤ 4 * εpk)
    (hKbase : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (τ + 2 * δ₀ * d.L + ε) ≤ Kpk)
    (hKband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + ε) ≤ Kpk)
    (hKcK : censusKAt K p.κ (d.N k) δ₀ d.L ub m R ≤ Kpk) :
    ∃ current : Set ParentSource.Event, MeasurableSet current ∧ current ⊆ source ∧
      ((d.ν k (p.γ root)).prod volume) source ≤
        ((d.ν k (p.γ root)).prod volume) current +
          ENNReal.ofReal (nfam * (4 / K ^ 2 + 1728 * K ^ (3 * R + 32) * fraction)) *
          (d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)) ∧
      (∀ b w : ℝ, fineMeshA ≤ b → b ≤ 1 → fineMeshA ≤ w → w ≤ 1 →
        censusKAt K p.κ (d.N k) δ₀ d.L ub m R ^ (100 : ℕ) * b ≤ 1 * w →
        (occupied current (fun z j => unshearedPacketBase p root z j)
          (physicalParentSignal (d.N k) p root (p.R root)) b w).Finite ∧
        ((occupied current (fun z j => unshearedPacketBase p root z j)
          (physicalParentSignal (d.N k) p root (p.R root)) b w).ncard : ℝ) ≤
          censusKAt K p.κ (d.N k) δ₀ d.L ub m R / (b ^ 3 * w ^ d₁)) ∧
      ∀ b : Fin p.C, p.lev b = i + c → p.par^[c] b = root → ∀ Se : Set ParentSource.Event,
        MeasurableSet Se → Se ⊆ current ∩ p.F b →
        CapClauses Kpk εpk d₁ (hRelOf (p.T i) (p.T (i + c)))
          (aRelOf (d.N k) (p.r i) (p.r (i + c)))
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
          (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
          (fun z => O204.Tangent.packetSignal (p.R root) z /
            O204.Split.δ (d.N k) (p.r (p.lev b))) Se := by
  classical
  -- basic facts
  have hN2 : 2 ≤ d.N k := hd.1 k
  have hN1 : 1 < d.N k := by linarith
  have hNp : 0 < d.N k := by linarith
  have hL : 0 < d.L := hd.2.2.2.1
  have hκ1 : 1 ≤ p.κ := hp.1
  have hκK' : p.κ ≤ K := (le_max_left _ _).trans hmax
  have hpath := hp.2.2.2.2.1
  have hrb : ∀ l, l < m → |p.r l - s l * d.L| ≤ δ₀ * d.L := fun l hl => (hpath l hl).1
  have hδ₀ : 0 ≤ δ₀ := by
    have := abs_nonneg (p.r 0 - s 0 * d.L)
    have := hrb 0 hm
    nlinarith
  have hrF0 : 0 < d.N k ^ (-(ub * d.L)) := Real.rpow_pos_of_pos hNp _
  have hrF1 : d.N k ^ (-(ub * d.L)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by nlinarith)
  -- the census choices
  unfold censusKAt listTargetAt at *
  generalize hKgdef : geomOf K (d.N k) δ₀ d.L = Kgeom at *
  have hKgge : K ≤ Kgeom ∧ d.N k ^ (2 * δ₀ * d.L) ≤ Kgeom ∧ 96 * coreRowK₀ ≤ Kgeom := by
    rw [← hKgdef]; exact geomOf_ge
  obtain ⟨hKK, hNK, hconst⟩ := hKgge
  have hKg1 : 1 < Kgeom := by linarith
  have hKg24 : 24 ≤ Kgeom := by linarith
  have hstrip := strip_spec hKg1 hκ1 hN1.le (by positivity : 0 ≤ 2 * δ₀ * d.L) hrF0 hrF1
    (κ := p.κ)
  generalize hwdef : stripExpOf Kgeom p.κ (d.N k) δ₀ d.L (d.N k ^ (-(ub * d.L))) = w at *
  generalize hgapdef : gapExpOf Kgeom (d.N k) δ₀ d.L m = gap at *
  have hgap : 2 * d.N k ^ ((1 / (m : ℝ) + 2 * δ₀) * d.L) ≤ Kgeom ^ gap := by
    rw [← hgapdef]
    refine (logCeil_spec hKg1 ?_).1
    have : 1 ≤ d.N k ^ ((1 / (m : ℝ) + 2 * δ₀) * d.L) := Real.one_le_rpow hN1.le (by positivity)
    linarith
  -- the levels of the window
  have hδm1 : 4 * δ₀ * (m : ℝ) ≤ 1 := hδm.trans hκ₁
  have hlev_lt : ∀ l, l ≤ stop → l < m := fun l hl => by omega
  have hrpos : ∀ l, l ≤ stop → 0 ≤ p.r l := fun l hl => (hpath l (hlev_lt l hl)).2.1.le
  have hrL : ∀ l, l ≤ stop → p.r l ≤ d.L := fun l hl =>
    r_le_L_of_grid hL hm hs hδm1 (by omega) (hrb l (hlev_lt l hl))
  have hTb : ∀ l, l < m → d.N k ^ ((κ₁ * s l - δ₀) * d.L) ≤ (2 : ℝ) ^ p.T l ∧
      (2 : ℝ) ^ p.T l ≤ d.N k ^ ((κ₁ * s l + δ₀) * d.L) :=
    fun l hl => ⟨(hpath l hl).2.2.1, (hpath l hl).2.2.2.1⟩
  -- the census's facts
  have hfam : ∀ j : Fin nfam, i + (j : ℕ) ≤ stop := fun j => by have := j.isLt; omega
  have hdeep : ∀ j : Fin nfam, ∀ fine deep : Fin p.C,
      p.lev fine = (fun j : Fin nfam => i + (j : ℕ)) j → p.lev deep = stop →
      6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤
        renewalCellMesh (Kgeom ^ (3 * R + 66)) FixedSourcePowers.jet (layerQOf w R) := by
    intro j fine deep hfine hdeep'
    unfold PathData.deepBaseRadius
    rw [hfine, hdeep']
    exact family_deep hN1 hL hm hs hδm hκ₁0 hTb hκ1 hκK' hKK hNK hKg24 hgeom hδ₀ hub hstrip.2.1
      hstop hstopm j.isLt hmargin
  -- the census constant
  have hKc := censusK_ge hKg1.le R FixedSourcePowers.jet w (rowExpOf R) gap
  generalize hKcdef : censusKOf Kgeom R FixedSourcePowers.jet w (rowExpOf R) gap = Kcen at *
  have hbudget : Kgeom ^ (3 * R + (((3 * R + 58) + 8) * FixedSourcePowers.jet + w +
      rowExpOf R * ⌈coreRowC₀⌉₊ + 1) + gap + 83) ≤ Kcen := by
    rw [← hKcdef]; exact le_rfl
  -- the two lists
  have hgp : censusGp R FixedSourcePowers.jet w (rowExpOf R) =
      ((3 * R + 58) + 8) * FixedSourcePowers.jet + w + rowExpOf R * ⌈coreRowC₀⌉₊ + 1 := rfl
  have hG : 0 < Kgeom ^ (censusGp R FixedSourcePowers.jet w (rowExpOf R) + 10) := by positivity
  have hδroot : 0 < O204.Split.δ (d.N k) (p.r i) := O204.Tangent.δ_pos _ _
  have hδlb : 0 < O204.Split.δ (d.N k) (p.r (i + c)) := O204.Tangent.δ_pos _ _
  have hlastA := census_list_last hN1 hL hm hG hFineA hs hrb (a := i) (by omega)
  have hlastB := census_list_last hN1 hL hm hG hε hs hrb (a := i + c) (by omega)
  rw [hgp] at hlastA hlastB
  obtain ⟨current, hcm, hcs, hmass, hmk4, hcaps⟩ :=
    root_census_package Q hpure hd hp C hHE hHbase hHterminal hK hmax hpower hκK broad hHbroad
      root hroot hactive (fun j => by rw [hroot]; exact Nat.le_add_right _ _) hfam
      (fun j => hrpos _ (hfam j)) (fun j => hrL _ (hfam j)) (le_refl 5186)
      FixedSourcePowers.jet_bound
      (fun j => by
        rw [hroot]
        exact path_delta_le hp hN1.le hL hm hs hδm hκ₁ (Nat.le_add_right _ _)
          (hlev_lt _ (hfam j)))
      (Kc := Kgeom ^ (3 * R + 66)) (width := (Kgeom ^ w)⁻¹)
      (θrow := (Kgeom ^ rowExpOf R)⁻¹) (qc := layerQOf w R)
      (layer_const (by linarith) hKK (by linarith) R) (by positivity)
      (layer_floor hKg1.le w R) hstrip.2.2 hdeep (by positivity)
      (inv_le_one_of_one_le₀ (one_le_pow₀ hKg1.le)) hfr.le (ENNReal.ofReal (16 * fraction))
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
      ENNReal.ofReal_ne_top
      (by
        rw [← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_div_of_pos (by linarith)]
        have e : 8 * fraction / (16 * fraction) = 1 / 2 := by field_simp; ring
        rw [e]
        simp)
      source hsource hsub (Kgeom := Kgeom) hKK hNK hconst w (rowExpOf R) le_rfl le_rfl hκ₁
      (fun j => hlev_lt _ (hfam j))
      -- MK4
      (listLenOf m δ₀ d.L (d.N k)
        (2 * Kgeom ^ (censusGp R FixedSourcePowers.jet w (rowExpOf R) + 10) / fineMeshA))
      (fun l => i + l) (fun j => ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩)
      (by simp [hroot]) (fun j => rfl) (fun j => by rw [hroot]; omega)
      (fun j => by rw [hroot]; exact s_le_of_le hm hs (by omega))
      d₁ (2 * δ₀ * d.L) fineMeshA Kcen gap hd₀ hd₁.le
      (fun j => by
        rw [hroot]
        exact profile_pair hprof (hrpos _ (by omega)) (hrL _ (by omega)) (hrpos _ (by omega))
          (hrL _ (by omega)))
      hNK hFineA
      (by
        have hδ0 : ParentSource.δ (d.N k) (p.r (p.lev root)) ≠ 0 := (O204.Tangent.δ_pos _ _).ne'
        have h2T : (2 : ℝ) ^ p.T (p.lev root) ≠ 0 := by positivity
        rw [div_self hδ0, div_self h2T, div_one]
        exact hKc.1)
      hbudget (by rw [hroot]; exact hlastA)
      (fun j hj => by
        rw [hroot]
        exact census_step hN1 hm hs hrb hgap hδroot (by omega))
      -- the children
      c (i + c) (by rw [hroot])
      (listLenOf m δ₀ d.L (d.N k)
        (2 * Kgeom ^ (censusGp R FixedSourcePowers.jet w (rowExpOf R) + 10) / εpk))
      (fun l => i + c + l) (fun j => ⟨c + (j : ℕ) + 1, by have := j.isLt; omega⟩)
      rfl (fun j => by show i + (c + (j : ℕ) + 1) = i + c + ((j : ℕ) + 1); omega)
      (fun j => by omega) (fun j => s_le_of_le hm hs (by omega))
      hd₀ hd₁ (2 * δ₀ * d.L) εpk Kcen gap
      (fun j => profile_pair hprof (hrpos _ (by omega)) (hrL _ (by omega)) (hrpos _ (by omega))
          (hrL _ (by omega)))
      hNK hε
      (by
        rw [hroot]
        exact census_shape hN1 hL.le hκ₁ (hrb i (by omega)) (hrb (i + c) (by omega))
          (s_le_of_le hm hs (by omega)) (hTb i (by omega)).1 (hTb (i + c) (by omega)).2 hNK
          (by linarith) hKc.2)
      hbudget hlastB
      (fun j hj => census_step hN1 hm hs hrb hgap hδlb (by omega))
      (by rw [hroot]; exact path_T_le hp hN1 hL hm hs hδm hκ₁0 (by omega) (by omega))
      (by rw [hroot]; exact path_delta_le hp hN1.le hL hm hs hδm hκ₁ (by omega) (by omega))
      (hrpos _ (by omega)) (hrL _ (by omega)) hprof hε hres hKbase hKband hKc.1 hKcK le_rfl
  refine ⟨current, hcm, hcs, ?_, hmk4, ?_⟩
  · refine hmass.trans (add_le_add le_rfl (mul_le_mul' ?_ le_rfl))
    exact census_cost_le (by linarith) (by linarith) hκK' hKK hfr.le
  · intro b hb hpar Se hSe hSeSub
    have h := hcaps b hb hpar Se hSe hSeSub
    rw [hroot] at h
    exact h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
