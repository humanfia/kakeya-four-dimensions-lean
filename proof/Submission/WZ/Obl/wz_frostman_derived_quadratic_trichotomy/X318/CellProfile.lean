-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CellProfile.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ProfileBridge
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Frostman
-- Copied from session x0338/x0318 (o070 branch, commit 2c4a35f, file CellProfile.lean), namespace renamed.

/-!
# The cell-count profile of a regularized family

Levels `k = 0, …, top` (fine to coarse) with radii `ρ k` and dyadic population classes `a k`
(every level-`k` cell holds between `2^(a k)` and `2^(a k + 1)` tubes).  The level density is
`dens k = 2^(a k) / ρ_k²` and the profile, read from the top level down,

  `G j = log_{1/δ} (dens top / dens (top - j))`,

is, up to an additive constant, `log_{1/δ} (#cells · ρ²)` at level `top - j`.  This file proves the
three hypotheses of the scale choice (x0305's `profile_dichotomy_step`, x0318's
`profile_scale_choice`):

* `cellProfile_zero`: `G 0 = 0`;
* `cellProfile_lower_of_family`: `G j ≥ -log_{1/δ}(768 · 82⁶ · K / ρ_top⁴)` for a `K`-Frostman family
  (`K = δ^(-ζ)` and `ρ_top ≥ δ^ε` make this `≥ -(ζ + 4ε) - o(1)`);
* `cellProfile_step_of_family`: `G (j+1) - G j ≤ log_{1/δ}(2 (4L+2)⁶ / L²)` when consecutive radii
  have ratio `L` (so at most `4 log_{1/δ} L + o(1)`),

and translates the outputs of the scale choice back to densities (`levelDens_le_of_profile_le`,
`levelDens_le_of_profile_sub_le`), which are the population facts used by x0305's
`SB_of_KTcase` (fullness) and by `roundBox_of_levels` (Katz–Tao below `ρ`).
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric MeasureTheory

/-- Density of level `k`: the dyadic population class over the squared radius. -/
noncomputable def levelDens (a : ℕ → ℕ) (ρ : ℕ → ℝ) (k : ℕ) : ℝ := (2 : ℝ) ^ a k / ρ k ^ 2

/-- The cell-count profile, coarse to fine. -/
noncomputable def cellProfile (δ : ℝ) (a : ℕ → ℕ) (ρ : ℕ → ℝ) (top j : ℕ) : ℝ :=
  Real.logb (1 / δ) (levelDens a ρ top / levelDens a ρ (top - j))

lemma levelDens_pos (a : ℕ → ℕ) {ρ : ℕ → ℝ} (hρ : ∀ k, 0 < ρ k) (k : ℕ) :
    0 < levelDens a ρ k := by
  unfold levelDens
  have := hρ k
  positivity

lemma one_lt_inv_base {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 1 < 1 / δ := by
  rw [lt_div_iff₀ hδ]; linarith

@[simp] lemma cellProfile_zero (δ : ℝ) (a : ℕ → ℕ) {ρ : ℕ → ℝ} (hρ : ∀ k, 0 < ρ k) (top : ℕ) :
    cellProfile δ a ρ top 0 = 0 := by
  simp [cellProfile, div_self (levelDens_pos a hρ top).ne']

/-- The profile difference between two depths. -/
lemma cellProfile_sub (δ : ℝ) (a : ℕ → ℕ) {ρ : ℕ → ℝ} (hρ : ∀ k, 0 < ρ k) (top i j : ℕ) :
    cellProfile δ a ρ top j - cellProfile δ a ρ top i =
      Real.logb (1 / δ) (levelDens a ρ (top - i) / levelDens a ρ (top - j)) := by
  have hT := levelDens_pos a hρ top
  have hi := levelDens_pos a hρ (top - i)
  have hj := levelDens_pos a hρ (top - j)
  unfold cellProfile
  rw [← Real.logb_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- **Upward step.** -/
lemma cellProfile_step_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (a : ℕ → ℕ) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) {top j : ℕ} {B : ℝ}
    (hB : levelDens a ρ (top - j) ≤ B * levelDens a ρ (top - (j + 1))) :
    cellProfile δ a ρ top (j + 1) - cellProfile δ a ρ top j ≤ Real.logb (1 / δ) B := by
  rw [cellProfile_sub δ a hρ]
  have hj := levelDens_pos a hρ (top - j)
  have hj1 := levelDens_pos a hρ (top - (j + 1))
  apply Real.logb_le_logb_of_le (one_lt_inv_base hδ hδ1) (by positivity)
  rw [div_le_iff₀ hj1]
  exact hB

/-- **Lower bound.** -/
lemma cellProfile_lower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (a : ℕ → ℕ) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) {top j : ℕ} {R : ℝ} (hR : 0 < R)
    (h : levelDens a ρ (top - j) ≤ R * levelDens a ρ top) :
    -Real.logb (1 / δ) R ≤ cellProfile δ a ρ top j := by
  have hT := levelDens_pos a hρ top
  have hj := levelDens_pos a hρ (top - j)
  rw [← Real.logb_inv]
  apply Real.logb_le_logb_of_le (one_lt_inv_base hδ hδ1) (by positivity)
  rw [le_div_iff₀ hj, inv_mul_eq_div, div_le_iff₀ hR]
  linarith

/-- Translation: `G j ≤ G i` means the level `top - i` is at most as dense as `top - j`. -/
lemma levelDens_le_of_profile_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (a : ℕ → ℕ)
    {ρ : ℕ → ℝ} (hρ : ∀ k, 0 < ρ k) {top i j : ℕ}
    (h : cellProfile δ a ρ top j ≤ cellProfile δ a ρ top i) :
    levelDens a ρ (top - i) ≤ levelDens a ρ (top - j) := by
  have h0 : 0 ≤ cellProfile δ a ρ top i - cellProfile δ a ρ top j := by linarith
  rw [cellProfile_sub δ a hρ] at h0
  have hi := levelDens_pos a hρ (top - i)
  have hj := levelDens_pos a hρ (top - j)
  rw [Real.le_logb_iff_rpow_le (one_lt_inv_base hδ hδ1) (by positivity), Real.rpow_zero,
    le_div_iff₀ hi, one_mul] at h0
  exact h0

/-- Translation: `G i - c ≤ G j` means `dens (top - j) ≤ (1/δ)^c dens (top - i)`. -/
lemma levelDens_le_of_profile_sub_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (a : ℕ → ℕ)
    {ρ : ℕ → ℝ} (hρ : ∀ k, 0 < ρ k) {top i j : ℕ} {c : ℝ}
    (h : cellProfile δ a ρ top i - c ≤ cellProfile δ a ρ top j) :
    levelDens a ρ (top - j) ≤ (1 / δ) ^ c * levelDens a ρ (top - i) := by
  have h0 : cellProfile δ a ρ top i - cellProfile δ a ρ top j ≤ c := by linarith
  rw [cellProfile_sub δ a hρ] at h0
  have hi := levelDens_pos a hρ (top - i)
  have hj := levelDens_pos a hρ (top - j)
  rw [Real.logb_le_iff_le_rpow (one_lt_inv_base hδ hδ1) (by positivity), div_le_iff₀ hi] at h0
  exact h0

/-! ### Density bounds from the family -/

/-- The population of the cell of `i` at grid size `s` (o038/x0305's `pop … (lineCell s)`). -/
noncomputable def cellPop {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n)) (s : ℝ)
    (i : Fin n) : ℕ :=
  (S.filter (fun j => lineGridCell s (x j) (v j) = lineGridCell s (x i) (v i))).card

open Classical in
/-- Frostman bounds every level density: `dens k ≤ 384 K |S|` when every level-`k` cell lies in the
`ρ_k`-tube of one of its members. -/
theorem levelDens_le_of_frostman {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n))
    (hS : S.Nonempty) {δ K : ℝ} (a : ℕ → ℕ) (ρ : ℕ → ℝ) (k : ℕ) (hK : 0 ≤ K)
    (hρk : 0 < ρ k) (hρk1 : ρ k ≤ 1) (hv : ∀ i ∈ S, ‖v i‖ = 1)
    (hbal : ∀ i ∈ S, 2 ^ a k ≤ cellPop x v S (ρ k / 20) i)
    (hcont : ∀ i ∈ S, ∀ j ∈ S, lineGridCell (ρ k / 20) (x j) (v j) =
      lineGridCell (ρ k / 20) (x i) (v i) → Tube δ (x j) (v j) ⊆ Tube (ρ k) (x i) (v i))
    (hF : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((S.filter (fun j => Tube δ (x j) (v j) ⊆ U)).card : ℝ) ≤
        ENNReal.ofReal (K * S.card) * volume U) :
    levelDens a ρ k ≤ 384 * K * S.card := by
  classical
  obtain ⟨i, hi⟩ := hS
  have hpop := card_fibre_le_of_frostman x v S (fun j => lineGridCell (ρ k / 20) (x j) (v j)) i
    (Tube (ρ k) (x i) (v i)) hK (by positivity : (0 : ℝ) ≤ 384 * ρ k ^ 2) (tube_convex _ _ _)
    (tube_volume_upper hρk hρk1 (x i) (v i) (hv i hi)) (fun j hj hji => hcont i hi j hj hji) hF
  have h2 : ((2 : ℝ) ^ a k) ≤ K * S.card * (384 * ρ k ^ 2) := by
    have := hbal i hi
    have : ((2 : ℕ) ^ a k : ℝ) ≤ (cellPop x v S (ρ k / 20) i : ℝ) := by exact_mod_cast this
    calc ((2 : ℝ) ^ a k) = ((2 : ℕ) ^ a k : ℝ) := by push_cast; ring
      _ ≤ _ := this
      _ ≤ K * S.card * (384 * ρ k ^ 2) := hpop
  unfold levelDens
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The step bound of the densities: a coarse cell of size `s` holds at most `(4 s / s' + 2)⁶`
cells of size `s'`, so `dens coarse ≤ 2 (4 s/s' + 2)⁶ (ρ'/ρ)² dens fine`. -/
theorem levelDens_step {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n)) (hS : S.Nonempty)
    (a : ℕ → ℕ) (ρ : ℕ → ℝ) (k k' : ℕ) (hρk : 0 < ρ k) (hρk' : 0 < ρ k')
    (hlow : ∀ i ∈ S, 2 ^ a k ≤ cellPop x v S (ρ k / 20) i)
    (hup : ∀ i ∈ S, cellPop x v S (ρ k' / 20) i < 2 ^ (a k' + 1)) :
    levelDens a ρ k ≤
      (2 * (4 * ρ k / ρ k' + 2) ^ 6 * (ρ k' ^ 2 / ρ k ^ 2)) * levelDens a ρ k' := by
  classical
  obtain ⟨i, hi⟩ := hS
  have hs : 0 < ρ k / 20 := by positivity
  have hs' : 0 < ρ k' / 20 := by positivity
  have hP : ∀ j ∈ S, ((S.filter (fun j' => lineGridCell (ρ k' / 20) (x j') (v j') =
      lineGridCell (ρ k' / 20) (x j) (v j))).card : ℝ) ≤ 2 * 2 ^ a k' := by
    intro j hj
    have := hup j hj
    have : (cellPop x v S (ρ k' / 20) j : ℝ) < ((2 ^ (a k' + 1) : ℕ) : ℝ) := by exact_mod_cast this
    unfold cellPop at this
    push_cast at this
    rw [pow_succ] at this
    linarith
  have hsub := card_lineCell_le_subcells S x v hs hs' (by positivity) hP i
  have hratio : 4 * (ρ k / 20) / (ρ k' / 20) = 4 * ρ k / ρ k' := by
    field_simp
  rw [hratio] at hsub
  have hlowi : ((2 : ℝ) ^ a k) ≤ (cellPop x v S (ρ k / 20) i : ℝ) := by
    have := hlow i hi
    exact_mod_cast this
  unfold cellPop at hlowi
  have hmain : (2 : ℝ) ^ a k ≤ (4 * ρ k / ρ k' + 2) ^ 6 * (2 * 2 ^ a k') := hlowi.trans hsub
  unfold levelDens
  rw [div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ a k ≤ (4 * ρ k / ρ k' + 2) ^ 6 * (2 * 2 ^ a k') := hmain
    _ = 2 * (4 * ρ k / ρ k' + 2) ^ 6 * (ρ k' ^ 2 / ρ k ^ 2) * (2 ^ a k' / ρ k' ^ 2) *
        ρ k ^ 2 := by
        field_simp

/-- The top density is not too small: the whole family meets at most `(80/ρ + 2)⁶` cells of size
`ρ/20`, so `dens top ≥ |S| / (2 (80/ρ + 2)⁶ ρ²)`. -/
theorem levelDens_top_lower {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (a : ℕ → ℕ) (ρ : ℕ → ℝ) (k : ℕ) (hρk : 0 < ρ k)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hball : ∀ i ∈ S, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hup : ∀ i ∈ S, cellPop x v S (ρ k / 20) i < 2 ^ (a k + 1)) :
    (S.card : ℝ) ≤ (2 * (80 / ρ k + 2) ^ 6 * ρ k ^ 2) * levelDens a ρ k := by
  classical
  have hs : 0 < ρ k / 20 := by positivity
  have hxnorm : ∀ i ∈ S, ‖x i‖ ≤ 1 := by
    intro i hi
    have := hball i hi (self_subset_thickening hδ _ (left_mem_segment ℝ (x i) (x i + v i)))
    exact (mem_ball_zero_iff.mp this).le
  have hfoot : ∀ i ∈ S, ‖lineFoot (x i) (v i)‖ ≤ 1 := by
    intro i hi
    have hsq : ‖lineFoot (x i) (v i)‖ ^ 2 ≤ ‖x i‖ ^ 2 := by
      unfold lineFoot
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hv i hi,
        mul_one, sq_abs]
      nlinarith [sq_nonneg (inner ℝ (x i) (v i))]
    have := hxnorm i hi
    nlinarith [norm_nonneg (lineFoot (x i) (v i)), norm_nonneg (x i)]
  have hD₁ : ∀ i ∈ S, ∀ j ∈ S, ‖lineFoot (x i) (v i) - lineFoot (x j) (v j)‖ ≤ 2 := by
    intro i hi j hj
    exact (norm_sub_le _ _).trans (by linarith [hfoot i hi, hfoot j hj])
  have hD₂ : ∀ i ∈ S, ∀ j ∈ S, ‖v i - v j‖ ≤ 2 := by
    intro i hi j hj
    exact (norm_sub_le _ _).trans (by linarith [(hv i hi).le, (hv j hj).le])
  have himg := card_lineCells_le S (fun i => lineFoot (x i) (v i)) v hs (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 2) hD₁ hD₂
  have he : (2 * 2 / (ρ k / 20) + 2) ^ 3 * (2 * 2 / (ρ k / 20) + 2) ^ 3 = (80 / ρ k + 2) ^ 6 := by
    field_simp
    ring
  rw [he] at himg
  -- every cell holds fewer than `2^(a k + 1)` tubes
  set f : Fin n → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun j => lineGridCell (ρ k / 20) (x j) (v j)
    with hf
  have hP : ∀ j ∈ S, ((S.filter (fun j' => f j' = f j)).card : ℝ) ≤ 2 * 2 ^ a k := by
    intro j hj
    have := hup j hj
    have : (cellPop x v S (ρ k / 20) j : ℝ) < ((2 ^ (a k + 1) : ℕ) : ℝ) := by exact_mod_cast this
    unfold cellPop at this
    push_cast at this
    rw [pow_succ] at this
    linarith
  have hcard : (S.card : ℝ) ≤ ((S.image f).card : ℝ) * (2 * 2 ^ a k) := by
    rw [Finset.card_eq_sum_card_image f S]
    push_cast
    calc ∑ g ∈ S.image f, ((S.filter (fun j => f j = g)).card : ℝ)
        ≤ ∑ _g ∈ S.image f, (2 * 2 ^ a k : ℝ) := by
          apply Finset.sum_le_sum
          intro g hg
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
          exact hP j hj
      _ = ((S.image f).card : ℝ) * (2 * 2 ^ a k) := by rw [Finset.sum_const, nsmul_eq_mul]
  have himgS : S.image f = S.image (fun i => (gridCell (ρ k / 20) (lineFoot (x i) (v i)),
      gridCell (ρ k / 20) (v i))) := rfl
  rw [himgS] at hcard
  unfold levelDens
  calc (S.card : ℝ) ≤ _ := hcard
    _ ≤ (80 / ρ k + 2) ^ 6 * (2 * 2 ^ a k) := by gcongr
    _ = 2 * (80 / ρ k + 2) ^ 6 * ρ k ^ 2 * (2 ^ a k / ρ k ^ 2) := by
        field_simp

/-! ### The packaged profile bounds -/

open Classical in
/-- **Profile lower bound.**  For a `K`-Frostman family whose level-`k` cells lie in `ρ_k`-tubes
of their members, `G j ≥ -log_{1/δ}(768 · 82⁶ · K / ρ_top⁴)` for every `j ≤ top`. -/
theorem cellProfile_lower_of_family {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n))
    (hS : S.Nonempty) {δ K : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (a : ℕ → ℕ) (ρ : ℕ → ℝ) (top : ℕ)
    (hK : 0 < K) (hρ : ∀ k, 0 < ρ k) (hρ1 : ∀ k ≤ top, ρ k ≤ 1)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hball : ∀ i ∈ S, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hlow : ∀ k ≤ top, ∀ i ∈ S, 2 ^ a k ≤ cellPop x v S (ρ k / 20) i)
    (hupTop : ∀ i ∈ S, cellPop x v S (ρ top / 20) i < 2 ^ (a top + 1))
    (hcont : ∀ k ≤ top, ∀ i ∈ S, ∀ j ∈ S, lineGridCell (ρ k / 20) (x j) (v j) =
      lineGridCell (ρ k / 20) (x i) (v i) → Tube δ (x j) (v j) ⊆ Tube (ρ k) (x i) (v i))
    (hF : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((S.filter (fun j => Tube δ (x j) (v j) ⊆ U)).card : ℝ) ≤
        ENNReal.ofReal (K * S.card) * volume U) :
    ∀ j ≤ top, -Real.logb (1 / δ) (768 * 82 ^ 6 * K / ρ top ^ 4) ≤ cellProfile δ a ρ top j := by
  intro j hj
  have hk : top - j ≤ top := Nat.sub_le top j
  have hρt := hρ top
  have hρt1 := hρ1 top le_rfl
  have hdk := levelDens_le_of_frostman x v S hS a ρ (top - j) hK.le (hρ _) (hρ1 _ hk) hv
    (hlow _ hk) (hcont _ hk) hF
  have htop := levelDens_top_lower x v S hδ a ρ top hρt hv hball hupTop
  have hdT := levelDens_pos a hρ top
  have hbase : (80 / ρ top + 2) ^ 6 * ρ top ^ 2 ≤ 82 ^ 6 / ρ top ^ 4 := by
    have h1 : 80 / ρ top + 2 ≤ 82 / ρ top := by
      rw [div_add' _ _ _ hρt.ne', div_le_div_iff_of_pos_right hρt]
      linarith
    have h2 : (80 / ρ top + 2) ^ 6 ≤ (82 / ρ top) ^ 6 := by
      gcongr
    calc (80 / ρ top + 2) ^ 6 * ρ top ^ 2 ≤ (82 / ρ top) ^ 6 * ρ top ^ 2 := by gcongr
      _ = 82 ^ 6 / ρ top ^ 4 := by field_simp
  apply cellProfile_lower hδ hδ1 a hρ (by positivity)
  calc levelDens a ρ (top - j) ≤ 384 * K * S.card := hdk
    _ ≤ 384 * K * ((2 * (80 / ρ top + 2) ^ 6 * ρ top ^ 2) * levelDens a ρ top) := by gcongr
    _ = (768 * K) * ((80 / ρ top + 2) ^ 6 * ρ top ^ 2) * levelDens a ρ top := by ring
    _ ≤ (768 * K) * (82 ^ 6 / ρ top ^ 4) * levelDens a ρ top := by gcongr
    _ = 768 * 82 ^ 6 * K / ρ top ^ 4 * levelDens a ρ top := by ring

/-- **Profile step bound.**  If consecutive radii have ratio `L`, then
`G (j+1) - G j ≤ log_{1/δ}(2 (4L+2)⁶ / L²)`. -/
theorem cellProfile_step_of_family {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n))
    (hS : S.Nonempty) {δ L : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (a : ℕ → ℕ) (ρ : ℕ → ℝ) (top : ℕ)
    (hρ : ∀ k, 0 < ρ k) (hL : 0 < L) (hratio : ∀ k, ρ (k + 1) = L * ρ k)
    (hlow : ∀ k ≤ top, ∀ i ∈ S, 2 ^ a k ≤ cellPop x v S (ρ k / 20) i)
    (hup : ∀ k ≤ top, ∀ i ∈ S, cellPop x v S (ρ k / 20) i < 2 ^ (a k + 1)) :
    ∀ j < top, cellProfile δ a ρ top (j + 1) - cellProfile δ a ρ top j ≤
      Real.logb (1 / δ) (2 * (4 * L + 2) ^ 6 / L ^ 2) := by
  intro j hj
  obtain ⟨k', hk'⟩ : ∃ k', top - j = k' + 1 := ⟨top - j - 1, by omega⟩
  have hk'' : top - (j + 1) = k' := by omega
  have hstep := levelDens_step x v S hS a ρ (k' + 1) k' (hρ _) (hρ _)
    (hlow _ (by omega)) (hup _ (by omega))
  have hρL : ρ (k' + 1) = L * ρ k' := hratio k'
  have hρk' := hρ k'
  have hcoef : 2 * (4 * ρ (k' + 1) / ρ k' + 2) ^ 6 * (ρ k' ^ 2 / ρ (k' + 1) ^ 2) =
      2 * (4 * L + 2) ^ 6 / L ^ 2 := by
    rw [hρL]
    field_simp
  rw [hcoef] at hstep
  apply cellProfile_step_le hδ hδ1 a hρ
  rw [hk', hk'']
  exact hstep

/-! ### From the scale choice to the population facts of (B) -/

/-- **Fullness.**  If the scale choice gives `G i₀ - c ≤ G j₂` and `2 δ^ζ₂ ≤ δ^c`, then at
`τ = ρ (top - j₂)`, `ρ = ρ (top - i₀)` the populations satisfy x0305's `SB_of_KTcase` fullness
`δ^ζ₂ (ρ/τ)² 2^(a_τ + 1) ≤ 2^(a_ρ)`. -/
theorem fullness_of_profile {δ c ζ₂ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (a : ℕ → ℕ) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) {top i₀ j₂ : ℕ}
    (h : cellProfile δ a ρ top i₀ - c ≤ cellProfile δ a ρ top j₂)
    (hc : 2 * δ ^ ζ₂ ≤ δ ^ c) :
    δ ^ ζ₂ * (ρ (top - i₀) / ρ (top - j₂)) ^ 2 * 2 ^ (a (top - j₂) + 1) ≤
      (2 : ℝ) ^ a (top - i₀) := by
  have hd := levelDens_le_of_profile_sub_le hδ hδ1 a hρ h
  have hρτ := hρ (top - j₂)
  have hρρ := hρ (top - i₀)
  have hinv : (1 / δ) ^ c * δ ^ c = 1 := by
    rw [← Real.mul_rpow (by positivity) hδ.le, one_div, inv_mul_cancel₀ hδ.ne', Real.one_rpow]
  unfold levelDens at hd
  -- `2^(a τ)/τ² ≤ (1/δ)^c 2^(a ρ)/ρ²`
  have hd' : (2 : ℝ) ^ a (top - j₂) * ρ (top - i₀) ^ 2 ≤
      (1 / δ) ^ c * 2 ^ a (top - i₀) * ρ (top - j₂) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hd
    have e : (1 / δ) ^ c * (2 ^ a (top - i₀) / ρ (top - i₀) ^ 2) * ρ (top - j₂) ^ 2 * ρ (top - i₀) ^ 2
        = (1 / δ) ^ c * 2 ^ a (top - i₀) * ρ (top - j₂) ^ 2 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg (ρ (top - i₀))), e]
  have h3 : δ ^ c * ((2 : ℝ) ^ a (top - j₂) * ρ (top - i₀) ^ 2) ≤
      (2 : ℝ) ^ a (top - i₀) * ρ (top - j₂) ^ 2 := by
    calc δ ^ c * ((2 : ℝ) ^ a (top - j₂) * ρ (top - i₀) ^ 2)
        ≤ δ ^ c * ((1 / δ) ^ c * 2 ^ a (top - i₀) * ρ (top - j₂) ^ 2) :=
          mul_le_mul_of_nonneg_left hd' (by positivity)
      _ = ((1 / δ) ^ c * δ ^ c) * (2 ^ a (top - i₀) * ρ (top - j₂) ^ 2) := by ring
      _ = (2 : ℝ) ^ a (top - i₀) * ρ (top - j₂) ^ 2 := by rw [hinv, one_mul]
  have h4 : (2 * δ ^ ζ₂) * ((2 : ℝ) ^ a (top - j₂) * ρ (top - i₀) ^ 2) ≤
      (2 : ℝ) ^ a (top - i₀) * ρ (top - j₂) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right hc (by positivity)) h3
  have e : δ ^ ζ₂ * (ρ (top - i₀) / ρ (top - j₂)) ^ 2 * 2 ^ (a (top - j₂) + 1) =
      (2 * δ ^ ζ₂) * ((2 : ℝ) ^ a (top - j₂) * ρ (top - i₀) ^ 2) / ρ (top - j₂) ^ 2 := by
    rw [pow_succ (2 : ℝ) (a (top - j₂)), div_pow]
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  exact h4

open Classical in
/-- **Round-box constant at the coarse level.**  If the scale choice gives `G j₂ ≤ G l` for every
`l ∈ [i₀, top]` (Katz–Tao between `ρ = ρ (top - i₀)` and `τ = ρ (top - j₂)`, and Frostman below
`τ`), then every set `F ⊆ S` with fewer than `2^(a_ρ + 1)` tubes (e.g. a level-`ρ` cell) satisfies
the round-box hypothesis of x0318's `fibre_dichotomy` with
`K = 800 · 122³ · 16³ · L² Λ · dens_τ · δ²`, where `dens_τ = 2^(a_τ)/τ²`. -/
theorem roundBox_of_profile {n : ℕ} (x v : Fin n → Space) (S F : Finset (Fin n)) (hFS : F ⊆ S)
    {δ L Λ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 1 ≤ L) (hΛ : 1 ≤ Λ) (a : ℕ → ℕ) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (hρ0 : ρ 0 ≤ 20 * L * δ) (hρstep : ∀ k, ρ (k + 1) ≤ L * ρ k)
    {top i₀ j₂ : ℕ} (hi₀ : i₀ ≤ top) (hρtop : ρ (top - i₀) ≤ 2)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hball : ∀ i ∈ S, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hanti : ∀ i ∈ S, ∀ j ∈ S, 1 ≤ ‖v i + v j‖)
    (hup : ∀ k ≤ top - i₀, ∀ i ∈ S, cellPop x v S (ρ k / 20) i < 2 ^ (a k + 1))
    (hFcard : F.card < 2 ^ (a (top - i₀) + 1))
    (hKT : ∀ l, i₀ ≤ l → l ≤ top → cellProfile δ a ρ top j₂ ≤ cellProfile δ a ρ top l) :
    ∀ (a' b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space), δ ≤ a' → a' ≤ b → b ≤ Λ * a' → b ≤ 2 →
      ((F.filter (fun i => Tube δ (x i) (v i) ⊆
        e '' {z : Space | |z 0| ≤ a' ∧ |z 1| ≤ b ∧ |z 2| ≤ 2})).card : ℝ) * δ ^ 2 ≤
        (400 * 122 ^ 3 * 16 ^ 3 * L ^ 2 * Λ * (2 * levelDens a ρ (top - j₂) * δ ^ 2)) * a' * b := by
  set D := 2 * levelDens a ρ (top - j₂) * δ ^ 2 with hD
  have hDpos : 0 ≤ D := by have := levelDens_pos a hρ (top - j₂); positivity
  -- every level `k ≤ top - i₀` is at most as dense as `τ`
  have hdens : ∀ k ≤ top - i₀, levelDens a ρ k ≤ levelDens a ρ (top - j₂) := by
    intro k hk
    have hl := hKT (top - k) (by omega) (by omega)
    have := levelDens_le_of_profile_le hδ hδ1 a hρ hl
    rwa [show top - (top - k) = k by omega] at this
  have hPD : ∀ k ≤ top - i₀, ((2 : ℝ) ^ (a k + 1)) * δ ^ 2 ≤ D * ρ k ^ 2 := by
    intro k hk
    have h := hdens k hk
    unfold levelDens at h
    have hρk := hρ k
    rw [div_le_iff₀ (by positivity)] at h
    rw [hD, pow_succ]
    unfold levelDens
    have e : 2 * (2 ^ a (top - j₂) / ρ (top - j₂) ^ 2) * δ ^ 2 * ρ k ^ 2 =
        2 * δ ^ 2 * ((2 ^ a (top - j₂) / ρ (top - j₂) ^ 2) * ρ k ^ 2) := by ring
    rw [e]
    nlinarith [sq_nonneg δ]
  apply roundBox_of_levels x v F ρ (fun k => (2 : ℝ) ^ (a k + 1)) (top - i₀) hδ hL hDpos hΛ hρ hρ0
    hρstep hρtop (fun i hi => hv i (hFS hi)) (fun i hi => hball i (hFS hi))
    (fun i hi j hj => hanti i (hFS hi) j (hFS hj)) (fun k _ => by positivity)
  · intro k hk i hi
    have h1 : (F.filter (fun j => lineGridCell (ρ k / 20) (x j) (v j) =
        lineGridCell (ρ k / 20) (x i) (v i))).card ≤ cellPop x v S (ρ k / 20) i :=
      Finset.card_le_card (Finset.filter_subset_filter _ hFS)
    have h2 := hup k hk i (hFS hi)
    have : ((F.filter (fun j => lineGridCell (ρ k / 20) (x j) (v j) =
        lineGridCell (ρ k / 20) (x i) (v i))).card : ℝ) < ((2 ^ (a k + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1.trans_lt h2
    push_cast at this
    exact this.le
  · exact hPD
  · have h1 : (F.card : ℝ) < ((2 ^ (a (top - i₀) + 1) : ℕ) : ℝ) := by exact_mod_cast hFcard
    push_cast at h1
    calc (F.card : ℝ) * δ ^ 2 ≤ (2 : ℝ) ^ (a (top - i₀) + 1) * δ ^ 2 := by gcongr
      _ ≤ D * ρ (top - i₀) ^ 2 := hPD _ le_rfl

open Classical in
/-- **Round-box constant with slack** (the sticky case).  If `G j - c ≤ G l` for every
`l ∈ [i₀, top]` (with `c ≥ 0`; e.g. `j = i₀` and `c = ξ` in the sticky case, `j = j₂` and `c = 0`
in the separated case), then every `F ⊆ S` with fewer than `2^(a (top - i₀) + 1)` tubes satisfies
the round-box hypothesis with `K = 800 · 122³ · 16³ · L² Λ · (1/δ)^c · dens (top - j) · δ²`. -/
theorem roundBox_of_profile_slack {n : ℕ} (x v : Fin n → Space) (S F : Finset (Fin n))
    (hFS : F ⊆ S) {δ L Λ c : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 1 ≤ L) (hΛ : 1 ≤ Λ)
    (a : ℕ → ℕ) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (hρ0 : ρ 0 ≤ 20 * L * δ) (hρstep : ∀ k, ρ (k + 1) ≤ L * ρ k)
    {top i₀ j : ℕ} (hi₀ : i₀ ≤ top) (hρtop : ρ (top - i₀) ≤ 2)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hball : ∀ i ∈ S, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hanti : ∀ i ∈ S, ∀ j ∈ S, 1 ≤ ‖v i + v j‖)
    (hup : ∀ k ≤ top - i₀, ∀ i ∈ S, cellPop x v S (ρ k / 20) i < 2 ^ (a k + 1))
    (hFcard : F.card < 2 ^ (a (top - i₀) + 1))
    (hprof : ∀ l, i₀ ≤ l → l ≤ top → cellProfile δ a ρ top j - c ≤ cellProfile δ a ρ top l) :
    ∀ (a' b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space), δ ≤ a' → a' ≤ b → b ≤ Λ * a' → b ≤ 2 →
      ((F.filter (fun i => Tube δ (x i) (v i) ⊆
        e '' {z : Space | |z 0| ≤ a' ∧ |z 1| ≤ b ∧ |z 2| ≤ 2})).card : ℝ) * δ ^ 2 ≤
        (400 * 122 ^ 3 * 16 ^ 3 * L ^ 2 * Λ *
          (2 * ((1 / δ) ^ c * levelDens a ρ (top - j)) * δ ^ 2)) * a' * b := by
  set D := 2 * ((1 / δ) ^ c * levelDens a ρ (top - j)) * δ ^ 2 with hD
  have hDpos : 0 ≤ D := by have := levelDens_pos a hρ (top - j); positivity
  have hdens : ∀ k ≤ top - i₀, levelDens a ρ k ≤ (1 / δ) ^ c * levelDens a ρ (top - j) := by
    intro k hk
    have hl := hprof (top - k) (by omega) (by omega)
    have := levelDens_le_of_profile_sub_le hδ hδ1 a hρ hl
    rwa [show top - (top - k) = k by omega] at this
  have hPD : ∀ k ≤ top - i₀, ((2 : ℝ) ^ (a k + 1)) * δ ^ 2 ≤ D * ρ k ^ 2 := by
    intro k hk
    have h := hdens k hk
    have hρk := hρ k
    have h' : (2 : ℝ) ^ (a k) ≤ (1 / δ) ^ c * levelDens a ρ (top - j) * ρ k ^ 2 := by
      have e0 : levelDens a ρ k = (2 : ℝ) ^ (a k) / ρ k ^ 2 := rfl
      rw [e0, div_le_iff₀ (by positivity)] at h
      exact h
    rw [hD, pow_succ (2 : ℝ) (a k)]
    have h2 := mul_le_mul_of_nonneg_left h' (by positivity : (0 : ℝ) ≤ 2 * δ ^ 2)
    nlinarith [h2]
  apply roundBox_of_levels x v F ρ (fun k => (2 : ℝ) ^ (a k + 1)) (top - i₀) hδ hL hDpos hΛ hρ hρ0
    hρstep hρtop (fun i hi => hv i (hFS hi)) (fun i hi => hball i (hFS hi))
    (fun i hi j hj => hanti i (hFS hi) j (hFS hj)) (fun k _ => by positivity)
  · intro k hk i hi
    have h1 : (F.filter (fun j => lineGridCell (ρ k / 20) (x j) (v j) =
        lineGridCell (ρ k / 20) (x i) (v i))).card ≤ cellPop x v S (ρ k / 20) i :=
      Finset.card_le_card (Finset.filter_subset_filter _ hFS)
    have h2 := hup k hk i (hFS hi)
    have : ((F.filter (fun j => lineGridCell (ρ k / 20) (x j) (v j) =
        lineGridCell (ρ k / 20) (x i) (v i))).card : ℝ) < ((2 ^ (a k + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1.trans_lt h2
    push_cast at this
    exact this.le
  · exact hPD
  · have h1 : (F.card : ℝ) < ((2 ^ (a (top - i₀) + 1) : ℕ) : ℝ) := by exact_mod_cast hFcard
    push_cast at h1
    calc (F.card : ℝ) * δ ^ 2 ≤ (2 : ℝ) ^ (a (top - i₀) + 1) * δ ^ 2 := by gcongr
      _ ≤ D * ρ (top - i₀) ^ 2 := hPD _ le_rfl

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
