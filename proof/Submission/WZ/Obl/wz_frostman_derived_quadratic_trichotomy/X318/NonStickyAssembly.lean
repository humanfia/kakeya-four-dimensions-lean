-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NonStickyAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NonStickyBranch
-- Copied from session x0318 (o070 branch, commit 2c4a35f, file NonStickyAssembly.lean), namespace renamed.

/-!
# The non-sticky branch, assembled

`nonsticky_fixed` composes, at one scale `δ`, the pieces of `NonStickyBranch.lean` for a prepared
set `S` (x0305's `Prepared`, o038 branch x0305, stated here with explicit hypotheses):

* x0305's `cell_cover` (copied under `X305/`) gives the parents: the level-`ρ` cells, as an exact
  cover by separated `ρ`-tubes;
* x0338's `roundBox_of_profile` (`CellProfile.lean`) gives the round-box bound in every parent from
  the minimality of `G j₂` on `[i₀, top]`;
* `cell_refine` splits the parents by `KTGood`: flat majority goes to `flat_side` (frozen `C`),
  otherwise `kt_side` (frozen `SB`), whose fullness comes from x0338's `fullness_of_profile`.

`nonsticky_branch` chooses `ν = ζF = min ζ₃ ω / 100`, `θ = ω/2`, `Λ = 16 δ^(-ν-ζ₂/200)` and a
threshold `δ₁` for all numeric side conditions.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
open Set MeasureTheory
open scoped ENNReal

/-- Counting along the enumeration of a finset. -/
lemma card_filter_enum {n : ℕ} (S : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun j : Fin S.card => P (S.equivFin.symm j).1)).card =
      (S.filter P).card := by
  rw [← WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.ncard_enum S P, ← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The non-sticky branch at a fixed scale.** A prepared set `S` (unit directions, tubes in
the unit ball, pairwise half-overlap, aligned, no antipodes, one residue class and balanced
populations at every level `k ≤ top` of `ρ_k = 2δL^k`, global Frostman) with a profile pair
`i₀ < j₂` gives frozen `SB` or frozen `C` on a `δ^ω` share. -/
theorem nonsticky_fixed {δ ν ζ ζ₁ ζ₂ ζ₃ θ ω ζ' KF Λ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hν : 0 ≤ ν) (hζ : 0 ≤ ζ) (hζ₂ : 0 ≤ ζ₂)
    {L : ℕ} (hL2 : 2 ≤ L) {top : ℕ} (htop : 2 * δ * (L : ℝ) ^ top ≤ 1 / 10000)
    (hdich : FibreDich ν δ)
    (hΛ : 16 * δ ^ (-ν - ζ₂ / 200) ≤ Λ) (h64 : 64 * δ ^ ν ≤ 1)
    (herror : localFlatLoss * δ ^ (ζ₃ - ζ - 5 * (2 * ν)) ≤ 1)
    (hretain : 2 * δ ^ (θ - 2 * ν) ≤ 1)
    (hcτ : 8 * (400 * 122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * Λ * δ ^ (-ν) ≤
      δ ^ (-ζ₂) * δ ^ (2 * ν))
    (hc' : 2 * δ ^ ζ' ≤ δ ^ (ζ₂ / 2)) (h8 : 8 * δ ^ ζ₂ ≤ δ ^ (3 * ν) * δ ^ ζ')
    (hζ₂4 : 4 ≤ δ ^ (-ζ₂)) (hfin2 : 2 * δ ^ ω ≤ δ ^ θ)
    {m : ℕ} (x v : Fin m → Space) (S : Finset (Fin m)) (hS : S.Nonempty)
    (hpig : ∀ n' : ℕ, n' ≤ S.card → (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
        (Nat.log 2 ⌊(n' : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν))
    (hsmall : 16 * ((Nat.log 2 S.card : ℝ) + 1) * δ ^ ν ≤ 1)
    (hKF0 : 0 ≤ KF) (hKFζ : 2 * KF ≤ δ ^ (-ζ))
    (hKF2 : 2 * (KF * (16 * ((Nat.log 2 S.card : ℝ) + 1) ^ 2 * δ ^ (-ν))) ≤ δ ^ (-ζ₂))
    (hfin1 : δ ^ ω * (16 * ((Nat.log 2 S.card : ℝ) + 1) ^ 2 * δ ^ (-ν)) ≤ 1)
    (hv : ∀ i ∈ S, ‖v i‖ = 1)
    (hT : ∀ i ∈ S, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i)))
    (hcan : ∀ i ∈ S, x i = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.leftStart δ (x i) (v i))
    (hanti : ∀ i ∈ S, ∀ j ∈ S, 1 ≤ ‖v i + v j‖)
    (a : ℕ → ℕ)
    (hcls : ∀ k ≤ top, ∀ i ∈ S, ∀ i' ∈ S,
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i) (v i) =
        WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i') (v i'))
    (hpop : ∀ k ≤ top, ∀ i ∈ S,
      2 ^ a k ≤ WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.pop S (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i ∧
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.pop S (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i <
        2 ^ (a k + 1))
    (hFG : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal (KF * S.card) * volume W)
    {i₀ j₂ : ℕ} (hij : i₀ < j₂) (hj₂ : j₂ ≤ top)
    (hprof : ∀ l, i₀ ≤ l → l ≤ top →
      cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j₂ ≤
        cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top l)
    (hgap : cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top i₀ - ζ₂ / 2 ≤
        cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j₂)
    (hsc : δ ^ (-ζ₁) ≤ (L : ℝ) ^ (j₂ - i₀)) :
    ∃ (k : ℕ) (g : Fin k → Fin m), Function.Injective g ∧ (∀ j, g j ∈ S) ∧
      δ ^ ω * S.card ≤ k ∧
      (WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.SBpred ζ₁ ζ₂ δ k
          (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))) ∨
        FlatPrisms ζ₂ ζ₃ δ (fun j => Tube δ (x (g j)) (v (g j)))) := by
  -- radii
  set ρf : ℕ → ℝ := fun k => 2 * δ * (L : ℝ) ^ k with hρf
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (le_trans (by norm_num) hL2)
  have hρpos : ∀ k, 0 < ρf k := fun k => by simp only [hρf]; positivity
  have hρmono : ∀ k k', k ≤ k' → ρf k ≤ ρf k' := by
    intro k k' h
    simp only [hρf]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 h) (by positivity)
  set τ := ρf (top - j₂) with hτ
  set ρ := ρf (top - i₀) with hρ
  set mm : ℕ := L ^ (j₂ - i₀) with hmm
  have hρm : ρ = (mm : ℝ) * τ := by
    simp only [hρ, hτ, hρf, hmm, Nat.cast_pow]
    have : top - i₀ = (j₂ - i₀) + (top - j₂) := by omega
    rw [this, pow_add]; ring
  have hmm2 : 2 ≤ mm := by
    calc 2 ≤ L := hL2
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (j₂ - i₀) := Nat.pow_le_pow_right (by omega) (by omega)
  have hδτ : 2 * δ ≤ τ := by
    have := hρmono 0 (top - j₂) (Nat.zero_le _)
    simpa [hρf] using this
  have hτρ : τ ≤ ρ := hρmono _ _ (by omega)
  have hρtop : ρ ≤ 1 / 10000 := (hρmono (top - i₀) top (Nat.sub_le _ _)).trans htop
  have hρ0 : 0 < ρ := hρpos _
  have hτ0 : 0 < τ := hρpos _
  have hscale : τ ≤ δ ^ ζ₁ * ρ := by
    rw [hρm]
    have hδζ : δ ^ ζ₁ * δ ^ (-ζ₁) = 1 := by rw [← Real.rpow_add hδ]; simp
    have hmmR : δ ^ (-ζ₁) ≤ (mm : ℝ) := by simpa [hmm] using hsc
    have hδ0 : 0 ≤ δ ^ ζ₁ := Real.rpow_nonneg hδ.le _
    calc τ = (δ ^ ζ₁ * δ ^ (-ζ₁)) * τ := by rw [hδζ, one_mul]
      _ ≤ (δ ^ ζ₁ * (mm : ℝ)) * τ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmmR hδ0) hτ0.le
      _ = δ ^ ζ₁ * ((mm : ℝ) * τ) := by ring
  -- re-indexing `S`
  set nS := S.card with hnS
  set e : Fin nS → Fin m := fun j => (S.equivFin.symm j).1 with he
  have he_inj : Function.Injective e := fun j j' h => S.equivFin.symm.injective (Subtype.ext h)
  have heS : ∀ j, e j ∈ S := fun j => (S.equivFin.symm j).2
  set xS : Fin nS → Space := fun j => x (e j) with hxS
  set vS : Fin nS → Space := fun j => v (e j) with hvS
  have hnS0 : 0 < nS := Finset.card_pos.mpr hS
  have hcount : ∀ (P : Fin m → Prop) [DecidablePred P],
      (Finset.univ.filter (fun j => P (e j))).card = (S.filter P).card :=
    fun P _ => card_filter_enum S P
  have hpopS : ∀ (κ : Fin m → (Fin 3 → ℤ) × (Fin 3 → ℤ)) (j : Fin nS),
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.pop Finset.univ (fun j => κ (e j)) j = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.pop S κ (e j) := by
    intro κ j
    unfold WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.pop
    exact hcount (fun i => κ i = κ (e j))
  have hvS' : ∀ j, ‖vS j‖ = 1 := fun j => hv _ (heS j)
  have hTS : ∀ j, Tube δ (xS j) (vS j) ⊆ Metric.ball 0 1 := fun j => hT _ (heS j)
  have hcanS : ∀ j, xS j = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.leftStart δ (xS j) (vS j) := fun j => hcan _ (heS j)
  have hantiS : ∀ j j', 1 ≤ ‖vS j + vS j'‖ := fun j j' => hanti _ (heS j) _ (heS j')
  have hsepS : Distinct (fun j => Tube δ (xS j) (vS j)) :=
    fun j j' hjj' => hsep _ (heS j) _ (heS j') (he_inj.ne hjj')
  have hclsS : ∀ k ≤ top, ∀ j j', WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 (ρf k) (xS j) (vS j) =
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 (ρf k) (xS j') (vS j') :=
    fun k hk j j' => hcls k hk _ (heS j) _ (heS j')
  have huniv_ne : (Finset.univ : Finset (Fin nS)).Nonempty := ⟨⟨0, hnS0⟩, Finset.mem_univ _⟩
  -- the parents: the exact cover by the cells at radius `ρ`
  obtain ⟨q, -, z, w, hw, hRsep, hexu, -, hrep⟩ := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.cell_cover hδ (by linarith) hρtop xS vS
    hvS' hTS hcanS hantiS Finset.univ huniv_ne
    (fun j _ j' _ => hclsS (top - i₀) (Nat.sub_le _ _) j j')
  have hexu' : ∀ j, ∃! l, Tube δ (xS j) (vS j) ⊆ Tube ρ (z l) (w l) :=
    fun j => hexu j (Finset.mem_univ j)
  set par : Fin nS → Fin q := fun j => Classical.choose (hexu' j).exists with hpardef
  have hpar : ∀ j, Tube δ (xS j) (vS j) ⊆ Tube ρ (z (par j)) (w (par j)) :=
    fun j => Classical.choose_spec (hexu' j).exists
  have huniq : ∀ j l, Tube δ (xS j) (vS j) ⊆ Tube ρ (z l) (w l) → l = par j :=
    fun j l h => (hexu' j).unique h (hpar j)
  set κ : Fin nS → (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
    fun j => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (xS j) (vS j) with hκ
  have hpar_iff : ∀ j j', par j' = par j ↔ κ j' = κ j := by
    intro j j'
    obtain ⟨r, -, -, -, hiff⟩ := hrep (par j)
    have hj : κ j = κ r := (hiff j (Finset.mem_univ _)).1 (hpar j)
    constructor
    · intro h
      have hj' : κ j' = κ r := (hiff j' (Finset.mem_univ _)).1 (by rw [← h]; exact hpar j')
      rw [hj, hj']
    · intro h
      exact (huniq j' (par j) ((hiff j' (Finset.mem_univ _)).2 (h.trans hj))).symm
  -- the round-box bound in every parent
  have hΛ1 : 1 ≤ Λ := by
    have : 1 ≤ δ ^ (-ν - ζ₂ / 200) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1.le (by linarith)
    linarith
  set K : ℝ := 400 * 122 ^ 3 * 16 ^ 3 * (L : ℝ) ^ 2 * Λ *
    (2 * levelDens a ρf (top - j₂) * δ ^ 2) with hK
  have hK0 : 0 ≤ K := by
    have := levelDens_pos a hρpos (top - j₂)
    simp only [hK]
    have : 0 ≤ Λ := by linarith
    positivity
  have hround : ∀ l (a' b : ℝ) (e' : Space ≃ᵃⁱ[ℝ] Space), δ ≤ a' → a' ≤ b → b ≤ Λ * a' →
      b ≤ 2 → (((Finset.univ.filter (fun j => par j = l)).filter
        (fun j => Tube δ (xS j) (vS j) ⊆ e' '' factorBox a' b)).card : ℝ) * δ ^ 2 ≤
          K * a' * b := by
    intro l a' b e' h1 h2 h3 h4
    by_cases hne : (Finset.univ.filter (fun j => par j = l)).Nonempty
    · obtain ⟨j₀, hj₀⟩ := hne
      have hpl : par j₀ = l := (Finset.mem_filter.mp hj₀).2
      set F : Finset (Fin m) := S.filter (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (x i) (v i) = κ j₀)
        with hF
      have hFS : F ⊆ S := Finset.filter_subset _ _
      have hFcard : F.card < 2 ^ (a (top - i₀) + 1) :=
        (hpop (top - i₀) (Nat.sub_le _ _) (e j₀) (heS j₀)).2
      have hrb := roundBox_of_profile x v S F hFS hδ hδ1 hL1 hΛ1 a hρpos
        (by simp only [hρf]; nlinarith) (fun k => by simp only [hρf]; rw [pow_succ]; nlinarith)
        (Nat.le_of_lt (hij.trans_le hj₂)) (by linarith) hv hT hanti
        (fun k hk i hi => (hpop k (le_trans hk (Nat.sub_le _ _)) i hi).2) hFcard hprof
        a' b e' h1 h2 h3 h4
      have hc : ((Finset.univ.filter (fun j => par j = l)).filter
          (fun j => Tube δ (xS j) (vS j) ⊆ e' '' factorBox a' b)).card =
          (F.filter (fun i => Tube δ (x i) (v i) ⊆
            e' '' {z : Space | |z 0| ≤ a' ∧ |z 1| ≤ b ∧ |z 2| ≤ 2})).card := by
        rw [Finset.filter_filter, hF, Finset.filter_filter, ← hcount]
        apply congrArg Finset.card
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hpl, hpar_iff]
        rfl
      rw [hc]
      exact hrb
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.filter_empty, Finset.card_empty,
        Nat.cast_zero, zero_mul]
      have ha' : 0 ≤ a' := by linarith
      have hb' : 0 ≤ b := by linarith
      positivity
  -- split the parents: KT-good or flat
  set Kd : ℝ := K * δ ^ (-ν) with hKd
  have hKd0 : 0 ≤ Kd := mul_nonneg hK0 (Real.rpow_nonneg hδ.le _)
  set flat : Finset (Fin nS) → Prop := fun F => ¬ KTGood δ ν Kd xS vS F with hflatdef
  set sub : Finset (Fin nS) → Finset (Fin nS) :=
    fun F => if h : KTGood δ ν Kd xS vS F then Classical.choose h else F with hsubdef
  have hsub : ∀ F, ¬ flat F → sub F ⊆ F ∧ (F.card : ℝ) ≤ δ ^ (-ν) * (sub F).card := by
    intro F hF
    have hg : KTGood δ ν Kd xS vS F := not_not.mp hF
    simp only [hsubdef, dif_pos hg]
    obtain ⟨h1, h2, -⟩ := Classical.choose_spec hg
    exact ⟨h1, h2⟩
  have hLν : 1 ≤ δ ^ (-ν) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1.le (by linarith)
  rcases WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.cell_refine Finset.univ par (δ ^ (-ν)) hLν flat sub hsub with hflat |
    ⟨S', -, hS'size, hS'cell⟩
  · -- flat side
    have hmaj : nS ≤ 2 * (Finset.univ.filter (fun j => ¬ KTGood δ ν (K * δ ^ (-ν)) xS vS
        (Finset.univ.filter (fun j' => par j' = par j)))).card := by
      have h := hflat
      rw [Finset.card_univ, Fintype.card_fin] at h
      convert h using 3
      ext j
      simp only [Finset.mem_filter]
      rfl
    have hFS : ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal (ncard {j | Tube δ (xS j) (vS j) ⊆ W} : ℝ) ≤
          ENNReal.ofReal (KF * nS) * volume W := by
      intro W hW
      have h := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.ncard_enum S (fun i => Tube δ (x i) (v i) ⊆ W)
      have h' : ncard {j | Tube δ (xS j) (vS j) ⊆ W} =
          (S.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card := h
      rw [h']
      exact hFG W hW
    obtain ⟨k, g', hg', hk, hC⟩ := flat_side hδ hδ1.le hν hζ hζ₂ hρ0 (by linarith) hΛ h64 hdich
      hnS0 hpig herror hretain xS vS hvS' hTS hsepS hKF0 hKFζ hFS z w hw hRsep par hpar huniq
      hround hmaj
    refine ⟨k, fun j => e (g' j), he_inj.comp hg', fun j => heS _, ?_, Or.inr hC⟩
    have hθ0 : 0 ≤ δ ^ θ := Real.rpow_nonneg hδ.le _
    have hn0 : (0 : ℝ) ≤ nS := Nat.cast_nonneg _
    have : 2 * (δ ^ ω * nS) ≤ δ ^ θ * nS := by
      have := mul_le_mul_of_nonneg_right hfin2 hn0
      linarith
    linarith
  · -- KT side
    have hKT' : ∀ j₀ ∈ S', ∀ W : Set WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Sp, Convex ℝ W →
        ENNReal.ofReal ((S'.filter (fun j => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (xS j) (vS j) =
            WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (xS j₀) (vS j₀) ∧
            Metric.thickening δ (segment ℝ (xS j) (xS j + vS j)) ⊆ W)).card * δ ^ 2) ≤
          ENNReal.ofReal Kd * volume W := by
      intro j₀ hj₀ W hW
      obtain ⟨hnf, hfib⟩ := hS'cell j₀ hj₀
      have hg : KTGood δ ν Kd xS vS (WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.fibre Finset.univ par j₀) := not_not.mp hnf
      have hsubeq : sub (WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.fibre Finset.univ par j₀) = Classical.choose hg := by
        simp only [hsubdef, dif_pos hg]
      obtain ⟨-, -, hKTc⟩ := Classical.choose_spec hg
      have heq : S'.filter (fun j => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (xS j) (vS j) =
            WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (xS j₀) (vS j₀) ∧
            Metric.thickening δ (segment ℝ (xS j) (xS j + vS j)) ⊆ W) =
          (Classical.choose hg).filter (fun j => Tube δ (xS j) (vS j) ⊆ W) := by
        rw [← hsubeq, ← hfib]
        ext j
        simp only [Finset.mem_filter, WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.fibre]
        constructor
        · rintro ⟨hj, hκj, hWj⟩
          exact ⟨⟨hj, (hpar_iff j₀ j).2 hκj⟩, hWj⟩
        · rintro ⟨⟨hj, hp⟩, hWj⟩
          exact ⟨hj, (hpar_iff j₀ j).1 hp, hWj⟩
      rw [heq]
      exact hKTc W hW
    have hS'size' : (nS : ℝ) ≤ 2 * δ ^ (-ν) * S'.card := by
      have h := hS'size
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact h
    have hτne : τ ≠ 0 := hτ0.ne'
    have hcτ' : Kd * τ ^ 2 ≤ δ ^ (-ζ₂) * (δ ^ (2 * ν) * 2 ^ a (top - j₂) / 4) * δ ^ 2 := by
      have hKdEq : Kd * τ ^ 2 = (8 * (400 * 122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * Λ * δ ^ (-ν)) *
          (2 ^ a (top - j₂) * δ ^ 2 / 4) := by
        simp only [hKd, hK, levelDens, ← hτ]
        field_simp
        ring
      rw [hKdEq]
      calc (8 * (400 * 122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * Λ * δ ^ (-ν)) *
            (2 ^ a (top - j₂) * δ ^ 2 / 4)
          ≤ (δ ^ (-ζ₂) * δ ^ (2 * ν)) * (2 ^ a (top - j₂) * δ ^ 2 / 4) :=
            mul_le_mul_of_nonneg_right hcτ (by positivity)
        _ = δ ^ (-ζ₂) * (δ ^ (2 * ν) * 2 ^ a (top - j₂) / 4) * δ ^ 2 := by ring
    have hfp := fullness_of_profile hδ hδ1 a hρpos hgap hc'
    have hfull' : δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ (a (top - j₂) + 4) ≤
        δ ^ (3 * ν) * 2 ^ a (top - i₀) := by
      have hr : 0 ≤ (ρ / τ) ^ 2 * 2 ^ (a (top - j₂) + 1) := by positivity
      calc δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ (a (top - j₂) + 4)
          = (8 * δ ^ ζ₂) * ((ρ / τ) ^ 2 * 2 ^ (a (top - j₂) + 1)) := by ring
        _ ≤ (δ ^ (3 * ν) * δ ^ ζ') * ((ρ / τ) ^ 2 * 2 ^ (a (top - j₂) + 1)) :=
            mul_le_mul_of_nonneg_right h8 hr
        _ = δ ^ (3 * ν) * (δ ^ ζ' * (ρ / τ) ^ 2 * 2 ^ (a (top - j₂) + 1)) := by ring
        _ ≤ δ ^ (3 * ν) * 2 ^ a (top - i₀) :=
            mul_le_mul_of_nonneg_left hfp (Real.rpow_nonneg hδ.le _)
    have hFGS : ∀ W : Set WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Sp, Convex ℝ W →
        ENNReal.ofReal ((Finset.univ.filter (fun j =>
          Metric.thickening δ (segment ℝ (xS j) (xS j + vS j)) ⊆ W)).card : ℝ) ≤
          ENNReal.ofReal (KF * nS) * volume W := by
      intro W hW
      have h' : (Finset.univ.filter (fun j =>
          Metric.thickening δ (segment ℝ (xS j) (xS j + vS j)) ⊆ W)).card =
          (S.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card :=
        hcount (fun i => Tube δ (x i) (v i) ⊆ W)
      rw [h']
      exact hFG W hW
    obtain ⟨S₃, -, hS₃size, hSB⟩ := kt_side hδ hν hδτ hmm2 hρm hρtop hscale hnS0 xS vS hvS'
      hTS hcanS hantiS (fun j j' => hclsS (top - j₂) (Nat.sub_le _ _) j j')
      (fun j j' => hclsS (top - i₀) (Nat.sub_le _ _) j j') (a (top - j₂)) (a (top - i₀))
      (fun j => by
        rw [hpopS (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (τ / 20) (x i) (v i)) j]
        exact hpop (top - j₂) (Nat.sub_le _ _) (e j) (heS j))
      (fun j => by
        rw [hpopS (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (x i) (v i)) j]
        exact hpop (top - i₀) (Nat.sub_le _ _) (e j) (heS j))
      S' hS'size' hKd0 hKT' hcτ' hfull' hKF0 hFGS hsmall hKF2 hζ₂4
    refine ⟨S₃.card, fun j => e (S₃.equivFin.symm j).1, ?_, fun j => heS _, ?_, Or.inl hSB⟩
    · intro j j' h
      exact S₃.equivFin.symm.injective (Subtype.ext (he_inj h))
    · have hω0 : 0 ≤ δ ^ ω := Real.rpow_nonneg hδ.le _
      calc δ ^ ω * nS
          ≤ δ ^ ω * (16 * ((Nat.log 2 nS : ℝ) + 1) ^ 2 * δ ^ (-ν) * S₃.card) :=
            mul_le_mul_of_nonneg_left hS₃size hω0
        _ = (δ ^ ω * (16 * ((Nat.log 2 nS : ℝ) + 1) ^ 2 * δ ^ (-ν))) * S₃.card := by ring
        _ ≤ 1 * S₃.card := mul_le_mul_of_nonneg_right hfin1 (Nat.cast_nonneg _)
        _ = S₃.card := one_mul _

/-- `c δ^p ≤ 1` for all small `δ`. -/
lemma exists_mul_rpow_le_one (c p : ℝ) (hp : 0 < p) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → c * δ ^ p ≤ 1 := by
  rcases le_or_gt c 0 with hc | hc
  · refine ⟨1, one_pos, fun δ hδ _ => ?_⟩
    have : 0 ≤ δ ^ p := Real.rpow_nonneg hδ.le p
    nlinarith
  · refine ⟨(1 / c) ^ (1 / p), by positivity, fun δ hδ hδd => ?_⟩
    have h1 : δ ^ p ≤ ((1 / c) ^ (1 / p)) ^ p := Real.rpow_le_rpow hδ.le hδd hp.le
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp.ne', Real.rpow_one] at h1
    calc c * δ ^ p ≤ c * (1 / c) := mul_le_mul_of_nonneg_left h1 hc.le
      _ = 1 := by field_simp

/-- From `c δ^p ≤ 1` and `A - B = p` follows `c δ^A ≤ δ^B`. -/
lemma mul_rpow_le_rpow_of {δ c A B p : ℝ} (hδ : 0 < δ) (hp : A - B = p)
    (h : c * δ ^ p ≤ 1) : c * δ ^ A ≤ δ ^ B := by
  have hB : 0 < δ ^ B := Real.rpow_pos_of_pos hδ B
  have e : c * δ ^ A = (c * δ ^ p) * δ ^ B := by
    rw [mul_assoc, ← Real.rpow_add hδ, ← hp, sub_add_cancel]
  rw [e]
  calc (c * δ ^ p) * δ ^ B ≤ 1 * δ ^ B := mul_le_mul_of_nonneg_right h hB.le
    _ = δ ^ B := one_mul _

/-- The polylogarithmic bound of `flat_exit_pig_eventually` bounds `log₂ n + 1`. -/
lemma log_add_one_le_of_pig {δ ν : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) {n : ℕ}
    (h : (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
      (Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν)) :
    (Nat.log 2 n : ℝ) + 1 ≤ δ ^ (-ν) := by
  have h1 : (n : ℝ) ≤ (n : ℝ) * δ ^ (-ν) := by
    have : 1 ≤ δ ^ (-ν) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h2 : n ≤ ⌊(n : ℝ) * δ ^ (-ν)⌋₊ := Nat.le_floor h1
  have h3 : Nat.log 2 n ≤ Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ := Nat.log_mono_right h2
  have h4 : Nat.log 2 n + 1 ≤ (Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
      (Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ + 1) := by
    calc Nat.log 2 n + 1 ≤ Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ + 1 := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by positivity)
  calc (Nat.log 2 n : ℝ) + 1 = ((Nat.log 2 n + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast h4
    _ ≤ δ ^ (-ν) := h

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The non-sticky branch.** For `0 < ζ₃ ≤ ζ₂ ≤ ζ₁` and a share exponent `ω > 0` there are
`ζF > 0` and `δ₁ > 0` such that, for `δ ≤ δ₁`, every prepared set `S` (global Frostman with
constant `δ^(-ζF)`, levels `ρ_k = 2δL^k` up to `top`, `δ^(-ζ₂/256) ≤ L ≤ δ^(-ζ₂/16)`) with a
profile pair `i₀ < j₂` (`G j₂` minimal on `[i₀, top]`, `G i₀ - ζ₂/2 ≤ G j₂`,
`δ^(-ζ₁) ≤ L^(j₂ - i₀)`) has a `δ^ω` share with frozen `SB` or frozen `C`. -/
theorem nonsticky_branch {ζ₁ ζ₂ ζ₃ ω : ℝ} (hζ₃ : 0 < ζ₃) (h32 : ζ₃ ≤ ζ₂) (h21 : ζ₂ ≤ ζ₁)
    (hω : 0 < ω) (Cp : ℝ) :
    ∃ ζF : ℝ, 0 < ζF ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
    ∀ L : ℕ, δ ^ (-(ζ₂ / 256)) ≤ (L : ℝ) → (L : ℝ) ≤ δ ^ (-(ζ₂ / 16)) →
    ∀ top : ℕ, 2 * δ * (L : ℝ) ^ top ≤ 1 / 10000 →
    ∀ (m : ℕ) (x v : Fin m → Space) (S : Finset (Fin m)), (m : ℝ) * δ ^ 4 ≤ Cp →
    S.Nonempty → (∀ i ∈ S, ‖v i‖ = 1) → (∀ i ∈ S, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) →
    (∀ i ∈ S, x i = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.leftStart δ (x i) (v i)) → (∀ i ∈ S, ∀ j ∈ S, 1 ≤ ‖v i + v j‖) →
    ∀ a : ℕ → ℕ,
    (∀ k ≤ top, ∀ i ∈ S, ∀ i' ∈ S,
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i) (v i) =
        WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i') (v i')) →
    (∀ k ≤ top, ∀ i ∈ S,
      2 ^ a k ≤ WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.pop S (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i ∧
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.pop S (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i <
        2 ^ (a k + 1)) →
    (∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal (δ ^ (-ζF) * S.card) * volume W) →
    ∀ i₀ j₂ : ℕ, i₀ < j₂ → j₂ ≤ top →
    (∀ l, i₀ ≤ l → l ≤ top →
      cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j₂ ≤
        cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top l) →
    cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top i₀ - ζ₂ / 2 ≤
        cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j₂ →
    δ ^ (-ζ₁) ≤ (L : ℝ) ^ (j₂ - i₀) →
    ∃ (k : ℕ) (g : Fin k → Fin m), Function.Injective g ∧ (∀ j, g j ∈ S) ∧
      δ ^ ω * S.card ≤ k ∧
      (WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.SBpred ζ₁ ζ₂ δ k
          (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))) ∨
        FlatPrisms ζ₂ ζ₃ δ (fun j => Tube δ (x (g j)) (v (g j)))) := by
  set μ := min ζ₃ ω with hμ
  have hμ0 : 0 < μ := lt_min hζ₃ hω
  have hμ3 : μ ≤ ζ₃ := min_le_left _ _
  have hμω : μ ≤ ω := min_le_right _ _
  set ν := μ / 100 with hνdef
  have hν0 : 0 < ν := by positivity
  have hνζ₂ : ν ≤ ζ₂ / 100 := by rw [hνdef]; linarith
  have hνω : ν ≤ ω / 100 := by rw [hνdef]; linarith
  set C := max Cp 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hζ₂0 : 0 < ζ₂ := lt_of_lt_of_le hζ₃ h32
  obtain ⟨dD, hdD, hdich⟩ := fibreDich_of_le ν hν0
  obtain ⟨dP, hdP, -, hpigP⟩ := flat_exit_pig_eventually ν C hν0 hC1
  obtain ⟨dQ, hdQ, -, hpigQ⟩ := flat_exit_pig_eventually (ν / 4) C (by positivity) hC1
  obtain ⟨d1, hd1, E1⟩ := exists_mul_rpow_le_one 64 ν hν0
  obtain ⟨d2, hd2, E2⟩ := exists_mul_rpow_le_one localFlatLoss (ζ₃ - 2 * ν - 5 * (2 * ν))
    (by rw [hνdef]; linarith)
  obtain ⟨d3, hd3, E3⟩ := exists_mul_rpow_le_one 2 (ω / 2 - 2 * ν) (by linarith)
  obtain ⟨d4, hd4, E4⟩ := exists_mul_rpow_le_one 2 ν hν0
  obtain ⟨d5, hd5, E5⟩ := exists_mul_rpow_le_one 2 (ζ₂ / 256) (by positivity)
  obtain ⟨d6, hd6, E6⟩ := exists_mul_rpow_le_one (128 * (400 * 122 ^ 3 * 16 ^ 3))
    (ζ₂ * (1 - 1 / 8 - 1 / 200) - 4 * ν) (by nlinarith)
  obtain ⟨d7, hd7, E7⟩ := exists_mul_rpow_le_one 2 (ζ₂ / 4) (by positivity)
  obtain ⟨d8, hd8, E8⟩ := exists_mul_rpow_le_one 8 (ζ₂ / 4 - 3 * ν) (by linarith)
  obtain ⟨d9, hd9, E9⟩ := exists_mul_rpow_le_one 16 (3 * ν / 4) (by positivity)
  obtain ⟨d10, hd10, E10⟩ := exists_mul_rpow_le_one 32 (ζ₂ - ν - 3 * ν / 2) (by linarith)
  obtain ⟨d11, hd11, E11⟩ := exists_mul_rpow_le_one 4 ζ₂ hζ₂0
  obtain ⟨d12, hd12, E12⟩ := exists_mul_rpow_le_one 16 (ω - 3 * ν / 2) (by linarith)
  obtain ⟨d13, hd13, E13⟩ := exists_mul_rpow_le_one 2 (ω / 2) (by positivity)
  set δ₁ := min (1 / 100) (min dD (min dP (min dQ (min d1 (min d2 (min d3 (min d4 (min d5
    (min d6 (min d7 (min d8 (min d9 (min d10 (min d11 (min d12 d13))))))))))))))) with hδ₁
  have hδ₁0 : 0 < δ₁ := by
    simp only [hδ₁, lt_min_iff]
    exact ⟨by norm_num, hdD, hdP, hdQ, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11,
      hd12, hd13⟩
  refine ⟨ν, hν0, δ₁, hδ₁0, ?_⟩
  intro δ hδ hδδ₁ L hLlow hLup top htop m x v S hm hS hv hT hsep hcan hanti a hcls hpop hFG
    i₀ j₂ hij hj₂ hprof hgap hsc
  simp only [hδ₁, le_min_iff] at hδδ₁
  obtain ⟨h100, hδD, hδP, hδQ, hδ1', hδ2, hδ3, hδ4, hδ5, hδ6, hδ7, hδ8, hδ9, hδ10, hδ11, hδ12,
    hδ13⟩ := hδδ₁
  have hδ1 : δ < 1 := by linarith
  -- the size bound `|S| ≤ C δ^(-4)`
  have hδ4pos : 0 < δ ^ 4 := by positivity
  have hm4 : (m : ℝ) ≤ C * δ ^ (-4 : ℝ) := by
    have e : δ ^ (-4 : ℝ) = 1 / δ ^ 4 := by
      rw [Real.rpow_neg hδ.le, one_div]
      congr 1
      exact_mod_cast Real.rpow_natCast δ 4
    rw [e, mul_one_div, le_div_iff₀ hδ4pos]
    linarith [le_max_left Cp 1]
  have hSm : (S.card : ℝ) ≤ m := by
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hpig : ∀ n' : ℕ, n' ≤ S.card → (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
      (Nat.log 2 ⌊(n' : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν) := by
    intro n' hn'
    apply hpigP δ hδ hδP n'
    have : (n' : ℝ) ≤ S.card := by exact_mod_cast hn'
    linarith
  -- the logarithm of `|S|`
  set Lg : ℝ := (Nat.log 2 S.card : ℝ) + 1 with hLg
  have hLg : Lg ≤ δ ^ (-(ν / 4)) :=
    log_add_one_le_of_pig hδ hδ1.le (by positivity) (hpigQ δ hδ hδQ S.card (by linarith))
  have hLg0 : 0 ≤ Lg := by positivity
  have hLg2 : Lg ^ 2 ≤ δ ^ (-(ν / 4) + -(ν / 4)) := by
    rw [Real.rpow_add hδ, ← sq]
    exact pow_le_pow_left₀ hLg0 hLg 2
  -- `L ≥ 2`
  have hL2 : 2 ≤ L := by
    have h2 : (2 : ℝ) ≤ δ ^ (-(ζ₂ / 256)) := by
      have := mul_rpow_le_rpow_of (c := 2) (A := 0) (B := -(ζ₂ / 256)) hδ (by ring) (E5 δ hδ hδ5)
      simpa using this
    exact_mod_cast h2.trans hLlow
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  -- the numeric hypotheses of `nonsticky_fixed`
  have hcτ : 8 * (400 * 122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * (16 * δ ^ (-ν - ζ₂ / 200)) *
      δ ^ (-ν) ≤ δ ^ (-ζ₂) * δ ^ (2 * ν) := by
    have hL2' : (L : ℝ) ^ 2 ≤ δ ^ (-(ζ₂ / 16) + -(ζ₂ / 16)) := by
      rw [Real.rpow_add hδ, ← sq]
      exact pow_le_pow_left₀ hL0 hLup 2
    rw [← Real.rpow_add hδ]
    calc 8 * (400 * 122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * (16 * δ ^ (-ν - ζ₂ / 200)) * δ ^ (-ν)
        ≤ 8 * (400 * 122 ^ 3 * 16 ^ 3) * δ ^ (-(ζ₂ / 16) + -(ζ₂ / 16)) *
            (16 * δ ^ (-ν - ζ₂ / 200)) * δ ^ (-ν) := by gcongr
      _ = (128 * (400 * 122 ^ 3 * 16 ^ 3)) *
            δ ^ ((-(ζ₂ / 16) + -(ζ₂ / 16)) + (-ν - ζ₂ / 200) + -ν) := by
          rw [Real.rpow_add hδ (-(ζ₂ / 16) + -(ζ₂ / 16) + (-ν - ζ₂ / 200)) (-ν),
            Real.rpow_add hδ (-(ζ₂ / 16) + -(ζ₂ / 16)) (-ν - ζ₂ / 200)]
          ring
      _ ≤ δ ^ (-ζ₂ + 2 * ν) := mul_rpow_le_rpow_of hδ (by ring) (E6 δ hδ hδ6)
  have hc' : 2 * δ ^ (3 * ζ₂ / 4) ≤ δ ^ (ζ₂ / 2) :=
    mul_rpow_le_rpow_of hδ (by ring) (E7 δ hδ hδ7)
  have h8 : 8 * δ ^ ζ₂ ≤ δ ^ (3 * ν) * δ ^ (3 * ζ₂ / 4) := by
    rw [← Real.rpow_add hδ]
    exact mul_rpow_le_rpow_of hδ (by ring) (E8 δ hδ hδ8)
  have hζ₂4 : 4 ≤ δ ^ (-ζ₂) := by
    have := mul_rpow_le_rpow_of (c := 4) (A := 0) (B := -ζ₂) hδ (by ring) (E11 δ hδ hδ11)
    simpa using this
  have hfin2 : 2 * δ ^ ω ≤ δ ^ (ω / 2) := mul_rpow_le_rpow_of hδ (by ring) (E13 δ hδ hδ13)
  have hKFζ : 2 * δ ^ (-ν) ≤ δ ^ (-(2 * ν)) := mul_rpow_le_rpow_of hδ (by ring) (E4 δ hδ hδ4)
  have hsmall : 16 * Lg * δ ^ ν ≤ 1 := by
    calc 16 * Lg * δ ^ ν ≤ 16 * δ ^ (-(ν / 4)) * δ ^ ν := by gcongr
      _ = 16 * δ ^ (3 * ν / 4) := by
          rw [mul_assoc, ← Real.rpow_add hδ, show -(ν / 4) + ν = 3 * ν / 4 by ring]
      _ ≤ 1 := E9 δ hδ hδ9
  have hKF2 : 2 * (δ ^ (-ν) * (16 * Lg ^ 2 * δ ^ (-ν))) ≤ δ ^ (-ζ₂) := by
    calc 2 * (δ ^ (-ν) * (16 * Lg ^ 2 * δ ^ (-ν)))
        ≤ 2 * (δ ^ (-ν) * (16 * δ ^ (-(ν / 4) + -(ν / 4)) * δ ^ (-ν))) := by gcongr
      _ = 32 * δ ^ (-ν + (-(ν / 4) + -(ν / 4)) + -ν) := by
          rw [Real.rpow_add hδ (-ν + (-(ν / 4) + -(ν / 4))) (-ν),
            Real.rpow_add hδ (-ν) (-(ν / 4) + -(ν / 4))]
          ring
      _ ≤ δ ^ (-ζ₂) := mul_rpow_le_rpow_of hδ (by ring) (E10 δ hδ hδ10)
  have hfin1 : δ ^ ω * (16 * Lg ^ 2 * δ ^ (-ν)) ≤ 1 := by
    calc δ ^ ω * (16 * Lg ^ 2 * δ ^ (-ν))
        ≤ δ ^ ω * (16 * δ ^ (-(ν / 4) + -(ν / 4)) * δ ^ (-ν)) := by gcongr
      _ = 16 * δ ^ (ω + (-(ν / 4) + -(ν / 4)) + -ν) := by
          rw [Real.rpow_add hδ (ω + (-(ν / 4) + -(ν / 4))) (-ν),
            Real.rpow_add hδ ω (-(ν / 4) + -(ν / 4))]
          ring
      _ ≤ δ ^ (0 : ℝ) := mul_rpow_le_rpow_of hδ (by ring) (E12 δ hδ hδ12)
      _ = 1 := Real.rpow_zero δ
  have herror : localFlatLoss * δ ^ (ζ₃ - 2 * ν - 5 * (2 * ν)) ≤ 1 := E2 δ hδ hδ2
  have hretain : 2 * δ ^ (ω / 2 - 2 * ν) ≤ 1 := E3 δ hδ hδ3
  exact nonsticky_fixed (ζ := 2 * ν) (θ := ω / 2) (ζ' := 3 * ζ₂ / 4) hδ hδ1 hν0.le
    (by positivity) hζ₂0.le hL2 htop (hdich δ hδ h100 hδD) le_rfl (E1 δ hδ hδ1') herror hretain
    hcτ hc' h8 hζ₂4 hfin2 x v S hS hpig hsmall (Real.rpow_nonneg hδ.le _) hKFζ hKF2 hfin1
    hv hT hsep hcan hanti a hcls hpop hFG hij hj₂ hprof hgap hsc

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
