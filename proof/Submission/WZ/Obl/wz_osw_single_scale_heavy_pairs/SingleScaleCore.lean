-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.SingleScaleCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.HeavyConfig
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.StripCode

/-!
# The single-scale heavy-pair estimate from Furstenberg and rich strips

If the heavy pairs at scale `r` are more than `r ^ θ * #G * #G'`, the points
`b ∈ G` carrying many of them, with maximal separated sets of heavy normals as
bushes, satisfy the hypotheses of the Furstenberg bush estimate; the separated
heavy strips it produces are rich in `G'`, and too many for the rich-strip count.
-/

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

open scoped Classical

/-- The Furstenberg bush estimate at one scale (internal form). -/
def FurstenbergAt (r σ ε₀ η : ℝ) : Prop :=
  ∀ (P : Set E2) (D : Set (E2 × E2)), P.Finite → P.Nonempty → (∀ p ∈ P, ‖p‖ ≤ 4) →
    (∀ (x : E2) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) →
    D.Finite → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) →
    (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) →
    (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e' ∧ r ≤ dist e (-e')) →
    (∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) →
    ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → StripSep r q q') ∧
      r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ)

/-- The rich-strip count at one scale and Frostman constant (internal form). -/
def RichStripAt (r C AB : ℝ) : Prop :=
  ∀ l : ℝ, 0 < l → ∀ (Y : Set E2) (J : Set (E2 × E2)), Y.Finite → Y.Nonempty →
    (∀ y ∈ Y, ‖y‖ ≤ 4) →
    (∀ (x : E2) (ρ : ℝ), r ≤ ρ → ((Y ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * Y.ncard) →
    J.Finite →
    (∀ q ∈ J, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 ∧ l * Y.ncard ≤ ({y ∈ Y | |inner ℝ (y - q.1) q.2| < r}.ncard : ℝ)) →
    (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → StripSep r q q') →
    l ^ 2 * J.ncard ≤ AB * C * (1 + Real.log (1 / r))

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

open scoped Classical

lemma rpow_two_mul_rpow {r a b : ℝ} (hr : 0 < r) : (r ^ a) ^ 2 * r ^ b = r ^ (2 * a + b) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
  congr 1; push_cast; ring

/-- The core of the single-scale estimate. -/
theorem heavy_count_le_core {δ r σ τ θ K C ε₀ η AB : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hr6 : r ≤ 1 / 6) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hK : 1 ≤ K) (hC : 1 ≤ C)
    (hFrostC : 2 * C * r ^ (-θ) ≤ r ^ (-η))
    (hbushC : r ^ (η - σ) ≤ r ^ (θ - σ) / (258 * K))
    (hKTC : 9 * K * r ^ (-τ) ≤ r ^ (-η))
    (hfinal : AB * C * (1 + Real.log (1 / r)) < r ^ (2 * τ - ε₀))
    (hFurst : FurstenbergAt r σ ε₀ η) (hRich : RichStripAt r C AB)
    {G G' : Set E2} (hG : Frost δ C G) (hG' : Frost δ C G')
    (hsep : ∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b')
    {E : Set (E2 × E2)} (hE : E ⊆ G ×ˢ G')
    (hthin : ∀ b ∈ G, ∀ e : E2, ‖e‖ = 1 → ∀ ρ : ℝ, δ ≤ ρ →
      ({b' | (b, b') ∈ E ∧ |inner ℝ (b' - b) e| < ρ}.ncard : ℝ) ≤ K * ρ ^ σ * G'.ncard) :
    ((p2Heavy E r σ τ G').ncard : ℝ) ≤ r ^ θ * G.ncard * G'.ncard := by
  by_contra hcon
  have hlt := not_le.mp hcon
  have hr : 0 < r := lt_of_lt_of_le hδ hδr
  set H := p2Heavy E r σ τ G' with hHdef
  have hHE : H ⊆ E := fun q hq => hq.1
  have hEfin : E.Finite := (hG.1.prod hG'.1).subset hE
  have hHfin : H.Finite := hEfin.subset hHE
  -- G' is nonempty
  have hG'pos : (0 : ℝ) < G'.ncard := by
    rcases Nat.eq_zero_or_pos G'.ncard with h0 | h0
    · exfalso
      have hG'e : G' = ∅ := (Set.ncard_eq_zero hG'.1).mp h0
      have hHe : H = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro q hq
        have := (hE (hHE hq)).2
        rw [hG'e] at this; exact this
      rw [hHe, Set.ncard_empty, h0] at hlt
      simp at hlt
    · exact_mod_cast h0
  set lam := r ^ (σ + τ) * (G'.ncard : ℝ) with hlamdef
  -- the bad points
  set Bset : Set E2 := {b | b ∈ G ∧ r ^ θ / 2 * G'.ncard ≤ ({b' | (b, b') ∈ H}.ncard : ℝ)}
    with hBdef
  have hBG : Bset ⊆ G := fun b hb => hb.1
  have hBfin : Bset.Finite := hG.1.subset hBG
  have hfib := ncard_eq_sum_fibers hG.1 hHfin (fun q hq => (hE (hHE hq)).1)
  have hrow : ∀ b ∈ hG.1.toFinset, ({b' | (b, b') ∈ H}.ncard : ℝ) ≤
      (if b ∈ Bset then (G'.ncard : ℝ) else 0) + r ^ θ / 2 * G'.ncard := by
    intro b hb
    have hbG : b ∈ G := by simpa using hb
    have hrθ : 0 ≤ r ^ θ / 2 * (G'.ncard : ℝ) := by positivity
    by_cases hbB : b ∈ Bset
    · simp only [hbB, ite_true]
      have hsub : {b' | (b, b') ∈ H} ⊆ G' := fun b' hb' =>
        (hE (hHE (show (b, b') ∈ H from hb'))).2
      have : ({b' | (b, b') ∈ H}.ncard : ℝ) ≤ G'.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub hG'.1
      linarith
    · simp only [hbB, ite_false]
      have : ¬ (r ^ θ / 2 * G'.ncard ≤ ({b' | (b, b') ∈ H}.ncard : ℝ)) := fun h => hbB ⟨hbG, h⟩
      linarith [not_le.mp this]
  have hsumB : ∑ b ∈ hG.1.toFinset, (if b ∈ Bset then (G'.ncard : ℝ) else 0) =
      (Bset.ncard : ℝ) * G'.ncard := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcoe : ((hG.1.toFinset.filter (· ∈ Bset) : Finset E2) : Set E2) = Bset := by
      ext b; simp only [Finset.coe_filter, Set.Finite.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hBG h, h⟩⟩
    have := Set.ncard_coe_finset (hG.1.toFinset.filter (· ∈ Bset))
    rw [hcoe] at this
    exact_mod_cast this.symm
  have hHle : (H.ncard : ℝ) ≤ (Bset.ncard : ℝ) * G'.ncard + G.ncard * (r ^ θ / 2 * G'.ncard) := by
    rw [hfib]
    calc ∑ b ∈ hG.1.toFinset, ({b' | (b, b') ∈ H}.ncard : ℝ)
        ≤ ∑ b ∈ hG.1.toFinset, ((if b ∈ Bset then (G'.ncard : ℝ) else 0) + r ^ θ / 2 * G'.ncard) :=
          Finset.sum_le_sum hrow
      _ = (Bset.ncard : ℝ) * G'.ncard + G.ncard * (r ^ θ / 2 * G'.ncard) := by
          rw [Finset.sum_add_distrib, hsumB, Finset.sum_const, nsmul_eq_mul,
            ← Set.ncard_eq_toFinset_card G hG.1]
  have hBbig : r ^ θ / 2 * G.ncard < Bset.ncard := by
    have h1 : r ^ θ / 2 * G.ncard * G'.ncard < (Bset.ncard : ℝ) * G'.ncard := by nlinarith
    exact lt_of_mul_lt_mul_right h1 hG'pos.le
  have hBpos : (0 : ℝ) < Bset.ncard := lt_of_le_of_lt (by positivity) hBbig
  have hBne : Bset.Nonempty := Set.nonempty_of_ncard_ne_zero (by exact_mod_cast hBpos.ne')
  -- bushes: maximal separated sets of heavy normals
  have hbush_ex : ∀ b : E2, ∃ Db : Finset E2, (Db : Set E2) ⊆ heavyNormals E b r lam ∧
      (Db : Set E2).Pairwise (NormSep (16 * r)) ∧
      ∀ e ∈ heavyNormals E b r lam, ∃ e' ∈ Db, dist e e' < 16 * r ∨ dist e (-e') < 16 * r :=
    fun b => exists_maximal_normSep _ (fun e he => he.1) (by positivity)
  choose Dm hDmH hDmsep hDmcov using hbush_ex
  set D : Set (E2 × E2) := {q | q.1 ∈ Bset ∧ q.2 ∈ Dm q.1} with hDdef
  have hDfin : D.Finite := by
    have hsub : D ⊆ ⋃ b ∈ hBfin.toFinset, (fun e => (b, e)) '' (Dm b : Set E2) := by
      intro q hq
      simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨q.1, by simpa using hq.1, q.2, hq.2, rfl⟩
    exact (Set.Finite.biUnion (Finset.finite_toSet _)
      (fun b _ => (Finset.finite_toSet _).image _)).subset hsub
  have hfiber : ∀ p ∈ Bset, {e | (p, e) ∈ D} = (Dm p : Set E2) := by
    intro p hp; ext e; simp [hDdef, hp]
  -- bush size
  have hbushsize : ∀ p ∈ Bset, r ^ (θ - σ) / (258 * K) ≤ ((Dm p).card : ℝ) := by
    intro p hp
    have h1 := heavy_fiber_card_le (τ := τ) hδr hr hG hG' hE hthin hp.1 (Dm p)
      (fun e he => (hDmH p he).1) (hDmcov p)
    have h2 := hp.2
    have h3 : r ^ θ / 2 ≤ (Dm p).card * (K * (129 * r) ^ σ) := by
      have h4 : r ^ θ / 2 * G'.ncard ≤ ((Dm p).card * (K * (129 * r) ^ σ)) * G'.ncard := by
        have := h2.trans h1
        linarith
      exact le_of_mul_le_mul_right h4 hG'pos
    have h129 : (129 * r) ^ σ ≤ 129 * r ^ σ := by
      rw [Real.mul_rpow (by norm_num) hr.le]
      have : (129 : ℝ) ^ σ ≤ 129 := by
        calc (129 : ℝ) ^ σ ≤ 129 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
          _ = 129 := Real.rpow_one _
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hr.le _)
    have hrσ : 0 < r ^ σ := Real.rpow_pos_of_pos hr σ
    have h5 : r ^ θ / 2 ≤ (Dm p).card * (K * (129 * r ^ σ)) := by
      have : ((Dm p).card : ℝ) * (K * (129 * r) ^ σ) ≤ (Dm p).card * (K * (129 * r ^ σ)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left h129 (by linarith)
      linarith
    rw [Real.rpow_sub hr, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- Katz-Tao
  have hKT : ∀ p ∈ Bset, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((Dm p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ := by
    intro p hp u hu ρ hρ
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr hρ
    have h1 := heavy_normals_near_card_le (τ := τ) hδr hr hr6 hρ hG hG' hsep hE hthin hp.1 (Dm p)
      (fun e he => hDmH p he) (hDmsep p) hu
    set F := (Dm p).filter (fun e => dist e u ≤ ρ)
    have h2 : (F.card : ℝ) * r ^ (σ + τ) ≤ K * (9 * ρ) ^ σ := by
      have : ((F.card : ℝ) * r ^ (σ + τ)) * G'.ncard ≤ (K * (9 * ρ) ^ σ) * G'.ncard := by
        calc ((F.card : ℝ) * r ^ (σ + τ)) * G'.ncard = (F.card : ℝ) * (r ^ (σ + τ) * G'.ncard) := by ring
          _ ≤ K * (9 * ρ) ^ σ * G'.ncard := h1
      exact le_of_mul_le_mul_right this hG'pos
    have h9 : (9 * ρ) ^ σ ≤ 9 * ρ ^ σ := by
      rw [Real.mul_rpow (by norm_num) hρ0.le]
      have : (9 : ℝ) ^ σ ≤ 9 := by
        calc (9 : ℝ) ^ σ ≤ 9 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
          _ = 9 := Real.rpow_one _
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hρ0.le _)
    have hrσ : 0 < r ^ σ := Real.rpow_pos_of_pos hr σ
    have hrτ : 0 < r ^ τ := Real.rpow_pos_of_pos hr τ
    have hadd : r ^ (σ + τ) = r ^ σ * r ^ τ := Real.rpow_add hr σ τ
    have hkey : (F.card : ℝ) ≤ 9 * K * ρ ^ σ / (r ^ σ * r ^ τ) := by
      rw [le_div_iff₀ (by positivity), ← hadd]
      have : K * (9 * ρ) ^ σ ≤ K * (9 * ρ ^ σ) := mul_le_mul_of_nonneg_left h9 (by linarith)
      linarith
    have hexpr : 9 * K * ρ ^ σ / (r ^ σ * r ^ τ) = (9 * K * r ^ (-τ)) * (ρ / r) ^ σ := by
      rw [Real.div_rpow hρ0.le hr.le, Real.rpow_neg hr.le]
      field_simp
    rw [hexpr] at hkey
    exact hkey.trans (mul_le_mul_of_nonneg_right hKTC (Real.rpow_nonneg (by positivity) _))
  -- the hypotheses of the Furstenberg estimate
  have hP4 : ∀ p ∈ Bset, ‖p‖ ≤ 4 := fun p hp => (hG.2.1 p hp.1).1
  have hPfrost : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((Bset ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * Bset.ncard := by
    intro x ρ hρ
    have h1 : ((Bset ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ ((G ∩ Metric.closedBall x ρ).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ hBG)
        (hG.1.subset Set.inter_subset_left)
    have h2 := hG.2.2 x ρ (hδr.trans hρ)
    have hrθ : 0 < r ^ θ := Real.rpow_pos_of_pos hr θ
    have h3 : (G.ncard : ℝ) ≤ 2 * r ^ (-θ) * Bset.ncard := by
      rw [Real.rpow_neg hr.le]
      rw [show 2 * (r ^ θ)⁻¹ * (Bset.ncard : ℝ) = 2 * Bset.ncard / r ^ θ by ring,
        le_div_iff₀ hrθ]
      linarith
    have hρ0 : 0 ≤ ρ := by linarith
    calc ((Bset ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * G.ncard := h1.trans h2
      _ ≤ C * ρ * (2 * r ^ (-θ) * Bset.ncard) := by
          apply mul_le_mul_of_nonneg_left h3; positivity
      _ = (2 * C * r ^ (-θ)) * ρ * Bset.ncard := by ring
      _ ≤ r ^ (-η) * ρ * Bset.ncard := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right hFrostC hρ0
  have hDmem : ∀ q ∈ D, q.1 ∈ Bset ∧ ‖q.2‖ = 1 := fun q hq => ⟨hq.1, (hDmH q.1 hq.2).1⟩
  have hbushA : ∀ p ∈ Bset, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ) := by
    intro p hp
    rw [hfiber p hp, Set.ncard_coe_finset]
    exact hbushC.trans (hbushsize p hp)
  have hsepA : ∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e' ∧ r ≤ dist e (-e') := by
    intro p e e' he he' hne
    have := hDmsep p he.2 he'.2 hne
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hKTA : ∀ p ∈ Bset, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ := by
    intro p hp u hu ρ hρ
    have : {e | (p, e) ∈ D ∧ dist e u ≤ ρ} =
        (((Dm p).filter (fun e => dist e u ≤ ρ) : Finset E2) : Set E2) := by
      ext e; simp [hDdef, hp]
    rw [this, Set.ncard_coe_finset]
    exact hKT p hp u hu ρ hρ
  obtain ⟨J, hJD, hJsep, hJcard⟩ :=
    hFurst Bset D hBfin hBne hP4 hPfrost hDfin hDmem hbushA hsepA hKTA
  -- the separated heavy strips are rich in G'
  have hJfin : J.Finite := hDfin.subset hJD
  have hG'ne : G'.Nonempty := Set.nonempty_of_ncard_ne_zero (by exact_mod_cast hG'pos.ne')
  have hl : 0 < r ^ (σ + τ) := Real.rpow_pos_of_pos hr _
  have hJrich : ∀ q ∈ J, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 ∧ r ^ (σ + τ) * G'.ncard ≤
      ({y ∈ G' | |inner ℝ (y - q.1) q.2| < r}.ncard : ℝ) := by
    intro q hq
    have hqD := hJD hq
    refine ⟨hP4 q.1 hqD.1, (hDmH q.1 hqD.2).1, ?_⟩
    have hheavy := (hDmH q.1 hqD.2).2
    have hsub : strip E q.1 q.2 r ⊆ {y ∈ G' | |inner ℝ (y - q.1) q.2| < r} :=
      fun y hy => ⟨(hE hy.1).2, hy.2⟩
    have hfin2 : ({y ∈ G' | |inner ℝ (y - q.1) q.2| < r}).Finite :=
      hG'.1.subset (fun y hy => hy.1)
    exact hheavy.trans (by exact_mod_cast Set.ncard_le_ncard hsub hfin2)
  have hY4 : ∀ y ∈ G', ‖y‖ ≤ 4 := fun y hy => (hG'.2.1 y hy).1
  have hYfrost : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((G' ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * G'.ncard :=
    fun x ρ hρ => hG'.2.2 x ρ (hδr.trans hρ)
  have hRB := hRich (r ^ (σ + τ)) hl G' J hG'.1 hG'ne hY4 hYfrost hJfin hJrich hJsep
  have hlow : r ^ (2 * τ - ε₀) ≤ (r ^ (σ + τ)) ^ 2 * J.ncard := by
    calc r ^ (2 * τ - ε₀) = (r ^ (σ + τ)) ^ 2 * r ^ (-(2 * σ) - ε₀) := by
          rw [rpow_two_mul_rpow hr]; congr 1; ring
      _ ≤ (r ^ (σ + τ)) ^ 2 * J.ncard := mul_le_mul_of_nonneg_left hJcard (by positivity)
  linarith

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
